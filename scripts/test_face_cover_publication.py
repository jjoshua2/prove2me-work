#!/usr/bin/env python3
"""Offline guard tests. These never call Prove2Me, GitHub, or Lean."""
from __future__ import annotations
import contextlib, hashlib, io, json, tempfile, unittest
from pathlib import Path
from unittest.mock import patch
import build_face_cover_publication as builder
import publish_face_cover_certificates as publisher

class Tests(unittest.TestCase):
    def test_public_signatures(self):
        self.assertEqual(len({c['name'] for c in builder.CASES}),4)
        for c in builder.CASES:
            self.assertNotIn(c['name'],c['proof'])
            self.assertNotIn('HirschFaceSplice.',c['signature'])
            self.assertNotIn('HirschRankFaceCover.',c['signature'])
            self.assertNotIn('faceRowSpan',c['signature'])
            self.assertNotIn('sorry',c['signature'])
            self.assertIn(c['checked'],c['proof'])
    def test_admission_guard(self):
        for text in ['theorem solution : True := by sorry','axiom trust : False','theorem solution := by native_decide',
                     'import Theorems.Thm_target','import Solutions.Hidden']:
            with self.assertRaises(ValueError):builder.check_proof(text)
        builder.check_proof('/- no sorry /- nested admit -/ here -/\ntheorem x : True := True.intro')
    def test_scoped_flatten_and_import_deduplication(self):
        texts={
          'Solutions/A.lean':'import Mathlib\nnoncomputable section\nnamespace A\ntheorem test : True := True.intro\nend A\n#print axioms A.test\n',
          'Solutions/B.lean':'import Solutions.A\nnamespace B\nsection\ntheorem test : True := A.test\nend\nend B\n',
          'Solutions/C.lean':'import Solutions.A\nimport Solutions.B\n'}
        with patch.object(builder,'read_git',side_effect=lambda repo,path:texts[path]):
            body,records=builder.flatten(Path('.'),'Solutions.C')
        self.assertEqual(len(records),3)
        self.assertEqual(body.count('theorem test : True := True.intro'),1)
        self.assertNotIn('#print',body)
        self.assertNotIn('import Solutions',body)
        self.assertIn('end A\nend\nend',body)
    def test_no_unknown_import(self):
        with patch.object(builder,'read_git',return_value='import Theorems.Thm_unknown\n'):
            with self.assertRaises(ValueError):builder.flatten(Path('.'),'Solutions.A')
    def test_import_cycle_rejected(self):
        with patch.object(builder,'read_git',return_value='import Solutions.A\n'):
            with self.assertRaises(ValueError):builder.flatten(Path('.'),'Solutions.A')
    def test_packet_tamper_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);entries=[];records=[]
            for c in builder.CASES:
                proof='theorem solution : True := True.intro\n';statement='theorem declared : True := by sorry\n'
                (root/(c['key']+'.lean')).write_text(proof);(root/(c['key']+'.statement.lean')).write_text(statement)
                e={'name':c['name'],'key':c['key'],'solution_sha256':builder.sha(proof),'statement_sha256':builder.sha(statement)}
                entries.append(e);records.append({**e,'axioms':[],'standalone_compilation':'PASSED'})
            man={'source_commit':builder.SOURCE,'source_run':builder.SOURCE_RUN,'mathlib_rev':builder.PIN,'lean_toolchain':builder.LEAN,'entries':entries}
            (root/'manifest.json').write_text(json.dumps(man))
            ver={'source_commit':builder.SOURCE,'mathlib_rev':builder.PIN,'status':'PASSED','entries':records,
                 'manifest_sha256':publisher.digest(root/'manifest.json')}
            (root/'verification.json').write_text(json.dumps(ver))
            self.assertEqual(len(publisher.checked_packet(root)['entries']),4)
            (root/'weighted.lean').write_text('theorem solution : True := by sorry')
            with self.assertRaises(ValueError):publisher.checked_packet(root)
    def test_existing_proved_is_not_resubmitted(self):
        entry={'key':'one','name':'Hirsch.example','formal_statement':'theorem example : True := by sorry','solution_sha256':'verified'}
        existing={'theorem_id':'id','theorem_name':'Hirsch.example','mathlib_rev':builder.PIN,
                  'formal_statement':entry['formal_statement'],'status':'Proved'}
        class Fake:
            def request(self,path,*args):
                if path.startswith('/theorems?'):return {'theorems':[existing]}
                if path=='/theorems/id':return existing
                raise AssertionError('unexpected write or API call')
            def verify(self,*args):raise AssertionError('unnecessary resubmission')
        with tempfile.TemporaryDirectory() as t:
            result=publisher.process(Fake(),entry,Path(t),Path(t))
            self.assertEqual(result['verdict'],'ALREADY_PROVED')
    def test_type_collision_blocks_submission(self):
        entry={'key':'one','name':'Hirsch.example','formal_statement':'theorem example : True := by sorry','solution_sha256':'verified'}
        existing={'theorem_id':'id','theorem_name':'Hirsch.example','mathlib_rev':builder.PIN,
                  'formal_statement':'theorem example : False := by sorry','status':'Open'}
        class Fake:
            def request(self,path,*args):
                return {'theorems':[existing]} if path.startswith('/theorems?') else existing
            def verify(self,*args):raise AssertionError('collision must not reach verification')
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaises(ValueError):publisher.process(Fake(),entry,Path(t),Path(t))

if __name__=='__main__':unittest.main()
