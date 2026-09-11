# Common-face row-excess publication retry

The first fresh publication run failed closed before authentication because the standalone compiler had not built the imported local common-face definition module. The owner-only base workflow now builds `Definitions.Def_Hirsch_common_face_geometry` before compiling the unchanged frozen standalone proof. No proof bytes or theorem statement changed.
