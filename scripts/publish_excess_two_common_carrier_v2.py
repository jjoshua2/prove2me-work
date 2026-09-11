#!/usr/bin/env python3
"""Pinned entrypoint for the repaired compact excess-two carrier proof."""
import argparse
import publish_excess_two_common_carrier as p

p.SOURCE = 'd85e9ff15194bd413c5f7e71e6f1f10e2b98697c'
p.DRIVER_BLOB = 'ef4aadf8672a49d399238a1c80c306111a0afc23'

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode', choices=['prepare', 'publish'])
    args = ap.parse_args()
    p.prepare() if args.mode == 'prepare' else p.publish()
