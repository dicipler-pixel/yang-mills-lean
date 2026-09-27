#!/usr/bin/env python3
"""Run every completed continuation verifier without modifying source code."""
from pathlib import Path
import subprocess
import sys

root=Path(__file__).resolve().parent
jobs=[('Exact SU(3) spectral certificates','su3/su3_character_certificate.py'),
      ('Local universal-frame controls','frame/verify_frame.py'),
      ('Exact holonomy and instanton controls','holonomy/verify_holonomy.py')]
for name,script in jobs:
    print('\n'+name,flush=True)
    subprocess.run([sys.executable,str(root/script)],cwd=root,check=True)
print('\nAll continuation verifiers passed. See the paper for the precise proof scope.')
