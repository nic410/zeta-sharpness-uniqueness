"""Make every stored [mid_string, rad_float] pair OUTWARD-ROUNDED (called by the writers of coefficients/out/*.json).
The writers stored mid = 40-significant-digit decimal rounding of the Arb midpoint (error <= 0.5e-39 |mid|) and
rad = float(Arb radius) (round-to-nearest, may be low by 1.2e-16 relative).  We replace
    rad  ->  nextafter( rad (1 + 1e-12) + |mid| 1e-38 , +inf )
so that the stored ball contains the computed ball.  (Arb strings produced by .str(n, radius=True) are already enclosures.)
Usage: fix_json_radii.py file.json [...]  (idempotent marker 'radii_outward' in meta)."""
import sys, json, math, hashlib, os
SELF_SHA = hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:16]
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))     # the top directory; file names are printed relative to it
from decimal import Decimal, getcontext
getcontext().prec = 60


def fix_pair(p):
    mid, rad = p
    r = Decimal(repr(float(rad))) * (1 + Decimal('1e-12')) + abs(Decimal(mid)) * Decimal('1e-38')
    return [mid, math.nextafter(float(r), math.inf)]


for fn in sys.argv[1:]:
    d = json.load(open(fn))
    if d.get('meta', {}).get('radii_outward'):
        print(os.path.relpath(os.path.abspath(fn), ROOT), 'already fixed'); continue
    cnt = 0
    for key, val in list(d.items()):
        if key == 'meta' or not isinstance(val, dict):
            continue
        for k, v in val.items():
            if isinstance(v, list) and len(v) == 2 and isinstance(v[0], str) and isinstance(v[1], (int, float)):
                val[k] = fix_pair(v); cnt += 1
    # top-level pairs (H0_cert.json style)
    for key, v in list(d.items()):
        if isinstance(v, list) and len(v) == 2 and isinstance(v[0], str) and isinstance(v[1], (int, float)):
            d[key] = fix_pair(v); cnt += 1
    d.setdefault('meta', {})['radii_outward'] = 'rad -> nextafter(rad(1+1e-12) + |mid| 1e-38) (fix_json_radii.py %s)' % SELF_SHA
    json.dump(d, open(fn, 'w'), indent=0)
    print(os.path.relpath(os.path.abspath(fn), ROOT), 'fixed %d pairs' % cnt)
