"""Write {n: [mid, rad]} files in the format of the COEFF_EXTRA files read by positivity/ (coefficients/out/extra_smalln_<TAG>.json)
from the a_mid_rad field of coefficients/out/an_smalln_<TAG>.json (radii already outward)."""
import os, sys, json, hashlib
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out')     # coefficients/out/ (fresh outputs)
sha = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('make_extra.py sha %s' % sha(os.path.abspath(__file__)))
for tag in sys.argv[1:]:
    src = os.path.join(OUT, 'an_smalln_%s.json' % tag); dst = os.path.join(OUT, 'extra_smalln_%s.json' % tag)
    json.dump(json.load(open(src))['a_mid_rad'], open(dst, 'w'), indent=0)
    print('from %s (sha %s) wrote %s sha %s' % (os.path.basename(src), sha(src), os.path.basename(dst), sha(dst)))
