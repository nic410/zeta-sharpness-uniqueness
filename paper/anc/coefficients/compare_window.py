"""Cross-check (Appendix A.2 of the paper), not used in any proof: compare the density-route H_raw(t) of cert_Ht.py (logs
coefficients/logs/cert_Ht_t*.log) with R(t_c) of the window certificate of positivity/ (Theorem 7.10 of the paper; four-path
formula; positivity/out/window_0_40.json, written by positivity/run_window.py):  R(t) = H_raw(t) * 2 pi^2 (t^2 + 1/4)^2 ;
report the overlap of the two certified balls at every cell centre t_c at which cert_Ht.py was run."""
import re, glob, os, json, hashlib
sha = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
from flint import arb, ctx
ctx.prec = 128
pi = arb.pi()
HERE = os.path.dirname(os.path.abspath(__file__))                                      # coefficients/
WIN = os.path.join(HERE, '..', 'positivity', 'out', 'window_0_40.json')
win = {}
for cell in json.load(open(WIN)):                     # [t_c, lower bound, verdict, R(t_c), error terms] per cell [t_c - 1/4, t_c + 1/4]
    m = re.match(r'\[(\S+) \+/- (\S+)\]$', cell[3])
    assert m, 'unexpected R(t_c) entry %r' % (cell[3],)
    win[round(float(cell[0]), 4)] = arb(m.group(1), float(m.group(2)))
rows = []
for fn in sorted(glob.glob(os.path.join(HERE, 'logs', 'cert_Ht_t*.log'))):
    s = open(fn).read()
    m = re.search(r'Re H_raw\(t\) = (\S+) \+- (\S+)', s); mt = re.search(r'cert_Ht.py t=(\S+) ', s)
    if not m or not mt:
        continue
    t = arb(mt.group(1)); tf = round(float(t.mid()), 4)
    H = arb(m.group(1), float(m.group(2)))
    R = H * 2 * pi ** 2 * (t ** 2 + arb(1) / 4) ** 2
    rows.append((tf, H, R))
print('compare_window.py sha %s ; window output %s sha %s (%d cells)' % (sha(os.path.abspath(__file__)), os.path.basename(WIN), sha(WIN), len(win)))
print('  t      | density route R(t)             | window certificate R(tc)    | overlap')
ncmp = 0
allok = True
for tf, H, R in sorted(rows, key=lambda r: r[0]):
    if tf in win:
        ok = R.overlaps(win[tf]); allok &= ok; ncmp += 1
        print('%7.2f | %-30s | %-27s | %s' % (tf, R.str(12), win[tf].str(10), ok))
    else:
        print('%7.2f | %-30s | (no cell centre)            |' % (tf, R.str(12)))
print('DECISIVE: %d/%d compared points overlap: %s' % (ncmp if allok else -1, ncmp, allok))
