"""Driver: certify R(t) > 0 on [T_A, T_B] by Taylor-model cells (cert_window.certify, all-Arb version),
8 worker processes.  Cell coverage is verified in exact rationals before certifying.
Usage: run_window.py TA TB d K rt tag   (env COEFF_EXTRA = sharper small-n ball file; env NGL = nodes per panel;
       env NSUB = sub-balls per cell; env COEFF_DATA = coefficient directory).  Writes out/window_<tag>.json."""
import sys, os, time, json, hashlib
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
TA, TB, D, K, RT, TAG = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), sys.argv[6]
NSUB = int(os.environ.get('NSUB', '8'))
S = None
def init():
    global S
    import cert_window as CW
    S = CW.Setup()
def work(tc):
    import cert_window as CW
    Rmin, R0, info = CW.certify(S, tc, D, K, RT, nsub=NSUB)
    return tc, Rmin.str(12), bool(Rmin > 0), R0.str(15), {k: (v.str(4) if hasattr(v, 'str') else v) for k, v in info.items()}
if __name__ == '__main__':
    t0 = time.time()
    centres = []
    tc = TA + D
    while tc - D < TB:
        centres.append(round(tc, 10)); tc += 2 * D
    cells = [(F(c) - F(D), F(c) + F(D)) for c in centres]
    assert cells[0][0] == F(TA) and cells[-1][1] >= F(TB) and all(cells[i][1] == cells[i + 1][0] for i in range(len(cells) - 1))
    here = os.path.dirname(os.path.abspath(__file__))
    hs = {f: hashlib.sha256(open(os.path.join(here, f), 'rb').read()).hexdigest()[:16] for f in ('poslib.py', 'cert_window.py', 'run_window.py')}
    COEFF_DIR = os.environ.get('COEFF_DATA', os.path.join(here, '..', 'coefficients', 'data', ''))
    for f in ['an_small_X1e4.json', 'an_cert_X1e4.json'] + ([os.path.basename(os.environ['COEFF_EXTRA'])] if os.environ.get('COEFF_EXTRA') else []):
        hs[f] = hashlib.sha256(open(COEFF_DIR + f, 'rb').read()).hexdigest()[:16]
    print('run_window (all-Arb, m-node Gauss-Legendre bound) %s: [%g, %g] d=%g K=%d rt=%g NGL=%s nsub=%d, %d cells (coverage verified in exact rationals); hashes %s' % (
        TAG, TA, TB, D, K, RT, os.environ.get('NGL', '30'), NSUB, len(centres), hs), flush=True)
    with Pool(8, initializer=init) as P:
        res = P.map(work, centres, chunksize=1)
    allok = True
    for tc, Rmin, ok, R0, info in res:
        allok &= ok
        print('cell [%.4f, %.4f]: R(tc)=%s  lower=%s  ok=%s  (cauchy %s quad %s ytail %s ktail %s)' % (tc - D, tc + D, R0, Rmin, ok, info['cauchy'], info['quad'], info['ytail'], info['ktail']), flush=True)
    json.dump(res, open(os.path.join(here, 'out', 'window_%s.json' % TAG), 'w'))
    print('DECISIVE: R(t) > 0 on [%g, %g] (all %d cells certified): %s   (%.0fs)' % (TA, centres[-1] + D, len(centres), allok, time.time() - t0), flush=True)
