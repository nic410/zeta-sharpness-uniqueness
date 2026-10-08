"""R(0) enclosure with ALL error terms (all-Arb certifier): R(0) in [lower, upper] on the cell [-1e-6, 1e-6];
=> H_raw(0) = 8 R(0)/pi^2 > 0 (sign coherence, C = pi^2/(8 R(0)) > 0).  [not a certificate] floating-point comparison of
H(t) = R(t)/(16(t^2+1/4)^2 R(0)) (midpoints) with independently computed Fourier-side values of H(t) (constants below)."""
import os, sys, hashlib
os.environ.setdefault('COEFF_EXTRA', os.environ.get('COEFF_DATA', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'coefficients', 'data', '')) + 'extra_smalln_X3e5.json')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_window as CW
from flint import arb
here = os.path.dirname(os.path.abspath(__file__))
H = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('check_r0: hashes poslib %s cert_window %s check_r0 %s extra %s' % (H(os.path.join(here, 'poslib.py')), H(os.path.join(here, 'cert_window.py')),
      H(os.path.abspath(__file__)), H(os.environ['COEFF_EXTRA'])), flush=True)
S = CW.Setup()
Rmin, R0, info = CW.certify(S, 0.0, 1e-6, K=8, rt=0.5)
R0b = arb(Rmin).union(info['Rmax'])
H0raw = 8 * R0b / arb.pi() ** 2
print('[certified] R(0) in [%s, %s] ; H_raw(0) = 8 R(0)/pi^2 in %s  (independent value, not checked here: 0.0011355097904 +- 1.9e-9) ; R(0) > 0: %s' % (
    Rmin.str(10), info['Rmax'].str(10), H0raw.str(10), Rmin > 0))
ref = {1: 1.0236561935088, 2: 1.0984547266103, 4: 1.4634652513158, 8: 4.7863619989632, 12: 34.198796018945, 20: 10148.127885764, 40: 2.8734990736123e12}   # [not a certificate] Fourier-side values of H(t), computed independently in floating point
for t, h in ref.items():
    Rm, Rt, inf = CW.certify(S, float(t), 1e-6, K=8, rt=0.5)
    Hv = Rt / (16 * (arb(t) ** 2 + arb(1) / 4) ** 2 * R0)
    print('[not a certificate] t=%2d: H (midpoints) = %s   Fourier-side value %.13g   rel %.2e' % (t, Hv.str(12), h, float(Hv.mid()) / h - 1))
