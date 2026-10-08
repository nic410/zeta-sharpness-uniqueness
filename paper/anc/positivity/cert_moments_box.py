"""Certificate M-box: the moment certificate on the trivial-bound box (Section 6 and Appendix A of the paper).

The box (boxlib.py; Section 6.1 of the paper): sequences (b_n) with |b_n - c_n| <= w_n, c_n := n T1_n + delta_{n1}/4 (the term
c = 1 of the Kloosterman series, S(+-1, n; 1) = 1) and w_n := abar_n varrho(z_n) (the bound for the terms c >= 2 from
|S(+-1, n; c)| <= phi(c) in the proof of Theorem 6.1).  Every element of the box satisfies the bounds of Theorems 6.1-6.2;
for n > N these bounds are all that is used.  The coefficients a_n of the paper lie in the box.

For a sequence b in the box let M_2j(b) := (1/pi) int_1^oo W_j(x) Ghat_b(x) dx/x, Ghat_b(x) := sin^2(pi x) sqrt(x) sum_n b_n
K0(4 pi sqrt(n x)), and P_K(t; b) := sum_{j<=2K+1} (-1)^j c_j(t) M_2j(b), c_j(t) = (2 pi t)^{2j}/(2j)!.  This script certifies a
lower bound for P_K(t; b) that is valid for EVERY b in the box.  P_K is linear in b:  M_2j(b) = sum_n b_n M_2j^(n) (+ tail), so
    P_K(t; b) >= P_K^low(t; centre, tail hull) - sum_{n <= n0} w_n |pi_n(t)| - eps * P_K^abs(t),
    pi_n(t) := sum_j (-1)^j c_j(t) M_2j^(n),  M_2j^(n) := (1/pi) int_1^oo W_j(x) sin^2(pi x) sqrt(x) K0(4 pi sqrt(n x)) dx/x,
    eps := max_{n0 < n <= N} w_n/(c_n - w_n),  P_K^abs(t) := sum_j c_j(t) M_2j(centre)^upper   (all M^(n) >= 0).
Applied to b = (a_n), for which P_K(t; a) <= F(t) = Xi(t)^2 H_raw(t) (Lemma in Section 6.3 of the paper), a positive lower
bound gives F(t) > 0, hence H_raw(t) > 0.  (For a general b in the box there is no function H; the statement is about the
linear functional P_K(t; .) only.)
Quadrature, panels and the bounds for the centre are those of cert_moments.py (imported); the single-term moments use the
same panels with the ellipse majorant |sin^2(pi x)| |sqrt x| K0(4 pi sqrt(n) sqrt(Re x)).
The verdict is that the certified interval [0, reach] contains [0, T_REQ].
Usage: cert_moments_box.py N n0 J T T_REQ PREC NPROC    (shipped run: 60 8 15 12 9 64 6)"""
import sys, os, json, math, time, hashlib
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_moments as CM
import boxlib as BX
from flint import arb, ctx

a_ = sys.argv[1:]
N_ = int(a_[0]) if len(a_) > 0 else 60
N0 = int(a_[1]) if len(a_) > 1 else 8
J_ = int(a_[2]) if len(a_) > 2 else 15
T_ = float(a_[3]) if len(a_) > 3 else 12.0
TR_ = float(a_[4]) if len(a_) > 4 else 9.0
P_ = int(a_[5]) if len(a_) > 5 else 64
NP_ = int(a_[6]) if len(a_) > 6 else 6
CM.configure(P_)
PI = arb.pi()


def main():
    t0 = time.time()
    here = os.path.abspath(__file__)
    Ac, files = CM.load_coeffs('centre', N_)
    print('cert_moments_box.py N=%d n0=%d J=%d T=%g T_req=%g prec=%d ; hashes: script %s cert_moments %s boxlib %s besselk %s ; %s' % (
        N_, N0, J_, T_, TR_, P_, CM.sha(here), CM.sha(CM.__file__), CM.sha(BX.__file__), CM.sha(os.path.join(CM.ANC, 'lib', 'besselk.py')),
        ' '.join('%s %s' % kv for kv in files.items())))
    T1 = json.load(open(os.path.join(CM.DATA, 'an_cert_X1e4.json')))['T1']
    w = [None] + [BX.centre_halfwidth(n, T1[str(n)])[1] for n in range(1, N_ + 1)]
    w = [None] + [arb(x.upper()) for x in w[1:]]
    for n in (1, 2, 3):
        print('box n=%d: centre c_n = %s, half-width w_n = %s (relative %.2e)' % (n, Ac[n].str(12), w[n].str(6), float(w[n] / Ac[n])))
    eps = arb(0)
    for n in range(N0 + 1, N_ + 1):
        r = w[n] / arb((Ac[n] - w[n]).lower())
        eps = eps.max(arb(r.upper()))
    eps = arb(eps.upper())
    print('eps = max_{n0<n<=N} w_n/(c_n - w_n) = %s' % eps.str(5), flush=True)
    GL = [arb.legendre_p_root(CM.MNODES, i, weight=True) for i in range(CM.MNODES)]
    P = CM.panels()
    meta = []; flat = []
    for pi_, (a, b, k, rho) in enumerate(P):
        h = (b - a) / 2; c = (a + b) / 2
        xs = [c + h * x for (x, wt) in GL]
        meta.append((a, b, k, rho, xs, [h * wt for (x, wt) in GL]))
        for ni, x in enumerate(xs):
            flat.append((pi_, ni, CM.ship(x, 50)))
    flat.sort(key=lambda r: float(r[2][0]))
    chunks = [flat[i::NP_ * 8] for i in range(NP_ * 8)]
    with Pool(NP_, initializer=CM._init, initargs=('centre', N_, P_)) as pool:
        res = pool.map(CM._work, [([c[2] for c in ch], N_) for ch in chunks])
    G = {}; Nused = {}
    for ch, rr in zip(chunks, res):
        for (pi_, ni, _), (gs, Nn) in zip(ch, rr):
            G[(pi_, ni)] = CM.unship(gs); Nused[pi_] = max(Nused.get(pi_, 0), Nn)
    print('centre node values: %d nodes (%.0fs)' % (len(G), time.time() - t0), flush=True)
    TC = {Nn: CM.tail_consts(Nn) for Nn in set(Nused.values())}
    J = J_
    Mc = [arb(0)] * (J + 1); Ec = [arb(0)] * (J + 1)
    Ms = {n: [arb(0)] * (J + 1) for n in range(1, N0 + 1)}; Es = {n: [arb(0)] * (J + 1) for n in range(1, N0 + 1)}
    for pi_, (a, b, k, rho, xs, ws) in enumerate(meta):
        Nn = Nused[pi_]
        Mb, Mcb, argx, xlo = CM.Mbound(a, b, k, rho, Nn, Ac, TC[Nn], J)
        q = (64 * (b - a) / 2 / 15) * rho ** (-2 * CM.MNODES) / (1 - rho ** -2)
        # single-term ellipse majorants
        xlo_, xhi_, B_ = CM.ellipse_box(a, b, rho)
        absx = (xhi_ ** 2 + B_ ** 2).sqrt()
        rx = arb(abs(xhi_ - k).upper()).max(arb(abs(xlo_ - k).upper()))
        r = arb((rx ** 2 + B_ ** 2).sqrt().upper())
        s2 = (PI * r).sinh() ** 2; s2b = (PI * B_).cosh() ** 2
        s2 = s2 if s2 < s2b else s2b
        Wb = [arb(0)] * (J + 1)
        argx_ = (B_ / xlo_).atan()
        for m in range(1, k + 1):
            Lm = arb(abs((xlo_ / m).log()).upper()).max(arb(abs((absx / m).log()).upper())) + argx_
            Lm = arb(Lm.upper()) / (2 * PI)
            wm = arb(CM.dcount(m)) / arb(m).sqrt()
            for j in range(J + 1):
                Wb[j] = Wb[j] + wm * Lm ** (2 * j)
        for n in range(1, N0 + 1):
            Gs = s2 * absx.sqrt() * CM.K0(4 * PI * arb(n).sqrt() * xlo_.sqrt())
            for j in range(J + 1):
                Es[n][j] += q * arb((Wb[j] * Gs / (PI * xlo_)).upper())
        for j in range(J + 1):
            Ec[j] += q * Mb[j]
        for ni, (x, wt) in enumerate(zip(xs, ws)):
            Wl = CM.W_list(x, k, J)
            base = wt / (PI * x)
            g = G[(pi_, ni)]
            for j in range(J + 1):
                Mc[j] += Wl[j] * base * g
            s2x = (PI * x).sin() ** 2 * x.sqrt()
            for n in range(1, N0 + 1):
                gs = s2x * CM.K0(4 * PI * (n * x).sqrt())
                for j in range(J + 1):
                    Ms[n][j] += Wl[j] * base * gs
    # sliver [1, 1+2^-KG] and tail [X, oo): centre as in cert_moments.py; single terms by the direct bounds below
    hs = arb(2) ** (-CM.KG)
    gs = (1 + hs) ** arb(0.25) * (hs ** 2 / 16 + (1 + hs) / (32 * PI ** 2))
    X = arb(CM.XMAX); kapX = 4 * PI * (X.sqrt() - 1)
    fac = (1 + 2 * (1 + kapX) / kapX ** 2) / (16 * PI ** 2) * (4 * PI).exp()
    cX = X.log() / (2 * PI * X.sqrt()); b4 = 4 * PI
    for j in range(J + 1):
        sl = hs * gs * ((1 + hs).log() / (2 * PI)) ** (2 * j) / PI
        qq = arb(j) + arb(0.75)
        tl = 2 / PI * cX ** (2 * j) * fac * 2 * b4 ** (-2 * qq - 2) * (b4 * X.sqrt()).gamma_upper(2 * qq + 2)
        Mc[j] = Mc[j] + arb(0, Ec[j].upper()) + arb(0, sl.upper()) / 2 + sl / 2 + arb(0, tl.upper()) / 2 + tl / 2
        for n in range(1, N0 + 1):
            # single term on the sliver: sin^2(pi x) sqrt x K0(4 pi sqrt(n x)) <= pi^2 hs^2 (1+hs)^{1/2} K0(4 pi sqrt n)
            sl1 = hs * PI ** 2 * hs ** 2 * (1 + hs).sqrt() * CM.K0(4 * PI * arb(n).sqrt()) * ((1 + hs).log() / (2 * PI)) ** (2 * j) / PI
            # beyond X: sqrt(x) K0(4 pi sqrt(n x)) <= x^{1/4} e^{-4 pi sqrt x}/(2 sqrt 2); W_j <= 2 x^{3/2} c^{2j} x^j (as for the centre)
            tl1 = 2 / PI * cX ** (2 * j) / (2 * arb(2).sqrt()) * 2 * b4 ** (-2 * qq - 2) * (b4 * X.sqrt()).gamma_upper(2 * qq + 2)
            Ms[n][j] = Ms[n][j] + arb(0, Es[n][j].upper()) + arb(0, sl1.upper()) / 2 + sl1 / 2 + arb(0, tl1.upper()) / 2 + tl1 / 2
    print('centre moments: M_0 = %s, M_2 = %s ; single-term moments n=1: %s %s' % (Mc[0].str(10), Mc[1].str(10), Ms[1][0].str(10), Ms[1][1].str(10)))
    # consistency check (informational): sum_n c_n M^(n) <= M(centre)
    s0 = sum((Ac[n] * Ms[n][0] for n in range(1, N0 + 1)), arb(0))
    print('[check] sum_{n<=n0} c_n M_0^(n) = %s <= M_0(centre) = %s : %s' % (s0.str(10), Mc[0].str(10), s0.lower() <= Mc[0].upper()))
    best = None
    for K in range(0, (J - 1) // 2 + 1):
        top = 2 * K + 1

        def parts(t, M):
            Pp = arb(0); Pm = arb(0)
            for j in range(top + 1):
                c = (2 * PI * t) ** (2 * j) / arb(2 * j).fac()
                if j % 2 == 0:
                    Pp += c * arb(M[j].lower())
                else:
                    Pm += c * arb(M[j].upper())
            return Pp, Pm

        def parts_up(t, M):
            Pp = arb(0); Pm = arb(0)
            for j in range(top + 1):
                c = (2 * PI * t) ** (2 * j) / arb(2 * j).fac()
                if j % 2 == 0:
                    Pp += c * arb(M[j].upper())
                else:
                    Pm += c * arb(M[j].lower())
            return Pp, Pm
        dt = 1 / arb(256)
        ta = arb(0); reach = 0.0; ok = True
        while float(ta.mid()) < T_ - 1e-12:
            tb = ta + dt
            Ppa, _ = parts(ta, Mc); _, Pmb = parts(tb, Mc)
            low = Ppa - Pmb
            corr = arb(0)
            for n in range(1, N0 + 1):
                ua, la = parts_up(ta, Ms[n]); ub, lb = parts_up(tb, Ms[n])
                pa, ma = parts(ta, Ms[n]); pb, mb = parts(tb, Ms[n])
                # on [ta,tb]: pi_n in [P+(ta)lower - P-(tb)upper, P+(tb)upper - P-(ta)lower]
                hi_ = ub - la; lo_ = pa - mb
                corr += w[n] * arb(abs(hi_).upper()).max(arb(abs(lo_).upper()))
            pabs = sum(((2 * PI * tb) ** (2 * j) / arb(2 * j).fac() * arb(Mc[j].upper()) for j in range(top + 1)), arb(0))
            val = low - corr - eps * pabs
            if not (val > 0):
                ok = False
                break
            reach = float(tb.mid()); ta = tb
        print('box moment bound with M_0..M_%d: lower bound of P_K(t; b) > 0 for every b in the box, on [0, %.8f]' % (2 * top, reach), flush=True)
        if best is None or reach > best[1]:
            best = (2 * top, reach)
    print('DECISIVE (Certificate M-box, trivial Kloosterman bound only): P_K(t; b) > 0 for every b in the box, hence (b = a) '
          'F(t) = Xi(t)^2 H_raw(t) > 0 and H_raw(t) > 0, for |t| <= %.8f (moments M_0..M_%d) ; covers [0, %g]: %s   (%.0fs)'
          % (best[1], best[0], TR_, best[1] >= TR_, time.time() - t0))


if __name__ == '__main__':
    main()
