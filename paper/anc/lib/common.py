"""Shared helpers: parameter files and hashes, prime powers, outward decimal rounding of Arb balls."""
import hashlib
import json
import os
from fractions import Fraction
from flint import arb, fmpq, fmpz

ANC = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class CertificationError(RuntimeError):
    """A precondition or a check of a certificate failed."""


def require(cond, msg='check failed'):
    """Explicit check (used instead of assert, which python -O would remove): raise CertificationError unless cond."""
    if not cond:
        raise CertificationError(msg)


def relpath(path):
    """Path relative to the anc/ directory (never print absolute paths)."""
    return os.path.relpath(os.path.abspath(path), ANC)


def sha256_file(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def load_factor_params(path):
    """Parameter file of a zero-killing function F_rep = Xi^2 (H + eps e^{-pi t^2}), H(t) = prod_j (1 + r_j t^2 + s_j t^4).

    JSON keys: 'J', 'eps' (a string '1e-E'), 'factors' = [[r_j, s_j], ...] (exact rationals written as decimal strings
    or 'p/q' strings), 'factors_sha256' = sha256 of the canonical list '\\n'.join(r_j + ' ' + s_j) (checked here).
    Returns (meta, [(fmpq r_j, fmpq s_j)], file_sha256)."""
    raw = open(path, 'rb').read()
    d = json.loads(raw)
    canon = '\n'.join('%s %s' % (r, s) for r, s in d['factors']).encode()
    h = hashlib.sha256(canon).hexdigest()
    if h != d['factors_sha256']:
        raise ValueError('canonical factor-list sha256 mismatch: %s' % h)
    rs = []
    for a, b in d['factors']:
        fa, fb = Fraction(a), Fraction(b)
        rs.append((fmpq(fa.numerator, fa.denominator), fmpq(fb.numerator, fb.denominator)))
    if len(rs) != int(d['J']):
        raise ValueError('J does not match the number of factors')
    return d, rs, hashlib.sha256(raw).hexdigest()


def eps_exponent(eps_string):
    """'1e-E' -> E (only exact negative powers of ten are used)."""
    s = eps_string.lower()
    require(s.startswith('1e-'), 'eps must be an exact negative power of ten 1e-E')
    return int(s[3:])


def prime_powers(limit):
    """[(n, p)] for prime powers n = p^k <= limit, increasing."""
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    out = []
    for p in range(2, limit + 1):
        if sieve[p]:
            q = p
            while q <= limit:
                out.append((q, p))
                q *= p
    return sorted(out)


def first_prime_powers(J):
    lim = 16
    while True:
        pp = prime_powers(lim)
        if len(pp) >= J:
            return pp[:J]
        lim *= 2


def _decimal_digits_of(u, nd, up):
    """Exact decimal with nd significant digits that is >= u (up) or <= u (down); u an exact arb > 0."""
    u = arb(u)
    e = int((u.log() / arb(10).log()).mid().floor().unique_fmpz())
    while arb(10) ** e > u:                     # fix the decade exactly: 10^e <= u < 10^(e+1)
        e -= 1
    while arb(10) ** (e + 1) <= u:
        e += 1
    w = u * arb(10) ** (nd - 1 - e)
    k = (arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz()
    if k >= fmpz(10) ** nd:                     # rounding up carried into the next decade
        k, e = fmpz(10) ** (nd - 1), e + 1
    ks = str(int(k))
    require(len(ks) == nd, 'decimal rounding: wrong number of digits')
    out = '%s.%se%d' % (ks[0], ks[1:], e)
    Fr = Fraction(out)
    q = arb(fmpq(Fr.numerator, Fr.denominator))
    require((q >= u) if up else (q <= u), 'decimal rounding: wrong direction')   # exact check of the direction
    return out


def round_up(v, nd=8):
    """Smallest nd-significant-digit decimal >= every point of the ball v (v > 0)."""
    require(v > 0, 'round_up needs a positive ball')
    return _decimal_digits_of(arb(v.upper()), nd, True)


def round_down(v, nd=8):
    """Largest nd-significant-digit decimal <= every point of the ball v (v > 0)."""
    require(v > 0, 'round_down needs a positive ball')
    return _decimal_digits_of(arb(v.lower()), nd, False)


def _fixed(v, nd, up):
    """Decimal string with nd digits after the point, >= every point of the ball v (up) or <= every point (down)."""
    u = arb(v.upper()) if up else arb(v.lower())
    w = u * arb(10) ** nd
    k = int((arb(w.upper()).ceil() if up else arb(w.lower()).floor()).unique_fmpz())
    q, r = divmod(abs(k), 10 ** nd)
    out = ('-' if k < 0 else '') + ('%d.%0*d' % (q, nd, r) if nd > 0 else '%d' % q)
    Fr = Fraction(out)
    qa = arb(fmpq(Fr.numerator, Fr.denominator))
    require((qa >= u) if up else (qa <= u), 'fixed-point rounding: wrong direction')   # exact check of the direction
    return out


def fixed_up(v, nd):
    """Smallest decimal with nd digits after the point that is >= every point of the ball v."""
    return _fixed(v, nd, True)


def fixed_down(v, nd):
    """Largest decimal with nd digits after the point that is <= every point of the ball v."""
    return _fixed(v, nd, False)


def exact_max(vals):
    """Largest of a list of arbs, compared by their exact upper endpoints (no binary64 conversion)."""
    best = None
    for v in vals:
        if best is None or arb(v.upper()) > arb(best.upper()):
            best = v
    return best


def exact_min(vals):
    """Smallest of a list of arbs, compared by their exact lower endpoints (no binary64 conversion)."""
    best = None
    for v in vals:
        if best is None or arb(v.lower()) < arb(best.lower()):
            best = v
    return best


def check_decimal(s, q, up):
    """Exact a-posteriori check of a printed decimal string s against the exact rational q (Fraction or int):
    s >= q if up, s <= q if not up.  Returns s.  Used by the general/ scripts, which round exact rationals to decimals
    themselves (their own formatting); kappa/ and exact/ use round_up/round_down above, which check in the same way."""
    v = Fraction(s)
    require(v >= q if up else v <= q, 'decimal rounding: wrong direction for %s' % s)
    return s


def check_round_up(v, s):
    """Exact check that the decimal string s is >= upper(v)."""
    Fr = Fraction(s)
    return arb(fmpq(Fr.numerator, Fr.denominator)) >= arb(v.upper())
