"""Independent re-implementation of the certificate primitives.

Toolchain: mpmath (interval arithmetic `mpmath.iv` and multiprecision `mp`) + numpy/LAPACK.
It deliberately shares NO code with arbcert.py / fc.py / gapmap.py / certify_*.py (those use python-flint/Arb).

What is rigorous here and what is not (labels used in README.md):
  * `qu_point`            : exact 2Q_u(v) of a floating-point vector by `mpmath.iv` interval arithmetic
                            (rigorous; the vector may come from anywhere).
  * `qu_lb` / `g_lb`      : interval kernel bounds with outward binary64 conversion.
                            LAPACK only proposes a shift and Cholesky factor. A residual
                            row bound, including gamma_n dot-product rounding bounds,
                            verifies positivity independently of eigenvalue accuracy.
                            Transcendentals in the tail use mpmath.iv.atan2.
                            These are computer-assisted bounds, not Lean proofs of
                            mpmath, NumPy, BLAS, or the floating-point error model.
  * the tail lemma itself (Lemma G) is Lean-checked (`MuStar.tail_psd`).
"""
import math
import numpy as np
import mpmath as mp
from mpmath import iv

mp.mp.dps = 50
iv.dps = 50
EPS = float(np.finfo(float).eps)
TWO_PI = 2 * iv.pi


def dn(x):
    return float(np.nextafter(float(x), -np.inf))


def up(x):
    return float(np.nextafter(float(x), np.inf))


# ---------------------------------------------------------------- kernel (Einstein): K_k = lam v^2/(v^2+k^2), v=t/(2 pi)
def v_bounds(tlo, thi):
    vl = (iv.mpf(tlo) / TWO_PI).a
    vh = (iv.mpf(thi) / TWO_PI).b
    return vl, vh


def kernel_bounds(lam, vl, vh, K):
    """klo[k] <= K_k(v) <= khi[k] for all v in [vl,vh], k=1..K (index 0 unused = 0)."""
    L = iv.mpf(lam)
    a2 = iv.mpf(vl) ** 2
    b2 = iv.mpf(vh) ** 2
    klo = np.zeros(K + 1)
    khi = np.zeros(K + 1)
    for k in range(1, K + 1):
        klo[k] = dn((L * a2 / (a2 + k * k)).a)
        khi[k] = up((L * b2 / (b2 + k * k)).b)
    return klo, khi


def S_up_array(lam, vh, Kmax):
    """S(K) = sum_{k>=K} K_k <= K_K(vh) + lam*vh*atan(vh/K), K=1..Kmax (index 0 unused)."""
    out = np.zeros(Kmax + 1)
    vh = iv.mpf(vh)
    lam = iv.mpf(lam)
    for K in range(1, Kmax + 1):
        val = lam * vh * vh / (vh * vh + K * K) + lam * vh * iv.atan2(vh, iv.mpf(K))
        out[K] = up(val.b)
    return out


def Msize(vh, Nc):
    return max(Nc + 1, int(40 * float(vh)) + 40)


def theta_tail(C, d):
    """theta in (0,1] and the tail coefficient d-(1/theta-1)C (sufficient to be >0)."""
    if not (d > 0):
        return 1.0, d
    th = min(1.0, 2 * C / (2 * C + d)) if C > 0 else 1.0
    return th, d - (1.0 / th - 1.0) * C


def lam_min_lb(lo, hi):
    """Residual verification, not a trusted LAPACK eigenvalue.

    For a computed F and shift c, B-cI = FF^T + R. Bound ||R|| by
    max row sum. gamma_{n+8} bounds dot-product and residual rounding;
    an additional 128*n*eps entrywise allowance covers the preceding
    binary64 matrix assembly and tail-penalty arithmetic. IEEE binary64
    round-to-nearest with no overflow is part of the trust base.
    """
    n = lo.shape[0]
    mid = 0.5 * (lo + hi)
    assembly = 128 * n * EPS * (1 + np.abs(lo) + np.abs(hi))
    rad = 0.5 * (hi - lo) + assembly
    c = float(np.linalg.eigvalsh(mid)[0]) * 0.5
    if c <= 0:
        return -math.inf
    try:
        F = np.linalg.cholesky(mid - c * np.eye(n))
    except np.linalg.LinAlgError:
        return -math.inf
    product = F @ F.T
    gamma = (n + 8) * EPS / (1 - (n + 8) * EPS)
    residual = mid - c * np.eye(n) - product
    error = gamma * (np.abs(F) @ np.abs(F).T + np.abs(mid) + c * np.eye(n) + np.abs(product))
    rows = np.sum(np.abs(residual) + error + rad, axis=1)
    return dn(c - up(float(np.max(rows)) * (1 + 4 * n * EPS)))


def qu_lb(lam, Nc, u, tlo, thi, M=None):
    """Lower bound on lambda_min(2Q_u) for t in [tlo,thi]  (None if the tail certificate fails)."""
    vl, vh = v_bounds(tlo, thi)
    if M is None:
        M = Msize(vh, Nc)
    K = 2 * M + 2
    klo, khi = kernel_bounds(lam, vl, vh, K)
    S = S_up_array(lam, vh, K)
    S1, SM = S[1], S[M]
    C = up(S1 + SM)
    d = dn((2 * M + 1) - up(2 * SM))
    th, tail = theta_tail(C, d)
    if not (tail > 0):
        return None
    n = np.arange(M)
    idx = np.abs(n[:, None] - n[None, :])
    idx2 = n[:, None] + n[None, :] + 1
    chi = (n < Nc).astype(float)
    Lam_lo = np.concatenate([[0.0], np.cumsum(klo[1:])])
    Lam_hi = np.concatenate([[0.0], np.cumsum(khi[1:])])
    # outward cumulative sums: add relative slack for float accumulation
    Lam_lo = Lam_lo * (1 - 4 * K * EPS)
    Lam_hi = Lam_hi * (1 + 4 * K * EPS)
    lo = -(khi[idx] + khi[idx2]) + 2 * u * np.outer(chi, chi)
    hi = -(klo[idx] + klo[idx2]) + 2 * u * np.outer(chi, chi)
    rho = S[M - n] + S[M + n + 1]
    diag_lo = (2 * n + 1) + 2 * Lam_lo[n] - khi[2 * n + 1] + 2 * u * chi - th * rho
    diag_hi = (2 * n + 1) + 2 * Lam_hi[n] - klo[2 * n + 1] + 2 * u * chi - th * rho * (1 - 4 * EPS)
    # diagonal entries replace the idx==0 entries
    lo[n, n] = diag_lo
    hi[n, n] = diag_hi
    # th*rho enters with a minus sign: lower bound uses rho upper (S is an upper bound) -> fine for lo;
    # for hi we only need an enclosure of the SAME quantity, so any value >= lo works (rad is then wider).
    hi[n, n] = np.maximum(hi[n, n], lo[n, n])
    kb = lam_min_lb(lo, hi)
    if not (kb > 0):
        return None
    return min(kb, tail)


def g_lb(lam, tlo, thi, M=None):
    """Lower bound on lambda_min(G) for t in [tlo,thi]."""
    vl, vh = v_bounds(tlo, thi)
    if M is None:
        M = Msize(vh, 1)
    K = 2 * M + 2
    klo, khi = kernel_bounds(lam, vl, vh, K)
    S = S_up_array(lam, vh, K)
    S1, SM = S[1], S[M]
    C = up(S1)
    d = dn((2 * M + 1) - SM)
    th, tail = theta_tail(C, d)
    if not (tail > 0):
        return None
    n = np.arange(M)
    idx = np.abs(n[:, None] - n[None, :])
    Lam_lo = np.concatenate([[0.0], np.cumsum(klo[1:])]) * (1 - 4 * K * EPS)
    Lam_hi = np.concatenate([[0.0], np.cumsum(khi[1:])]) * (1 + 4 * K * EPS)
    lo = -khi[idx]
    hi = -klo[idx]
    rho = S[M - n]
    diag_lo = (2 * n + 1) + 2 * Lam_lo[n] - th * rho
    diag_hi = np.maximum((2 * n + 1) + 2 * Lam_hi[n] - th * rho * (1 - 4 * EPS), diag_lo)
    lo[n, n] = diag_lo
    hi[n, n] = diag_hi
    kb = lam_min_lb(lo, hi)
    if not (kb > 0):
        return None
    return min(kb, tail)


def cover(f, t0, t1, h0=0.25, kappa=0.0, hmin=1e-6, hmax=8.0):
    """Adaptive cover of [t0,t1] by intervals on which f(tlo,thi) > kappa.  Returns (segments, ok, minlb)."""
    t = float(t0)
    t1 = float(t1)
    h = h0
    segs = []
    mn = math.inf
    while t < t1:
        hh = min(h, t1 - t)
        tn = t + hh
        if tn <= t:
            return segs, False, mn
        lb = f(t, tn)
        if lb is not None and lb > kappa:
            segs.append((t, tn, lb))
            mn = min(mn, lb)
            t = tn
            h = min(h * 1.5, hmax)
        else:
            h *= 0.5
            if h < hmin:
                return segs, False, mn
    return segs, True, mn


# ---------------------------------------------------------------- exact point evaluation of 2Q_u(v)
def qu_point(lam, Nc, u, t, v):
    """Interval enclosure of 2Q_u(v) at t=1/T for a float vector v.  u may be an iv/mpf number."""
    vp = iv.mpf(t) / TWO_PI
    N = len(v)
    L = iv.mpf(lam)
    v2 = vp * vp
    K = [None] + [L * v2 / (v2 + k * k) for k in range(1, 2 * N + 2)]
    Lam = [iv.mpf(0)]
    for n in range(1, N):
        Lam.append(Lam[-1] + K[n])
    vv = [iv.mpf(float(x)) for x in v]
    s = iv.mpf(0)
    for n in range(N):
        s += ((2 * n + 1) + 2 * Lam[n] - K[2 * n + 1]) * vv[n] ** 2
    off = iv.mpf(0)
    for n in range(N):
        for m in range(n + 1, N):
            off += (K[m - n] + K[n + m + 1]) * vv[n] * vv[m]
    chi = sum(vv[n] for n in range(min(Nc, N)))
    return s - 2 * off + 2 * iv.mpf(u) * chi * chi


def build_qu_float(lam, Nc, u, T, N):
    """Float matrix of 2Q_u (own builder) used ONLY to propose an eigenvector."""
    v = 1.0 / (2 * math.pi * T)
    n = np.arange(N)
    kk = lambda k: lam * v * v / (v * v + np.asarray(k, dtype=float) ** 2)
    Kk = np.concatenate([[0.0], kk(np.arange(1, 2 * N + 3))])
    Lam = np.cumsum(Kk)
    A = -(Kk[np.abs(n[:, None] - n[None, :])] + Kk[n[:, None] + n[None, :] + 1])
    chi = (n < Nc).astype(float)
    A = A + 2 * u * np.outer(chi, chi)
    A[n, n] = (2 * n + 1) + 2 * Lam[n] - Kk[2 * n + 1] + 2 * u * chi
    return A


def Nfor(T, Nc):
    return min(400, max(Nc + 10, int(10 / (2 * math.pi * T)) + 30))


def lowest_vector(A):
    w, V = np.linalg.eigh(A)
    v = V[:, 0]
    return v / np.max(np.abs(v)), w[0]


# ---------------------------------------------------------------- witness energy (direct, mpmath 50 digits)
def energy_direct(lam, Nc, u, t, z, N, interval=False):
    """E_T(S) for the folded chain with the exterior frozen at the normal state.
    Exterior weight: sum_{m>=N} (K_{m-n} - K_{n+m+1}) = sum_{j=N-n}^{N+n} K_j  (telescoping, 2n+1 terms).
    z = [theta_xi(N), phi_xi(N), theta_eta(N), phi_eta(N)]; the eta chain is eta_n = M S_{-n-1}."""
    ctx = iv if interval else mp
    vp = ctx.mpf(t) / (2 * ctx.pi)
    lam = ctx.mpf(lam)
    Kf = lambda k: lam * vp * vp / (vp * vp + k * k)
    K = [None] + [Kf(k) for k in range(1, 2 * N + 3)]
    z = [ctx.mpf(x) for x in z]
    th, ph, tb, pb = z[:N], z[N:2 * N], z[2 * N:3 * N], z[3 * N:]
    xi = [(ctx.sin(th[n]) * ctx.cos(ph[n]), ctx.sin(th[n]) * ctx.sin(ph[n]), ctx.cos(th[n])) for n in range(N)]
    et = [(ctx.sin(tb[n]) * ctx.cos(pb[n]), ctx.sin(tb[n]) * ctx.sin(pb[n]), ctx.cos(tb[n])) for n in range(N)]
    E = ctx.mpf(0)
    for n in range(N):
        wt = (2 * n + 1) + sum(K[j] for j in range(N - n, N + n + 1))
        E += wt * (2 - xi[n][2] - et[n][2])
        for m in range(n + 1, N):
            dxx = sum(xi[n][i] * xi[m][i] for i in range(3))
            dee = sum(et[n][i] * et[m][i] for i in range(3))
            E += K[m - n] * ((1 - dxx) + (1 - dee))
        for m in range(N):
            E -= K[n + m + 1] * (1 + xi[n][0] * et[m][0] + xi[n][1] * et[m][1] - xi[n][2] * et[m][2])
    X = sum(xi[n][0] + et[n][0] for n in range(min(Nc, N)))
    Y = sum(xi[n][1] + et[n][1] for n in range(min(Nc, N)))
    return E + ctx.mpf(u) / 2 * (X * X + Y * Y)


def energy_I2(lam, Nc, u, t, z, N):
    """The same energy through Proposition I2: 2Q_u(P)+2Q^o(R)+G(alpha)/2+G(beta)/2+<alpha,H beta>, with the
    block weights and exterior handled as in the paper (exact multiprecision)."""
    vp = mp.mpf(t) / (2 * mp.pi)
    lam = mp.mpf(lam)
    Kf = lambda k: lam * vp * vp / (vp * vp + k * k)
    K = [None] + [Kf(k) for k in range(1, 2 * N + 3)]
    z = [mp.mpf(x) for x in z]
    th, ph, tb, pb = z[:N], z[N:2 * N], z[2 * N:3 * N], z[3 * N:]
    xx = [mp.sin(th[n]) * mp.cos(ph[n]) for n in range(N)]
    xy = [mp.sin(th[n]) * mp.sin(ph[n]) for n in range(N)]
    xz = [mp.cos(th[n]) for n in range(N)]
    ex = [mp.sin(tb[n]) * mp.cos(pb[n]) for n in range(N)]
    ey = [mp.sin(tb[n]) * mp.sin(pb[n]) for n in range(N)]
    ez = [mp.cos(tb[n]) for n in range(N)]
    Lam = [mp.mpf(0)]
    for n in range(1, N):
        Lam.append(Lam[-1] + K[n])
    c = [(2 * n + 1) + 2 * Lam[n] for n in range(N)]
    Tm = lambda n, m: K[abs(n - m)] if n != m else mp.mpf(0)
    Hm = lambda n, m: K[n + m + 1]

    def form(a, kind):
        s = sum(c[n] * a[n] ** 2 for n in range(N))
        for n in range(N):
            for m in range(N):
                if kind == "Qu":
                    s -= (Tm(n, m) + Hm(n, m)) * a[n] * a[m]
                elif kind == "Qo":
                    s -= (Tm(n, m) - Hm(n, m)) * a[n] * a[m]
                elif kind == "G":
                    s -= Tm(n, m) * a[n] * a[m]
        if kind == "Qu":
            s += 2 * mp.mpf(u) * sum(a[n] for n in range(min(Nc, N))) ** 2
        return s

    Px = [(xx[n] + ex[n]) / 2 for n in range(N)]
    Py = [(xy[n] + ey[n]) / 2 for n in range(N)]
    Rx = [(xx[n] - ex[n]) / 2 for n in range(N)]
    Ry = [(xy[n] - ey[n]) / 2 for n in range(N)]
    al = [1 - xz[n] for n in range(N)]
    be = [1 - ez[n] for n in range(N)]
    bil = sum(Hm(n, m) * al[n] * be[m] for n in range(N) for m in range(N))
    return (form(Px, "Qu") + form(Py, "Qu") + form(Rx, "Qo") + form(Ry, "Qo")
            + form(al, "G") / 2 + form(be, "G") / 2 + bil)


def S_tail_check(lam, v, K):
    """mp check of S(K) <= K_K + lam v atan(v/K) (tail lemma input)."""
    lam = mp.mpf(lam)
    v = mp.mpf(v)
    ex = mp.nsum(lambda k: lam * v * v / (v * v + k * k), [K, mp.inf])
    bd = lam * v * v / (v * v + K * K) + lam * v * mp.atan(v / K)
    return ex, bd
