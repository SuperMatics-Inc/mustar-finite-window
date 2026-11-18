"""Shared Arb (python-flint) certificates for the infinite even form Q_u and the longitudinal form G.

Einstein kernel lam(k) = lam*vp^2/(vp^2+k^2), vp = 1/(2 pi T) (Omega = 1), temperature via t = 1/T.
On l^2(N_0) (finitely supported v):
  2Q_u(v) = sum_n (w_n + 2Lam_n) v_n^2 - sum_{n,m} W_nm v_n v_m + 2u (sum_{n<Nc} v_n)^2,
            w_n = 2n+1, Lam_n = sum_{k=1}^n lam(k), W_nm = [n!=m] lam|n-m| + lam(n+m+1);
  G(v)    = sum_n (w_n + 2Lam_n) v_n^2 - sum_{n!=m} lam|n-m| v_n v_m.
Infinite-chain lower bound (block [0,M), M >= Nc, tail [M,inf)). Block-tail couplings: 2|ab| <= theta a^2 + b^2/theta
(0 < theta <= 1); tail-tail couplings: 2|ab| <= a^2 + b^2. Hence
  v^T A v >= v_B^T (A_BB - theta diag rho) v_B + sum_{m>=M} [d_m - (1/theta - 1) c_m] v_m^2,
  rho_n = sum_{m>=M} |A_nm| (n < M),  c_m = sum_{n<M} |A_nm|,  d_m = A_mm - sum_{m'!=m} |A_mm'|  (m >= M).
Q_u: rho_n <= S(M-n) + S(M+n+1), c_m <= S(1) + S(M+1), d_m = 2m+1 - 2 sum_{k>m} lam(k) >= 2M+1 - 2 S(M+1).
G:   rho_n <= S(M-n),              c_m <= S(1),          d_m = 2m+1 -   sum_{k>m} lam(k) >= 2M+1 -   S(M+1).
theta = 2C/(2C + dlow) (exact float) puts half the tail margin into absorbing the block-tail couplings.
S(K) = sum_{k>=K} lam(k) <= lam(K) + lam*vp*atan(vp/K) (integral test; lam(k) decreasing); same bound for sum_{k>K}.
Block: verified Cholesky, B - cI = L L^T + R, ||R||_2 <= max_i sum_j |R_ij|  =>  lambda_min(B) >= c - ||R||.
Temperature intervals t in [tlo, thi] <=> vp in [vlo, vhi]. Every lam(k) is increasing in vp, so lam(k) over the
interval is enclosed by the hull of its two endpoint values; the bounds S(K) and sum_{k>m} lam(k) <= lam*vp*atan(vp/m)
are increasing in vp, so their values at vhi bound them on the whole interval. Every matrix entry is therefore an
Arb ball valid simultaneously for all t in the interval."""
import numpy as np
from flint import arb, arb_mat, ctx

ctx.prec = 128
PI = arb.pi()


def vp_pt(t):
    """vp = t/(2 pi) for an exact float t = 1/T."""
    return arb(t) / (2 * PI)


def lam_pt(lam, k, vp):
    """lam(k) at a point vp (tiny ball)."""
    return lam * vp * vp / (vp * vp + k * k)


def lam_iv(lam, k, vlo, vhi):
    """Enclosure of lam(k) for all vp in [vlo, vhi] (monotone increasing in vp)."""
    return lam_pt(lam, k, vlo).union(lam_pt(lam, k, vhi))


def S_ub(lam, K, vhi):
    """Upper bound for sum_{k>=K} lam(k), K >= 1, valid for all vp <= vhi."""
    return lam_pt(lam, K, vhi) + lam * vhi * (vhi / arb(K)).atan()


def chol_cert(B):
    """B: symmetric list of lists of arb. Certified lower bound (arb) on lambda_min, or None."""
    M = len(B)
    Bm = np.array([[float(x.mid()) for x in row] for row in B])
    ev = np.linalg.eigvalsh(Bm)[0]
    if ev <= 0:
        return None
    c = 0.5 * ev
    L = np.linalg.cholesky(Bm - c * np.eye(M))
    La = arb_mat(L.tolist())
    LLt = La * La.transpose()
    r = arb(0)  # exact (radius-0) running maximum of rigorous row-sum upper bounds
    for i in range(M):
        s = arb(0)
        for j in range(M):
            s += (B[i][j] - (arb(c) if i == j else 0) - LLt[i, j]).abs_upper()
        su = arb(s.upper())
        if su > r:
            r = su
    return arb(c) - r


def lower_min(a, b):
    """Exact ball equal to min(lower(a), lower(b))."""
    la, lb = arb(a.lower()), arb(b.lower())
    return la if la < lb else lb


def _Msize(vhi, Nc):
    return max(Nc + 1, int(40 * float(vhi.upper())) + 40)


def _theta(C, dlow):
    """Exact float theta in (0, 1] and the certified tail coefficient dlow - (1/theta - 1) C."""
    Cf, df = float(C.upper()), float(dlow.lower())
    th = arb(max(1e-12, min(1.0, 2 * Cf / (2 * Cf + df)))) if df > 0 else arb(1)
    return th, dlow - (1 / th - 1) * C


def Qu_bound(lam, Nc, u, tlo, thi):
    """Certified lower bound on lambda_min(2Q_u) on l^2(N_0), valid for all t in [tlo, thi]; None if failed."""
    vlo, vhi = vp_pt(tlo), vp_pt(thi)
    M = _Msize(vhi, Nc)
    lk = [None] + [lam_iv(lam, k, vlo, vhi) for k in range(1, 2 * M + 2)]
    Lam = [arb(0)]
    for n in range(1, M):
        Lam.append(Lam[-1] + lk[n])
    chi = [1 if n < Nc else 0 for n in range(M)]
    B = [[None] * M for _ in range(M)]
    S1, SM = S_ub(lam, 1, vhi), S_ub(lam, M + 1, vhi)
    th, tail = _theta(S1 + SM, (2 * M + 1) - 2 * SM)
    for n in range(M):
        rho = S_ub(lam, M - n, vhi) + S_ub(lam, M + n + 1, vhi)
        B[n][n] = (2 * n + 1) + 2 * Lam[n] - lk[2 * n + 1] + 2 * u * chi[n] - th * rho
        for m in range(n + 1, M):
            B[n][m] = B[m][n] = -(lk[m - n] + lk[n + m + 1]) + 2 * u * (chi[n] * chi[m])
    kb = chol_cert(B)
    if kb is None or not (kb > 0) or not (tail > 0):
        return None
    return lower_min(kb, tail)


def G_bound(lam, tlo, thi):
    """Certified lower bound on lambda_min(G) on l^2(N_0), valid for all t in [tlo, thi]; None if failed."""
    vlo, vhi = vp_pt(tlo), vp_pt(thi)
    M = _Msize(vhi, 1)
    lk = [None] + [lam_iv(lam, k, vlo, vhi) for k in range(1, 2 * M + 2)]
    Lam = [arb(0)]
    for n in range(1, M):
        Lam.append(Lam[-1] + lk[n])
    B = [[None] * M for _ in range(M)]
    th, tail = _theta(S_ub(lam, 1, vhi), (2 * M + 1) - S_ub(lam, M + 1, vhi))
    for n in range(M):
        B[n][n] = (2 * n + 1) + 2 * Lam[n] - th * S_ub(lam, M - n, vhi)
        for m in range(n + 1, M):
            B[n][m] = B[m][n] = -lk[m - n]
    kb = chol_cert(B)
    if kb is None or not (kb > 0) or not (tail > 0):
        return None
    return lower_min(kb, tail)


def cover(bound, t_from, t_to, h0, kappa, hmin=1e-6):
    """Adaptively cover [t_from, t_to] by intervals on which bound(tlo, thi) >= kappa (arb).
    Returns (list of [tlo, thi, lower bound], ok)."""
    tlo, h, out = t_from, h0, []
    while tlo < t_to:
        thi = min(tlo + h, t_to)
        kb = bound(tlo, thi)
        if kb is None or not (kb >= kappa):
            h /= 2
            if h < hmin:
                return out, False
            continue
        out.append([tlo, thi, float(kb.lower())])
        tlo, h = thi, h * 1.5
    return out, True
