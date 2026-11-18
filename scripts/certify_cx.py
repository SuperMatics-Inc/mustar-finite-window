"""Use Arb bounds to prove a discontinuity in the l2 norm for the unrestricted spin model.
The Coulomb XY term uses a fixed window on both indices.
Einstein Omega=1, lam=8, Nc=5 (j=-5..4), u=20 (unphysical). Exit 0 only if all steps hold:
 (1) E_{T1}(S) < 0 at T1 = 1/40 for the explicit finitely supported configuration in cx_config.json
     (direct full-chain sum, exterior frozen normal; independent of the identities).
 (2) 2Q_u(T) >= 1/2 on l^2(N_0) for every T in [T1, T2], T2 = 4/13 (t = 1/T in [13/4, 40] covered by
     intervals; arbcert.Qu_bound is valid for all t in each interval).
 (3) G(T) > 0 and 2Q_u(T) > 0 on l^2(N_0) for every T >= T2 (t in [0, 13/4] covered), so Theorem C applies:
     the normal state is the unique global minimiser for all T >= T2.
Also prints Lambda_inf <= S(1) at T1 and the separation radius delta0 = min(sqrt 2, sqrt(kappa'/(2 Lambda_inf)))."""
import json, sys, time
import numpy as np
from flint import arb
from arbcert import vp_pt, lam_pt, S_ub, Qu_bound, G_bound, cover

cfg = json.load(open("cx_config.json"))
LAM, NC, U = arb(cfg["lam"]), cfg["Nc"], arb(cfg["u"])


def energy(t):
    """Direct full-chain energy: xi_n = S_n, ups_n = M S_{-n-1} (M = z-mirror), n < N; exterior normal.
    E = sum_n wt_n (2 - xi^z_n - ups^z_n) + sum_{n<m} lam(m-n) [(1 - xi_n.xi_m) + (1 - ups_n.ups_m)]
        - sum_{n,m} lam(n+m+1) (1 + xi_n . M ups_m) + (u/2) |sum_{n<Nc} (xi^perp_n + ups^perp_n)|^2,
    wt_n = (2n+1) + t_n,  t_n = sum_{m>=N} D_nm = 2 Lam_n + lam(2n+1) - sum_{m<N, m!=n} D_nm (Lemma Dsum)."""
    vp = vp_pt(t)
    N, z = cfg["N"], [arb(x) for x in cfg["z"]]
    ta, pa, tb, pb = z[:N], z[N:2 * N], z[2 * N:3 * N], z[3 * N:]
    xi = [(ta[n].sin() * pa[n].cos(), ta[n].sin() * pa[n].sin(), ta[n].cos()) for n in range(N)]
    up = [(tb[n].sin() * pb[n].cos(), tb[n].sin() * pb[n].sin(), tb[n].cos()) for n in range(N)]
    lk = [None] + [lam_pt(LAM, k, vp) for k in range(1, 2 * N + 2)]
    Lam = [arb(0)]
    for n in range(1, N):
        Lam.append(Lam[-1] + lk[n])
    E = arb(0)
    for n in range(N):
        tn = 2 * Lam[n] + lk[2 * n + 1] - sum((lk[abs(n - m)] - lk[n + m + 1] for m in range(N) if m != n), arb(0))
        E += ((2 * n + 1) + tn) * (2 - xi[n][2] - up[n][2])
        for m in range(n + 1, N):
            dxx = xi[n][0] * xi[m][0] + xi[n][1] * xi[m][1] + xi[n][2] * xi[m][2]
            duu = up[n][0] * up[m][0] + up[n][1] * up[m][1] + up[n][2] * up[m][2]
            E += lk[m - n] * ((1 - dxx) + (1 - duu))
        for m in range(N):
            dxu = xi[n][0] * up[m][0] + xi[n][1] * up[m][1] - xi[n][2] * up[m][2]  # xi_n . M ups_m
            E -= lk[n + m + 1] * (1 + dxu)
    X = sum((xi[n][0] + up[n][0] for n in range(NC)), arb(0))
    Y = sum((xi[n][1] + up[n][1] for n in range(NC)), arb(0))
    return E + U / 2 * (X ** 2 + Y ** 2)


if __name__ == "__main__":
    t0 = time.time()
    out = {}
    t1 = float(cfg["T"][1]) / float(cfg["T"][0])  # 1/T1 = 40
    t2 = 3.25                                      # 1/T2 = 13/4
    E = energy(t1)
    okE = bool(E < 0)
    out["E_T1"] = [float(E.lower()), float(E.upper())]
    print("(1) E(S) at T1=1/40:", E.str(12), " (float identity value", cfg["E_float"], ") certified < 0:", okE)
    covG, okG = cover(lambda a, b: G_bound(LAM, a, b), 0.0, t2, 0.25, arb(0))
    covH, okH = cover(lambda a, b: Qu_bound(LAM, NC, U, a, b), 0.0, t2, 0.25, arb(0))
    okG = okG and okH
    out["minG_T>=T2"] = min(c[2] for c in covG) if covG else None
    out["minQu_T>=T2"] = min(c[2] for c in covH) if covH else None
    print("(3) T >= T2=4/13: min lambda_min G >=", out["minG_T>=T2"], "(%d int.)," % len(covG),
          " min lambda_min 2Q_u >=", out["minQu_T>=T2"], "(%d int.)" % len(covH), " certified > 0:", okG)
    KAPPA = arb(0.5)
    cov, okQ = cover(lambda a, b: Qu_bound(LAM, NC, U, a, b), t2, t1, 0.05, KAPPA)
    out["cover"] = cov
    out["kappa_min"] = min(c[2] for c in cov) if cov else None
    print("(2) Q_u cover of t in [13/4, 40]:", len(cov), "intervals, complete:", okQ, " min certified lambda_min(2Q_u):", out["kappa_min"])
    Linf = S_ub(LAM, 1, vp_pt(t1))  # Lambda_inf is increasing in vp, so its maximum on [T1, T2] is at T1
    out["Lambda_inf_ub"] = float(Linf.upper())
    if okQ:
        out["delta0"] = min(np.sqrt(2), np.sqrt(0.5 / (2 * float(Linf.upper())) * (1 - 1e-12)))
        print("Lambda_inf <=", out["Lambda_inf_ub"], " separation radius delta0 >=", out["delta0"])
    ok = okE and okG and okQ
    out["ok"] = ok
    out["seconds"] = time.time() - t0
    json.dump(out, open("certify_cx.json", "w"), indent=1)
    print("Discontinuity certified" if ok else "Discontinuity not certified", " %.1fs" % (time.time() - t0))
    sys.exit(0 if ok else 1)
