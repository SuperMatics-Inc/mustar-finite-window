"""CERTIFIED (Arb): Theorem C / Corollary D thresholds for a FIXED-FREQUENCY Coulomb cutoff omega_c.

Model: window N_c(T) = #{n >= 0 : (2n+1) pi T < omega_c}  (frequencies in units of the Einstein
frequency Omega = 1).  At every fixed T the model is the fixed-index model with N_c = N_c(T), so the
two-form Theorem C holds verbatim at that T.  Corollary D needs only: for (lam, omega_c, u1) an explicit
T_b > T_G and finite vector v with 2Q_{u1}(v; N_c(T_b)) < 0 at T_b, and G >= 0 (Arb cover) for ALL
T >= T_b.  Then, for every 0 <= u <= u1:  T_tr(u) = T_lin(u) >= T_b > T_G  and the normal state is the
unique global minimiser in A_Z for every T > T_lin(u).  (T_lin is the sup over T, with the window
N_c(T) piecewise constant; no continuity in T of the form is used because T_b itself is a negative
point and Q_u(T) is non-PSD at T_b by exact evaluation at the single window N_c(T_b).)

Outputs certify_fixed_omega.json  (max certified u1 per (lam, omega_c) on the 1/20 grid, cap UCAP).
Usage: certify_fixed_omega.py [lam ...]   (default 1 2 4 8)
"""
import json, sys, time
import numpy as np
from flint import arb, ctx
from arbcert import vp_pt, lam_pt, G_bound, cover
from certify_physical import Qu_of_vector
from gapmap import Tsup, Nfor
from fc import Chain

ctx.prec = 128
UCAP = 2.0
WCS = (3, 5, 10, 20)


def window_count(wc, T, strict=True):
    """Exact N_c(T) = #{n>=0 : (2n+1) pi T < wc}, with a guard against breakpoints."""
    x = arb(wc) / (arb.pi() * arb(T))
    y = (x - 1) / 2
    m = float(y.mid())
    if m <= 0:
        return 0
    c = int(np.ceil(m))
    assert (not strict) or abs(m - round(m)) > 1e-9, "T_b too close to a window breakpoint"
    return c


def ev_w(lam, T, wc, u):
    Nc = window_count(wc, T, strict=False)
    return np.linalg.eigvalsh(Chain(lam, T, Nfor(T, max(Nc, 1)), Nc, u).Heven())[0]


def TG_cert(lamf, Tstart):
    """G cover from t=0 to 1/Tstart -> list, ok."""
    lam = arb(lamf)
    return cover(lambda a, b: G_bound(lam, a, b), 0.0, 1.0 / Tstart, 0.25, arb(0))


def cell(lamf, wc, k, TG, covG_cache):
    """Try to certify (lam, wc, exact u1=k/20). Returns record or None."""
    u1 = k / 20  # floating point is used only to propose the temperature and vector
    Tl, _ = Tsup(lambda T: ev_w(lamf, T, wc, u1), lo=5e-3, hi=3.0, n=120)
    if Tl <= 1.02 * TG:
        return dict(ok=False, why="T_lin<=1.02 T_G", Tlin=float(Tl))
    Tb = float(np.float64(0.99 * Tl))
    Nc = window_count(wc, Tb)
    N = Nfor(Tb, max(Nc, 1))
    w, V = np.linalg.eigh(Chain(lamf, Tb, N, Nc, u1).Heven())
    v = V[:, 0] / np.max(np.abs(V[:, 0]))
    qv = Qu_of_vector(arb(lamf), Nc, arb(k) / 20, 1 / arb(Tb), v)
    okC = bool(qv < 0)
    return dict(ok=okC, Tlin_num=float(Tl), Tb=Tb, Nc_Tb=Nc, N_v=N, twoQu_v_Tb=[float(qv.lower()), float(qv.upper())],
                okC=okC, TG_num=TG)


if __name__ == "__main__":
    lams = [float(a) for a in sys.argv[1:]] or [1.0, 2.0, 4.0, 8.0]
    TGnum = {1.0: 0.01984, 2.0: 0.06928, 4.0: 0.14853, 8.0: 0.25011}
    res = {}
    t0 = time.time()
    for lamf in lams:
        TG = TGnum[lamf]
        recs = {}
        Tb_min = None
        for wc in WCS:
            best = None
            # numerical bisection on the 1/20 grid: largest k with T_lin^omega(k/20) > 1.02 T_G (monotone in u)
            lo, hi = 1, int(UCAP * 20)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                Tl, _ = Tsup(lambda T: ev_w(lamf, T, wc, mid / 20), lo=5e-3, hi=3.0, n=120)
                if Tl > 1.02 * TG:
                    lo = mid
                else:
                    hi = mid - 1
            for k in range(lo, 1, -1):  # certify from the numerical maximum downwards
                r = cell(lamf, wc, k, TG, None)
                if r["ok"]:
                    best = dict(u1=f"{k}/20", **r)
                    break
            recs[str(wc)] = best
            if best and (Tb_min is None or best["Tb"] < Tb_min):
                Tb_min = best["Tb"]
            print(f"lam={lamf:g} wc={wc}: {best}", flush=True)
        # one G cover per lambda down to the smallest T_b used
        covG, okG = TG_cert(lamf, Tb_min)
        print(f"lam={lamf:g}: G cover to T_b,min={Tb_min:.5f}: ok={okG}, n={len(covG)}, min={min(c[2] for c in covG)}", flush=True)
        res[f"{lamf:g}"] = dict(cells=recs, okG=okG, nG=len(covG), minG=str(min(c[2] for c in covG)),
                                 t_cover_to=1 / Tb_min)
        for wc in WCS:
            if recs[str(wc)]:
                recs[str(wc)]["ok"] = recs[str(wc)]["ok"] and okG
    res["seconds"] = time.time() - t0
    json.dump(res, open("certify_fixed_omega.json", "w"), indent=1)
    allok = all(c is not None and c["ok"] for k, v in res.items() if k != "seconds" for c in v["cells"].values())
    print("ALL CERTIFIED" if allok else "SOME CELLS MISSING")
    sys.exit(0 if allok else 1)
