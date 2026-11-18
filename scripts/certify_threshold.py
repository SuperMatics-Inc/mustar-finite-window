"""CERTIFIED explicit mu* threshold (route (a), Theorem D) on a (lam, Nc) grid.
Definitions: T_lin(mu) = sup{T : Q_mu(T) is not PSD on l^2(N_0)}, T_G = sup{T : G(T) is not PSD}.
Theorem D (PROVED, report): if G(T) is PSD for every T >= T_b and Q_{mu1}(T_b) has a negative direction, then for
EVERY mu* in [0, mu1]: T_lin(mu*) > T_b (openness and monotonicity in mu), and the normal state is the unique
global minimiser for all T > T_lin(mu*). Negative directions occur arbitrarily close below that supremum;
no whole left neighbourhood, single instability interval, or endpoint continuity is asserted.
Certified per cell: (i) 2Q_{mu1}(v) < 0 at a numerically proposed temperature T_b;
(ii) G > 0 for all T >= T_b. Numerical root finding only proposes inputs; Arb supplies the proof."""
import json, sys, time
from multiprocessing import Pool
import numpy as np
from flint import arb
from arbcert import G_bound, cover
from certify_physical import Qu_of_vector
from gapmap import Tsup, ev_even, Nfor
from fc import Chain

# Sufficient rational endpoints selected by an exploratory numerical crossing surrogate, not optimal thresholds.
GRID = {1.0: {1: (1, 1), 2: (1, 1), 5: (11, 20), 10: (2, 5), 20: (7, 20)},
        2.0: {1: (1, 1), 2: (9, 10), 5: (11, 20), 10: (3, 5), 20: (1, 1)},
        4.0: {1: (1, 1), 2: (17, 20), 5: (7, 10), 10: (1, 1), 20: (1, 1)},
        8.0: {1: (1, 1), 2: (17, 20), 5: (17, 20), 10: (1, 1), 20: (1, 1)}}


def job(lamf):
    t0 = time.time()
    lam = arb(lamf)
    rows = []
    for Nc, (p, q) in GRID[lamf].items():
        Tl = Tsup(lambda T: ev_even(lamf, T, Nc, p / q))[0]
        Tb = 0.99 * Tl
        tb = 1 / Tb
        N = Nfor(Tb, Nc)
        w, V = np.linalg.eigh(Chain(lamf, Tb, N, Nc, p / q).Heven())
        v = V[:, 0] / np.max(np.abs(V[:, 0]))
        qv = Qu_of_vector(lam, Nc, arb(p) / q, tb, v)
        rows.append(dict(lam=lamf, Nc=Nc, mu1=f"{p}/{q}", Tlin_mu1=Tl, Tb=Tb, tb=tb,
                         twoQ_v=float(qv.upper()), okQ=bool(qv < 0)))
    tmax = max(r["tb"] for r in rows)
    covG, okG = cover(lambda a, b: G_bound(lam, a, b), 0.0, tmax, 0.25, arb(0))
    reached = covG[-1][1] if covG else 0.0
    for r in rows:
        r["okG"] = bool(okG or reached >= r["tb"])
        r["minG"] = min(c[2] for c in covG if c[0] < r["tb"])
        r["ok"] = r["okQ"] and r["okG"]
    return dict(lam=lamf, tmax=tmax, G_reached=reached, nG=len(covG), rows=rows, seconds=time.time() - t0)


if __name__ == "__main__":
    with Pool(4) as pool:
        res = pool.map(job, list(GRID))
    json.dump(res, open("certify_threshold.json", "w"), indent=1)
    allok = True
    for r in res:
        print("lam=%g  G cover to t=%.4f (%d intervals, %.0fs)" % (r["lam"], r["G_reached"], r["nG"], r["seconds"]))
        for x in r["rows"]:
            allok &= x["ok"]
            print("   Nc=%2d mu1=%-6s T_lin(mu1)=%.6f T_b=%.6f 2Q(v)<=%.3e minG=%.3e ok=%s"
                  % (x["Nc"], x["mu1"], x["Tlin_mu1"], x["Tb"], x["twoQ_v"], x["minG"], x["ok"]))
    print("ALL CERTIFIED" if allok else "NOT ALL CERTIFIED")
    sys.exit(0 if allok else 1)
