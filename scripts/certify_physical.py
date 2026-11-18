"""CERTIFIED (Arb) spin-model brackets, not physical/material validation:
for (lam, Nc, mu*) given, with T_c = numerical block threshold of Q_u, T_a = (1+eps) T_c, T_b = (1-eps) T_c:
 (A) 2Q_u(T) > 0 on l^2(N_0) for ALL T >= T_a  (t = 1/T in [0, 1/T_a] covered by Arb intervals);
 (B) G(T) > 0 on l^2(N_0) for ALL T >= T_a;
     => Theorem C: the normal state is the unique global minimiser of the full (non-TRS, 3D) chain
        for every T >= T_a;
 (C) 2Q_u(v) < 0 at T_b for an explicit finitely supported v (exact finite sum)
     => the normal state is not a local minimiser at T_b (TRS tilt theta = eps v).
Hence the last global spin threshold lies in [T_b, T_a], around a numerical block proposal,
not an interval-certified linear critical temperature. Usage: certify_physical.py lam Nc p q [eps]."""
import json, sys, time
import numpy as np
from flint import arb
from arbcert import vp_pt, lam_pt, Qu_bound, G_bound, cover
from gapmap import Tsup, ev_even, Nfor
from fc import Chain


def Qu_of_vector(lam, Nc, u, t, v):
    """Exact 2Q_u(v) on the infinite chain for v supported on [0, len(v))."""
    vp = vp_pt(t)
    N = len(v)
    va = [arb(x) for x in v]
    lk = [None] + [lam_pt(lam, k, vp) for k in range(1, 2 * N + 2)]
    Lam = [arb(0)]
    for n in range(1, N):
        Lam.append(Lam[-1] + lk[n])
    s = arb(0)
    for n in range(N):
        s += ((2 * n + 1) + 2 * Lam[n] - lk[2 * n + 1]) * va[n] ** 2
        for m in range(n + 1, N):
            s -= 2 * (lk[m - n] + lk[n + m + 1]) * va[n] * va[m]
    win = sum((va[n] for n in range(min(Nc, N))), arb(0))
    return s + 2 * u * win ** 2


if __name__ == "__main__":
    lamf, Nc, p, q = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    eps = float(sys.argv[5]) if len(sys.argv) > 5 else 0.01
    t0 = time.time()
    lam, u = arb(lamf), arb(p) / q
    Tc = Tsup(lambda T: ev_even(lamf, T, Nc, p / q))[0]
    Ta, Tb = Tc * (1 + eps), Tc * (1 - eps)
    ta, tb = 1 / Ta, 1 / Tb
    covQ, okQ = cover(lambda a, b: Qu_bound(lam, Nc, u, a, b), 0.0, ta, 0.25, arb(0))
    covG, okG = cover(lambda a, b: G_bound(lam, a, b), 0.0, ta, 0.25, arb(0))
    N = Nfor(Tb, Nc)
    w, V = np.linalg.eigh(Chain(lamf, Tb, N, Nc, p / q).Heven())
    v = V[:, 0] / np.max(np.abs(V[:, 0]))
    qv = Qu_of_vector(lam, Nc, u, tb, v)
    okC = bool(qv < 0)
    ok = okQ and okG and okC
    rec = dict(lam=lamf, Nc=Nc, mu=f"{p}/{q}", Tc_block=Tc, Ta=Ta, Tb=Tb, ta=ta, tb=tb,
               nQ=len(covQ), okQ=okQ, minQ=min(c[2] for c in covQ) if covQ else None,
               nG=len(covG), okG=okG, minG=min(c[2] for c in covG) if covG else None,
               twoQu_v_Tb=[float(qv.lower()), float(qv.upper())], okC=okC, ok=ok, seconds=time.time() - t0)
    print(json.dumps(rec))
    json.dump(rec, open(f"certify_physical_{lamf:g}_{Nc}_{p}_{q}.json", "w"), indent=1)
    sys.exit(0 if ok else 1)
