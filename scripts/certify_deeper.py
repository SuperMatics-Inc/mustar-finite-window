"""CERTIFIED (Arb ball arithmetic, 128-bit): deeper unrestricted-spin configurations than the witness.

The supplied witness (cx_config.json, N=40) has E_{1/40} = -13.0703815796. The supplied
N=64 configurations were found by floating optimization (NUMERICAL); this script certifies, by direct
full-chain Arb evaluation (exterior frozen at the normal state, independent of every identity), that

    E_{T}(S) < 0           for each stored configuration at T = 1/40, 1/38, 1/37    (lam=8, Nc=5, u=20),
    E_{1/40}(S_deeper) < E_{1/40}(S_witness) - 1  (the witness is NOT the global minimiser at T1).

Exterior weight (telescoping, no Lemma Dsum needed):  sum_{m>=N} (K_{m-n} - K_{n+m+1}) = sum_{j=N-n}^{N+n} K_j.
Exit 0 iff all checks hold.  Nothing here is a statement about a physical free energy."""
import json, sys, time
from flint import arb
from arbcert import vp_pt, lam_pt

LAM, NC, U = arb(8), 5, arb(20)
WITNESS_LOWER = arb("-13.0703815797")   # certified lower bound on the witness energy (certify_cx.json E_T1)


def energy(cfg, t):
    vp = vp_pt(t)
    N, z = cfg["N"], [arb(x) for x in cfg["z"]]
    ta, pa, tb, pb = z[:N], z[N:2 * N], z[2 * N:3 * N], z[3 * N:]
    xi = [(ta[n].sin() * pa[n].cos(), ta[n].sin() * pa[n].sin(), ta[n].cos()) for n in range(N)]
    et = [(tb[n].sin() * pb[n].cos(), tb[n].sin() * pb[n].sin(), tb[n].cos()) for n in range(N)]
    lk = [None] + [lam_pt(LAM, k, vp) for k in range(1, 2 * N + 2)]
    E = arb(0)
    for n in range(N):
        tn = sum((lk[j] for j in range(N - n, N + n + 1)), arb(0))
        E += ((2 * n + 1) + tn) * (2 - xi[n][2] - et[n][2])
        for m in range(n + 1, N):
            dxx = xi[n][0] * xi[m][0] + xi[n][1] * xi[m][1] + xi[n][2] * xi[m][2]
            dee = et[n][0] * et[m][0] + et[n][1] * et[m][1] + et[n][2] * et[m][2]
            E += lk[m - n] * ((1 - dxx) + (1 - dee))
        for m in range(N):
            dxe = xi[n][0] * et[m][0] + xi[n][1] * et[m][1] - xi[n][2] * et[m][2]
            E -= lk[n + m + 1] * (1 + dxe)
    X = sum((xi[n][0] + et[n][0] for n in range(NC)), arb(0))
    Y = sum((xi[n][1] + et[n][1] for n in range(NC)), arb(0))
    return E + U / 2 * (X ** 2 + Y ** 2)


if __name__ == "__main__":
    t0 = time.time()
    out, ok = {}, True
    for fn, t in (("deeper_cfg_t40.json", 40), ("deeper_cfg_t38.json", 38), ("deeper_cfg_t37.json", 37)):
        cfg = json.load(open(fn))
        E = energy(cfg, arb(t))
        neg = bool(E < 0)
        rec = dict(t=t, T=1.0 / t, N=cfg["N"], E_float=cfg["E_float"], E=[float(E.lower()), float(E.upper())], negative=neg)
        if t == 40:
            below = bool(E < WITNESS_LOWER - 1)
            rec["below_witness_by_more_than_1"] = below
            neg = neg and below
        out[fn] = rec
        ok = ok and neg
        print("%-22s t=%2d N=%d  E in [%.12f, %.12f]  float %.12f  certified %s" % (
            fn, t, cfg["N"], rec["E"][0], rec["E"][1], cfg["E_float"], neg), flush=True)
    out["ok"] = ok
    out["seconds"] = time.time() - t0
    json.dump(out, open("certify_deeper.json", "w"), indent=1)
    print("ALL CERTIFIED" if ok else "FAILED", "(%.1fs)" % out["seconds"])
    sys.exit(0 if ok else 1)
