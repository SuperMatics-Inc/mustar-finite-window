"""Independent re-verification of every MuStar certificate (mpmath.iv + numpy/LAPACK; no Arb, no shared code).

Run:  uv run --no-project --with numpy --with mpmath python verify_independent.py [--quick]
Exit code 0 iff every positive check passes AND every mutant is rejected.
Output: logs/rigor/verify_independent.log  and  logs/rigor/verify_independent.json
"""
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

import numpy as np
import mpmath as mp
from mpmath import iv

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import indep as ix  # noqa: E402

ROOT = os.path.dirname(HERE)
LOGDIR = os.path.join(ROOT, "logs", "rigor")


def J(name):
    with open(os.path.join(HERE, name)) as f:
        return json.load(f)


def ivfrac(fr):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def dnfrac(fr):
    return ix.dn(ivfrac(fr).a)


# ------------------------------------------------------------------------------------------- task workers
def task_point(d):
    """2Q_u(v) < 0 at T=Tb with v the lowest eigenvector of a float matrix built here."""
    lam, Nc, u, Tb = d["lam"], d["Nc"], d["u"], d["Tb"]
    uf = Fraction(u)
    N = d.get("N") or ix.Nfor(Tb, max(Nc, 1))
    A = ix.build_qu_float(lam, Nc, float(uf), Tb, N)
    v, w0 = ix.lowest_vector(A)
    if d.get("mutate") == "random":
        v = np.random.default_rng(d.get("seed", 0)).uniform(-1, 1, N)
    elif d.get("mutate") == "noise":
        v = v * (1 + 0.5 * np.random.default_rng(d.get("seed", 0)).standard_normal(N))
    elif d.get("mutate") == "signflip":
        v = v.copy()
        v[0] = -v[0]
    t = 1.0 / Tb
    q = ix.qu_point(lam, d.get("Nc_eval", Nc), ivfrac(uf), t, v)
    return dict(kind="point", tag=d["tag"], lo=float(q.a), hi=float(q.b), neg=bool(q.b < 0), N=N,
                eig_float=float(w0), scaled_float=float(w0 * np.dot(v, v)), stored=d.get("stored"))


def task_cover(d):
    lam, Nc, u = d["lam"], d.get("Nc"), d.get("u")
    form = d["form"]
    t0, t1, kap = d["t0"], d["t1"], d.get("kappa", 0.0)
    if form == "G":
        f = lambda a, b: ix.g_lb(lam, a, b, d.get("M"))
    else:
        uu = dnfrac(Fraction(u))
        f = lambda a, b: ix.qu_lb(lam, Nc, uu, a, b, d.get("M"))
    s0 = time.time()
    segs, ok, mn = ix.cover(f, t0, t1, d.get("h0", 0.25), kap)
    return dict(kind="cover", tag=d["tag"], form=form, ok=bool(ok), n=len(segs), minlb=(mn if segs else None),
                reached=(segs[-1][1] if segs else t0), seconds=time.time() - s0, stored=d.get("stored"))


def task_energy(d):
    t = d["t"]
    E1 = ix.energy_direct(d["lam"], d["Nc"], d["u"], t, d["z"], d["N"])
    out = dict(kind="energy", tag=d["tag"], E_direct=mp.nstr(E1, 30))
    Ei = ix.energy_direct(d["lam"], d["Nc"], d["u"], t, d["z"], d["N"], interval=True)
    out["interval_lo"], out["interval_hi"] = str(mp.mpf(Ei.a)), str(mp.mpf(Ei.b))
    if d.get("i2", True):
        E2 = ix.energy_I2(d["lam"], d["Nc"], d["u"], t, d["z"], d["N"])
        out["E_I2"] = mp.nstr(E2, 30)
        out["I2_minus_direct"] = mp.nstr(E2 - E1, 5)
    return out


def run_task(d):
    return dict(point=task_point, cover=task_cover, energy=task_energy)[d["kind"]](d)


# ------------------------------------------------------------------------------------------- main
def main():
    quick = "--quick" in sys.argv
    os.makedirs(LOGDIR, exist_ok=True)
    log = open(os.path.join(LOGDIR, "verify_independent.log"), "w")

    def P(*a):
        s = " ".join(str(x) for x in a)
        print(s, flush=True)
        log.write(s + "\n")
        log.flush()

    t00 = time.time()
    P("verify_independent.py  (mpmath", mp.__version__, " numpy", np.__version__, ")  quick=%s" % quick)
    thr, cx, ph, fo = J("certify_threshold.json"), J("cx_config.json"), [], J("certify_fixed_omega.json")
    for f in ("1_5_13_100", "2_5_13_100", "4_10_1_5", "8_5_13_100"):
        ph.append(J("certify_physical_%s.json" % f))
    LAM, NC, U = 8.0, 5, "20"
    tasks = []
    exp_ok = {}  # tag -> expected outcome predicate name

    # (1) fixed-index threshold grid: point checks + G covers
    for blk in thr:
        lam = blk["lam"]
        tbmax = max(r["tb"] for r in blk["rows"])
        for r in blk["rows"]:
            tag = "thr/lam%g/Nc%d/u1=%s" % (lam, r["Nc"], r["mu1"])
            tasks.append(dict(kind="point", tag=tag, lam=lam, Nc=r["Nc"], u=r["mu1"], Tb=r["Tb"], stored=r["twoQ_v"]))
            exp_ok[tag] = "neg"
        tag = "thr/lam%g/G-cover[0,%.4f]" % (lam, tbmax)
        tasks.append(dict(kind="cover", tag=tag, form="G", lam=lam, t0=0.0, t1=float(np.nextafter(tbmax, np.inf)),
                          stored=dict(tmax=blk["tmax"], nG=blk["nG"])))
        exp_ok[tag] = "cover"
    # (2) physical cases
    for r in ph:
        lam, Nc = r["lam"], r["Nc"]
        tag = "phys/lam%g/Nc%d/mu=%s" % (lam, Nc, r["mu"])
        tasks.append(dict(kind="point", tag=tag + "/point", lam=lam, Nc=Nc, u=r["mu"], Tb=r["Tb"], stored=r["twoQu_v_Tb"]))
        exp_ok[tag + "/point"] = "neg"
        t1 = float(np.nextafter(1.0 / r["Ta"], np.inf))
        tasks.append(dict(kind="cover", tag=tag + "/Qu-cover", form="Qu", lam=lam, Nc=Nc, u=r["mu"], t0=0.0, t1=t1,
                          stored=dict(minQ=r["minQ"], nQ=r["nQ"])))
        tasks.append(dict(kind="cover", tag=tag + "/G-cover", form="G", lam=lam, t0=0.0, t1=t1,
                          stored=dict(minG=r["minG"], nG=r["nG"])))
        exp_ok[tag + "/Qu-cover"] = exp_ok[tag + "/G-cover"] = "cover"
    # (3) fixed-omega_c cells + G covers
    for lamk, blk in fo.items():
        if not isinstance(blk, dict) or "cells" not in blk:
            continue
        lam = float(lamk)
        for wc, c in blk["cells"].items():
            if not c:
                continue
            Tb = c["Tb"]
            x = mp.mpf(int(wc)) / (mp.pi * mp.mpf(Tb))
            Nc = int(mp.ceil((x - 1) / 2))
            tag = "fixw/lam%g/wc%s/u1=%s" % (lam, wc, c["u1"])
            tasks.append(dict(kind="point", tag=tag, lam=lam, Nc=Nc, u=str(Fraction(c["u1"])), Tb=Tb,
                              stored=c["twoQu_v_Tb"], Nc_stored=c["Nc_Tb"]))
            exp_ok[tag] = "neg"
        tag = "fixw/lam%g/G-cover[0,%.4f]" % (lam, blk["t_cover_to"])
        tasks.append(dict(kind="cover", tag=tag, form="G", lam=lam, t0=0.0, t1=float(np.nextafter(blk["t_cover_to"], np.inf)),
                          stored=dict(minG=blk["minG"], nG=blk["nG"])))
        exp_ok[tag] = "cover"
    # (4) witness (lam=8, Nc=5, u=20, T1=1/40, T2=4/13)
    z = cx["z"]
    tasks.append(dict(kind="energy", tag="witness/E(T=1/40)", lam=LAM, Nc=NC, u=20, t=40, z=z, N=cx["N"]))
    for wc in (5, 10):
        ncut = int(mp.ceil((mp.mpf(wc) * 40 / mp.pi - 1) / 2))
        tasks.append(dict(kind="energy", tag="scope/wc=%d" % wc, lam=LAM, Nc=ncut, u=20, t=40, z=z, N=cx["N"]))
    tasks.append(dict(kind="cover", tag="witness/Qu>=0.5 on t in [3.25,40]", form="Qu", lam=LAM, Nc=NC, u="20", t0=3.25, t1=40.0,
                      kappa=0.5, h0=0.05, stored=dict(minQu_cover="0.5018")))
    tasks.append(dict(kind="cover", tag="witness/Qu>0 on t in [0,3.25]", form="Qu", lam=LAM, Nc=NC, u="20", t0=0.0, t1=3.25))
    tasks.append(dict(kind="cover", tag="witness/G>0 on t in [0,3.25]", form="G", lam=LAM, t0=0.0, t1=3.25))
    for tg in ("witness/Qu>=0.5 on t in [3.25,40]", "witness/Qu>0 on t in [0,3.25]", "witness/G>0 on t in [0,3.25]"):
        exp_ok[tg] = "cover"
    # (5) deeper configurations found by the independent search
    for fn in sorted(os.listdir(HERE)):
        if fn.startswith("deeper_cfg_") and fn.endswith(".json"):
            dc = J(fn)
            t = dc.get("t", dc["T"][1] / dc["T"][0])
            tasks.append(dict(kind="energy", tag="deeper/%s/E(t=%g)" % (fn, t), lam=8.0, Nc=5, u=20, t=t, z=dc["z"], N=dc["N"],
                              float_E=dc["E_float"]))
    # (6) mutants (each MUST be rejected: cover not ok / point not negative / energy mismatch)
    mut = []

    def addm(tag, d, pred):
        d = dict(d, tag="MUTANT/" + tag)
        mut.append((d["tag"], pred))
        tasks.append(d)

    addm("G cover lam=1 up to 0.90*T_G", dict(kind="cover", form="G", lam=1.0, t0=0.0, t1=1 / (0.9 * 0.01984)), "cover_fails")
    addm("G cover lam=8 up to 0.90*T_G", dict(kind="cover", form="G", lam=8.0, t0=0.0, t1=1 / (0.9 * 0.25011)), "cover_fails")
    addm("G cover lam=2 up to 0.97*T_G", dict(kind="cover", form="G", lam=2.0, t0=0.0, t1=1 / (0.97 * 0.06928)), "cover_fails")
    addm("Qu cover witness down to T=0.0200 (< T_lin=0.02031)", dict(kind="cover", form="Qu", lam=LAM, Nc=NC, u="20", t0=0.0, t1=50.0), "cover_fails")
    addm("Qu cover phys1 to 0.98*T_c", dict(kind="cover", form="Qu", lam=1.0, Nc=5, u="13/100", t0=0.0, t1=1 / (0.98 * 0.07210907246663323)), "cover_fails")
    addm("Qu cover phys2 to 0.98*T_c", dict(kind="cover", form="Qu", lam=2.0, Nc=5, u="13/100", t0=0.0, t1=1 / (0.98 * 0.16268701083616172)), "cover_fails")
    addm("Qu cover phys4 to 0.98*T_c", dict(kind="cover", form="Qu", lam=4.0, Nc=10, u="1/5", t0=0.0, t1=1 / (0.98 * 0.25473840709166085)), "cover_fails")
    addm("Qu cover phys8 to 0.98*T_c", dict(kind="cover", form="Qu", lam=8.0, Nc=5, u="13/100", t0=0.0, t1=1 / (0.98 * 0.4142814123859763)), "cover_fails")
    addm("tail with M=Nc+1 at t in [39,40] (witness Qu)", dict(kind="cover", form="Qu", lam=LAM, Nc=NC, u="20", t0=39.0, t1=40.0, M=NC + 1, h0=0.5, kappa=0.5), "cover_fails")
    addm("tail with M=3 for G lam=1 at t in [30,31]", dict(kind="cover", form="G", lam=1.0, t0=30.0, t1=31.0, M=3, h0=0.5), "cover_fails")
    addm("G cover with lam*1.2 at lam=1 up to 1/T_b", dict(kind="cover", form="G", lam=1.2, t0=0.0, t1=1 / 0.02028791986668813), "cover_fails")
    addm("point: phys2 vector evaluated at 1.05*Tb", dict(kind="point", lam=2.0, Nc=5, u="13/100", Tb=1.05 * ph[1]["Tb"] * 1.0, N=None), "point_nonneg")
    addm("point: random vector, phys2 at Tb", dict(kind="point", lam=2.0, Nc=5, u="13/100", Tb=ph[1]["Tb"], mutate="random", seed=1), "point_nonneg")
    addm("point: random vector, fixed-index lam=1 Nc=5", dict(kind="point", lam=1.0, Nc=5, u="11/20", Tb=0.03, mutate="random", seed=2), "point_nonneg")
    addm("point: u=20 instead of 0.13 (phys1 Tb; T_lin is nonincreasing in u)", dict(kind="point", lam=1.0, Nc=5, u="20", Tb=ph[0]["Tb"]), "point_nonneg")
    addm("point: lam=0.5 instead of 1 (phys1 Tb; weaker coupling lowers T_lin)", dict(kind="point", lam=0.5, Nc=5, u="13/100", Tb=ph[0]["Tb"]), "point_nonneg")
    addm("point: T above T_lin for witness (T=0.0210)", dict(kind="point", lam=LAM, Nc=NC, u="20", Tb=0.0210), "point_nonneg")
    addm("energy: witness with 0.5-rad noise", dict(kind="energy", lam=LAM, Nc=NC, u=20, t=40, z=list(np.array(z) + 0.5 * np.random.default_rng(3).standard_normal(len(z))), N=cx["N"], i2=False), "energy_not_below")
    addm("energy: witness at wrong T (t=8)", dict(kind="energy", lam=LAM, Nc=NC, u=20, t=8, z=z, N=cx["N"], i2=False), "energy_not_below")
    addm("energy: witness with u=200 (Coulomb term only adds energy)", dict(kind="energy", lam=LAM, Nc=NC, u=200, t=40, z=z, N=cx["N"], i2=False), "energy_not_below")
    addm("energy: witness with lam=2", dict(kind="energy", lam=2.0, Nc=NC, u=20, t=40, z=z, N=cx["N"], i2=False), "energy_not_below")
    tasks = [d for d in tasks]
    if quick:
        tasks = [d for d in tasks if d["tag"].startswith("MUTANT") or d["tag"].startswith("witness") or d["tag"].startswith("phys")]
    P("tasks:", len(tasks), "(mutants %d)" % len(mut))
    results = {}
    with ProcessPoolExecutor(max_workers=4) as ex:
        for r in ex.map(run_task, tasks, chunksize=1):
            results[r["tag"]] = r
    P("all tasks done in %.0f s" % (time.time() - t00))

    nfail = 0

    def verdict(cond, line):
        nonlocal nfail
        P(("PASS  " if cond else "FAIL  ") + line)
        if not cond:
            nfail += 1

    P("\n== positive checks ==")
    for tag, kind in exp_ok.items():
        if tag not in results:
            continue
        r = results[tag]
        if kind == "neg":
            st = r["stored"]
            sv = (st[0] if isinstance(st, list) else st)
            verdict(r["neg"], "%-52s 2Q_u(v) in [%.6e, %.6e] (mpmath.iv) <0 ; Arb stored %.6e ; |diff|=%.2e ; N=%d"
                    % (tag, r["lo"], r["hi"], sv, abs(r["hi"] - sv), r["N"]))
        else:
            sto = r["stored"] or {}
            verdict(r["ok"], "%-52s cover ok=%s  n=%d  min lb=%s  [%.1fs]  stored %s"
                    % (tag, r["ok"], r["n"], ("%.4e" % r["minlb"]) if r["minlb"] is not None else "-", r["seconds"], sto))
    for tag, r in results.items():
        if tag.startswith("witness/E") or tag.startswith("deeper/"):
            P("%-52s E_direct=%s  E_I2=%s  (I2-direct=%s)" % (tag, r["E_direct"], r.get("E_I2"), r.get("I2_minus_direct")))
    Ew = mp.mpf(results["witness/E(T=1/40)"]["E_direct"])
    ref = mp.mpf("-13.07038157963107015514593001009491560179969447")
    verdict(abs(Ew - ref) < mp.mpf("1e-18"), "witness E(T=1/40) direct = Arb 256-bit value to 1e-18: |diff|=%s" % mp.nstr(abs(Ew - ref), 5))
    verdict(abs(mp.mpf(results["witness/E(T=1/40)"]["E_I2"]) - Ew) < mp.mpf("1e-25"), "witness: I2 identity reproduces the direct energy")
    for tag, r in results.items():
        if r["kind"] == "energy":
            val = mp.mpf(r["E_direct"])
            lo, hi = mp.mpf(r["interval_lo"]), mp.mpf(r["interval_hi"])
            verdict(lo - mp.mpf("1e-25") <= val <= hi + mp.mpf("1e-25"),
                    "%s multiprecision direct agrees with independent interval energy" % tag)
            if tag.startswith("scope/"):
                verdict(lo > 0, "%s energy interval strictly positive" % tag)
            elif tag.startswith(("witness/E", "deeper/")):
                verdict(hi < 0, "%s energy interval strictly negative" % tag)
    signs = [iv.cos(iv.mpf(float(z[n]))) for n in range(cx["N"])]
    verdict(all(s.b < 0 if n < 6 else s.a > 0 for n, s in enumerate(signs)),
            "scope: exactly six positive-frequency longitudinal reversals")
    for tag, r in results.items():
        if tag.startswith("deeper/"):
            Ed = mp.mpf(r["E_direct"])
            dd = next(d for d in tasks if d["tag"] == tag)
            verdict(abs(Ed - dd["float_E"]) < 1e-6 and Ed < 0, "%s E_mp=%s vs float search %.10f, interval sign checked above" % (tag, r["E_direct"][:20], dd["float_E"]))
            verdict(abs(mp.mpf(r["E_I2"]) - Ed) < mp.mpf("1e-25"), "%s I2 identity" % tag)
    # tail input check
    worst = 0
    for lam in (1, 2, 8):
        for v in (0.1, 1.0, 6.4):
            for K in (1, 2, 7, 40):
                ex_, bd = ix.S_tail_check(lam, v, K)
                worst = max(worst, float(ex_ - bd))
    verdict(worst <= 0, "tail input S(K) <= K_K + lam v atan(v/K) on 36 samples (max excess %.2e)" % worst)

    P("\n== mutants (each must be REJECTED) ==")
    for tag, pred in mut:
        r = results[tag]
        if pred == "cover_fails":
            rej = not r["ok"]
            detail = "cover ok=%s reached t=%.4f of requested" % (r["ok"], r["reached"])
        elif pred == "point_nonneg":
            rej = not r["neg"]
            detail = "2Q_u(v) in [%.4e, %.4e]" % (r["lo"], r["hi"])
        else:
            Em = mp.mpf(r["E_direct"])
            rej = not (Em <= ref + mp.mpf("1e-9"))
            detail = "E=%s" % mp.nstr(Em, 12)
        verdict(rej, "%-62s rejected=%s  (%s)" % (tag, rej, detail))
    P("\nTOTAL: %d failed checks; wall %.0f s" % (nfail, time.time() - t00))
    json.dump(results, open(os.path.join(LOGDIR, "verify_independent.json"), "w"), indent=1, default=str)
    log.close()
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
