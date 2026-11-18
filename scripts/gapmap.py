"""NUMERICAL block proposals only; no endpoint or non-reentrance theorem is asserted."""
import json
import numpy as np
from fc import Chain


def Nfor(T, Nc):
    return min(400, max(Nc + 10, int(10 / (2 * np.pi * T)) + 30))


def ev_even(lam, T, Nc, u):
    return np.linalg.eigvalsh(Chain(lam, T, Nfor(T, Nc), Nc, u).Heven())[0]


def ev_G(lam, T):
    ch = Chain(lam, T, Nfor(T, 1), 1, 0.0)
    return np.linalg.eigvalsh(0.5 * (ch.H0() + ch.Hodd()))[0]


def ev_B(lam, T):
    ch = Chain(lam, T, Nfor(T, 1), 1, 0.0)
    return np.linalg.eigvalsh(ch.H0() + np.diag(ch.w))[0]


def Tsup(f, lo=5e-3, hi=3.0, n=90):
    Ts = np.geomspace(lo, hi, n)
    v = np.array([f(T) for T in Ts])
    neg = np.where(v < 0)[0]
    if len(neg) == 0:
        return 0.0, False
    i = neg[-1]
    a, b = Ts[i], Ts[i + 1]
    for _ in range(40):
        m = 0.5 * (a + b)
        a, b = (m, b) if f(m) < 0 else (a, m)
    return 0.5 * (a + b), bool(np.any(v[:i] >= 0))


