"""Full-chain (non-TRS) Eliashberg spin energy with symmetric finite-window Coulomb term.

Frozen-normal truncation: spins j>=N and j<-N are fixed at the normal state. This is a
restriction of the configuration space, so energies computed here are EXACT energies of
finitely supported configurations of the infinite chain (no truncation error in E).

Planar parametrisation, n = 0..N-1:
  xi_n  = S_n             = (sin a_n, cos a_n)   (x, z)
  ups_n = M S_{-n-1}      = (sin b_n, cos b_n)   (M = z-mirror)
TRS  <=>  a == b.

E(a,b) = sum_n wt_n (2 - cos a_n - cos b_n)
       + 1/2 sum_{n!=m} lam(|n-m|) [(1-cos(a_n-a_m)) + (1-cos(b_n-b_m))]
       - sum_{n,m} lam(n+m+1) (1 - cos(a_n + b_m))
       + (u/2) (sum_{n<Nc} (sin a_n + sin b_n))^2
with wt_n = (2n+1) + t_n,  t_n = sum_{m>=N} D_nm  (exterior normal spins).
TRS restriction: E(th,th) = 2 K_u(th),  K_u = K + u (sum_{n<Nc} sin th_n)^2.
"""
import numpy as np


def einstein_lam(lam, varpi, kmax):
    k = np.arange(kmax + 1, dtype=float)
    return lam * varpi**2 / (varpi**2 + k**2)


class Chain:
    def __init__(self, lam, T, N, Nc, u, Omega=1.0, kern=None):
        self.N, self.Nc, self.u = N, Nc, u
        varpi = Omega / (2 * np.pi * T)
        kmax = 2 * N + 2
        if kern is None:
            lk = einstein_lam(lam, varpi, kmax)
            self.lamk = lambda k: lam * varpi**2 / (varpi**2 + np.asarray(k, float) ** 2)
        else:
            self.lamk = kern
            lk = kern(np.arange(kmax + 1))
        n = np.arange(N)
        self.w = 2 * n + 1.0
        L1 = lk[np.abs(n[:, None] - n[None, :])].copy()
        np.fill_diagonal(L1, 0.0)
        L2 = lk[n[:, None] + n[None, :] + 1]
        self.L1, self.L2 = L1, L2
        # exact Lambda_n = sum_{k=1}^n lam(k)
        self.Lam = np.array([lk[1:i + 1].sum() for i in range(N)])
        # sum_{m != n, all m>=0} D_nm = 2 Lambda_n + lam(2n+1)  (Lemma Dsum of the paper)
        Dfull = 2 * self.Lam + lk[2 * n + 1]
        Dblock = (L1 - L2).copy()
        np.fill_diagonal(Dblock, 0.0)
        self.t = Dfull - Dblock.sum(1)
        self.wt = self.w + self.t
        self.chi = (n < Nc).astype(float)
        self.W = L1 + L2  # W_nm = [n!=m] lam|n-m| + lam(n+m+1)
        self.D = Dblock

    # ---- quadratic forms ----
    def Heven(self, u=None):
        """2 Q_u on the block: diag(w+2Lam) - W + 2u chi chi^T."""
        u = self.u if u is None else u
        return np.diag(self.w + 2 * self.Lam) - self.W + 2 * u * np.outer(self.chi, self.chi)

    def Hodd(self):
        """2 Q^o on the block: diag(w + sum_{m!=n} D_nm) - D."""
        return np.diag(self.w + 2 * self.Lam + self.lamk(2 * np.arange(self.N) + 1)) - self.D

    def H0(self):
        return self.Heven(0.0)

