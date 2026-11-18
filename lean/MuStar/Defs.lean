import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Definitions for the finite-window Coulomb-penalised Matsubara spin chain

Everything here is stated for a block `range N` of Matsubara indices with spins
outside the block frozen to the normal state `(0,0,1)`. The telescoped exterior
weight is part of the block definition. Its identification with the infinite-chain
sum and padding invariance are proved in the text, not separately formalised here.
The extension from finitely supported configurations to the full admissible
class `A_Z` is also not formalised; see the repository-root `README.md` (Lean scope).

The kernel is an abstract positive, antitone sequence `K : ℕ → ℝ`; the Einstein kernel
`K_k = λ v² / (v² + k²)` of the paper is an instance (`Kernel.einstein`).
-/

open Finset

namespace MuStar

/-- A coupling kernel: `K k` is the pair coupling at Matsubara index distance `k`. -/
structure Kernel where
  K : ℕ → ℝ
  pos : ∀ k, 0 < K k
  anti : Antitone K

/-- The Einstein kernel `K_k = λ v² / (v² + k²)` of the paper. -/
noncomputable def Kernel.einstein (lam v : ℝ) (hl : 0 < lam) (hv : 0 < v) : Kernel where
  K := fun k => lam * v ^ 2 / (v ^ 2 + (k : ℝ) ^ 2)
  pos := fun k => by positivity
  anti := by
    intro a b hab
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have h1 : (a : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by nlinarith
    have h2 : 0 < v ^ 2 + (a : ℝ) ^ 2 := by positivity
    exact div_le_div_of_nonneg_left (by positivity) h2 (by linarith)

variable (κ : Kernel)

/-- `Λ_n = Σ_{k=1}^{n} K_k`. -/
noncomputable def Lam (n : ℕ) : ℝ := ∑ k ∈ range n, κ.K (k + 1)

/-- Free weight `w_n = 2n+1` (the Matsubara frequency in units of `π T`). -/
def w (n : ℕ) : ℝ := 2 * n + 1

/-- Diagonal coefficient `c_n = w_n + 2 Λ_n`. -/
noncomputable def c (n : ℕ) : ℝ := w n + 2 * Lam κ n

/-- Ferromagnetic Toeplitz part `T_{nm} = K_{|n-m|}` for `n ≠ m`, `T_{nn} = 0`. -/
noncomputable def T (n m : ℕ) : ℝ :=
  if n < m then κ.K (m - n) else if m < n then κ.K (n - m) else 0

/-- Hankel part `H_{nm} = K_{n+m+1}`. -/
noncomputable def H (n m : ℕ) : ℝ := κ.K (n + m + 1)

/-- `W = T + H`. -/
noncomputable def W (n m : ℕ) : ℝ := T κ n m + H κ n m

/-- `D = T - H` (the odd-sector matrix; `D_{nm} ≥ 0` for `n ≠ m`). -/
noncomputable def Dm (n m : ℕ) : ℝ := T κ n m - H κ n m

/-- Indicator of the Coulomb window `n < N_c`. -/
def chi (Nc n : ℕ) : ℝ := if n < Nc then 1 else 0

/-- Block bilinear sum `Σ_{n,m<N} M_{nm} a_n b_m`. -/
noncomputable def bil (M : ℕ → ℕ → ℝ) (N : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, ∑ m ∈ range N, M n m * a n * b m

/-- `2 Q_u(a)` on the block: `Σ c_n a_n² - ⟨a, W a⟩ + 2u (χ·a)²`. -/
noncomputable def Q2u (Nc : ℕ) (u : ℝ) (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, c κ n * a n ^ 2 - bil (W κ) N a a
    + 2 * u * (∑ n ∈ range N, chi Nc n * a n) ^ 2

/-- `2 Q^o(a)` on the block: `Σ c_n a_n² - ⟨a, (T-H) a⟩`. -/
noncomputable def Q2o (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, c κ n * a n ^ 2 - bil (Dm κ) N a a

/-- `G(a)` on the block: `Σ c_n a_n² - ⟨a, T a⟩`. -/
noncomputable def Gform (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, c κ n * a n ^ 2 - bil (T κ) N a a

/-- Positive semidefiniteness of `2 Q_u` on all finitely supported vectors. -/
def PsdQu (Nc : ℕ) (u : ℝ) : Prop := ∀ (N : ℕ) (a : ℕ → ℝ), 0 ≤ Q2u κ Nc u N a

/-- Positive semidefiniteness of `G` on all finitely supported vectors. -/
def PsdG : Prop := ∀ (N : ℕ) (a : ℕ → ℝ), 0 ≤ Gform κ N a

/-- A configuration of the folded chain: `ξ_n = (xx, xy, xz)`, `η_n = (ex, ey, ez)`. -/
structure Cfg where
  xx : ℕ → ℝ
  xy : ℕ → ℝ
  xz : ℕ → ℝ
  ex : ℕ → ℝ
  ey : ℕ → ℝ
  ez : ℕ → ℝ

/-- Unit-spin constraint at every site. -/
def Cfg.Unit (S : Cfg) : Prop :=
  ∀ n, S.xx n ^ 2 + S.xy n ^ 2 + S.xz n ^ 2 = 1 ∧ S.ex n ^ 2 + S.ey n ^ 2 + S.ez n ^ 2 = 1

/-- `α_n = 1 - ξ_n^z`. -/
def Cfg.alpha (S : Cfg) (n : ℕ) : ℝ := 1 - S.xz n

/-- `β_n = 1 - η_n^z`. -/
def Cfg.beta (S : Cfg) (n : ℕ) : ℝ := 1 - S.ez n

/-- The normal state: all spins along `e_z`. -/
def Cfg.normal : Cfg := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 1⟩

/-- `S` is normal at every site of the block `range N`. -/
def Cfg.NormalOn (S : Cfg) (N : ℕ) : Prop :=
  ∀ n < N, S.xx n = 0 ∧ S.xy n = 0 ∧ S.xz n = 1 ∧ S.ex n = 0 ∧ S.ey n = 0 ∧ S.ez n = 1

/-- Tail weight `t_n = Σ_{m ≥ N} (K_{m-n} - K_{n+m+1}) = Σ_{k=N-n}^{N+n} K_k` (telescoped),
the contribution of the frozen normal exterior to the free weight of site `n < N`. -/
noncomputable def tailW (N n : ℕ) : ℝ := Lam κ (N + n) - Lam κ (N - n - 1)

/-- Block energy (paper eq. (energy)) with a frozen normal exterior:
`E = Σ_n (w_n + t_n)(α_n + β_n) + Σ_{n<m} K_{m-n}(2 - ξ_n·ξ_m - η_n·η_m)
   - Σ_{n,m} K_{n+m+1}(1 + ξ_n^⊥·η_m^⊥ - ξ_n^z η_m^z) + (u/2) |Σ_{n<N_c} (ξ_n^⊥+η_n^⊥)|²`. -/
noncomputable def energy (Nc : ℕ) (u : ℝ) (N : ℕ) (S : Cfg) : ℝ :=
  ∑ n ∈ range N, (w n + tailW κ N n) * (S.alpha n + S.beta n)
  + ∑ n ∈ range N, ∑ m ∈ (range N).filter (fun m => n < m),
      κ.K (m - n) * (2 - (S.xx n * S.xx m + S.xy n * S.xy m + S.xz n * S.xz m)
                       - (S.ex n * S.ex m + S.ey n * S.ey m + S.ez n * S.ez m))
  - ∑ n ∈ range N, ∑ m ∈ range N,
      κ.K (n + m + 1) * (1 + (S.xx n * S.ex m + S.xy n * S.ey m) - S.xz n * S.ez m)
  + u / 2 * ((∑ n ∈ range N, chi Nc n * (S.xx n + S.ex n)) ^ 2
             + (∑ n ∈ range N, chi Nc n * (S.xy n + S.ey n)) ^ 2)

/-! ### Elementary kernel facts -/

theorem T_symm (n m : ℕ) : T κ n m = T κ m n := by
  unfold T
  rcases lt_trichotomy n m with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst h; simp
  · simp [h, not_lt.mpr h.le]

theorem T_self (n : ℕ) : T κ n n = 0 := by simp [T]

theorem T_nonneg (n m : ℕ) : 0 ≤ T κ n m := by
  unfold T
  split_ifs
  · exact (κ.pos _).le
  · exact (κ.pos _).le
  · exact le_refl _

theorem H_symm (n m : ℕ) : H κ n m = H κ m n := by
  unfold H; rw [add_comm n m]

theorem H_pos (n m : ℕ) : 0 < H κ n m := κ.pos _

theorem Dm_symm (n m : ℕ) : Dm κ n m = Dm κ m n := by
  unfold Dm; rw [T_symm, H_symm]

/-- `D_{nm} ≥ 0` off the diagonal (monotone kernel). -/
theorem Dm_nonneg {n m : ℕ} (h : n ≠ m) : 0 ≤ Dm κ n m := by
  unfold Dm T H
  rcases lt_or_gt_of_ne h with h' | h'
  · simp only [h', ite_true]
    have : κ.K (n + m + 1) ≤ κ.K (m - n) := κ.anti (by omega)
    linarith
  · have h'' : ¬ n < m := by omega
    simp only [h'', ite_false, h', ite_true]
    have : κ.K (n + m + 1) ≤ κ.K (n - m) := κ.anti (by omega)
    linarith

theorem Lam_zero : Lam κ 0 = 0 := by simp [Lam]

theorem Lam_succ (n : ℕ) : Lam κ (n + 1) = Lam κ n + κ.K (n + 1) := by
  simp [Lam, sum_range_succ]

theorem Lam_nonneg (n : ℕ) : 0 ≤ Lam κ n :=
  sum_nonneg fun _ _ => (κ.pos _).le

theorem Lam_mono {a b : ℕ} (h : a ≤ b) : Lam κ a ≤ Lam κ b := by
  unfold Lam
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) fun k _ _ => (κ.pos _).le

theorem tailW_nonneg (N n : ℕ) : 0 ≤ tailW κ N n := by
  unfold tailW
  have : Lam κ (N - n - 1) ≤ Lam κ (N + n) := Lam_mono κ (by omega)
  linarith

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; positivity

theorem c_pos (n : ℕ) : 0 < c κ n := by
  unfold c
  have := w_pos n
  have := Lam_nonneg κ n
  linarith

end MuStar
