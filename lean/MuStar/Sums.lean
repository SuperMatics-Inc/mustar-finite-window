import MuStar.Defs

/-!
# Finite-sum lemmas: symmetrisation, row sums, and the odd-sector bound (paper Lemma `lem:odd`)
-/

open Finset

namespace MuStar

variable (κ : Kernel)

/-- An antisymmetric integrand sums to zero over a square block. -/
theorem sum_antisymm (N : ℕ) (Φ : ℕ → ℕ → ℝ) (h : ∀ n m, Φ n m = -Φ m n) :
    ∑ n ∈ range N, ∑ m ∈ range N, Φ n m = 0 := by
  have h1 : ∑ n ∈ range N, ∑ m ∈ range N, Φ n m = ∑ n ∈ range N, ∑ m ∈ range N, Φ m n :=
    sum_comm
  have h2 : ∑ n ∈ range N, ∑ m ∈ range N, Φ m n = -∑ n ∈ range N, ∑ m ∈ range N, Φ n m := by
    simp only [← sum_neg_distrib]
    exact sum_congr rfl fun n _ => sum_congr rfl fun m _ => h m n
  linarith

/-- For a symmetric matrix, the two one-index weightings of a double sum agree. -/
theorem sum_swap (N : ℕ) (M : ℕ → ℕ → ℝ) (hM : ∀ n m, M n m = M m n) (f : ℕ → ℝ) :
    ∑ n ∈ range N, ∑ m ∈ range N, M n m * f n = ∑ n ∈ range N, ∑ m ∈ range N, M n m * f m := by
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun m _ => by rw [hM m n]

/-- Sum of `T` over the row `n` of the block `N` (`n < N`). -/
theorem rowsum_T (N n : ℕ) (hn : n < N) :
    ∑ m ∈ range N, T κ n m = Lam κ n + Lam κ (N - n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j := ⟨N - n - 1, by omega⟩
  rw [sum_range_add, sum_range_succ]
  have h1 : ∑ x ∈ range n, T κ n x = Lam κ n := by
    have : ∑ x ∈ range n, T κ n x = ∑ x ∈ range n, κ.K (n - 1 - x + 1) := by
      refine sum_congr rfl fun x hx => ?_
      have hx' : x < n := mem_range.mp hx
      have e1 : n - 1 - x + 1 = n - x := by omega
      simp [T, hx', not_lt.mpr hx'.le, e1]
    rw [this]
    exact sum_range_reflect (fun k => κ.K (k + 1)) n
  have h2 : ∑ x ∈ range j, T κ n (n + 1 + x) = Lam κ j := by
    unfold Lam
    refine sum_congr rfl fun x _ => ?_
    have e1 : n + 1 + x - n = x + 1 := by omega
    have e2 : n < n + 1 + x := by omega
    simp [T, e2, e1]
  have h3 : n + 1 + j - n - 1 = j := by omega
  rw [h3, h1, h2, T_self]
  ring

/-- Sum of `H` over the row `n` of the block `N`. -/
theorem rowsum_H (N n : ℕ) : ∑ m ∈ range N, H κ n m = Lam κ (n + N) - Lam κ n := by
  unfold Lam H
  rw [sum_range_add (fun k => κ.K (k + 1)) n N]
  ring

/-- The row-sum identity: `Σ_m T_{nm} - Σ_m H_{nm} + t_n = 2 Λ_n`. -/
theorem rowsum (N n : ℕ) (hn : n < N) :
    ∑ m ∈ range N, T κ n m - ∑ m ∈ range N, H κ n m + tailW κ N n = 2 * Lam κ n := by
  rw [rowsum_T κ N n hn, rowsum_H κ N n]
  unfold tailW
  rw [add_comm N n]
  ring

theorem rowsum_Dm (N n : ℕ) (hn : n < N) :
    ∑ m ∈ range N, Dm κ n m = 2 * Lam κ n - tailW κ N n := by
  have := rowsum κ N n hn
  unfold Dm
  rw [sum_sub_distrib]
  linarith

/-- Identity for the odd-sector form (the content of `lem:odd`):
`2Q^o(a) = Σ (w_n + t_n) a_n² + ½ Σ_{n,m} D_{nm}(a_n - a_m)²`. -/
theorem Q2o_eq (N : ℕ) (a : ℕ → ℝ) :
    Q2o κ N a = ∑ n ∈ range N, (w n + tailW κ N n) * a n ^ 2
      + (1 / 2) * ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * (a n - a m) ^ 2 := by
  have hexp : ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * (a n - a m) ^ 2
      = ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * a n ^ 2
        + ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * a m ^ 2
        - 2 * bil (Dm κ) N a a := by
    unfold bil
    have : ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * (a n - a m) ^ 2
        = ∑ n ∈ range N, ∑ m ∈ range N,
            (Dm κ n m * a n ^ 2 + Dm κ n m * a m ^ 2 - 2 * (Dm κ n m * a n * a m)) :=
      sum_congr rfl fun n _ => sum_congr rfl fun m _ => by ring
    rw [this]
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  have hswap := sum_swap N (Dm κ) (Dm_symm κ) (fun m => a m ^ 2)
  have hrow : ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * a n ^ 2
      = ∑ n ∈ range N, (2 * Lam κ n - tailW κ N n) * a n ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_mul, rowsum_Dm κ N n (mem_range.mp hn)]
  unfold Q2o
  rw [hexp, ← hswap, hrow]
  have : ∑ n ∈ range N, c κ n * a n ^ 2
      = ∑ n ∈ range N, (w n + tailW κ N n) * a n ^ 2
        + ∑ n ∈ range N, (2 * Lam κ n - tailW κ N n) * a n ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun n _ => by unfold c; ring
  rw [this]
  ring

/-- **Lemma (odd sector).** `2 Q^o(a) ≥ Σ (2n+1) a_n² ≥ Σ a_n²`, for every block. -/
theorem lemma_odd (N : ℕ) (a : ℕ → ℝ) :
    ∑ n ∈ range N, w n * a n ^ 2 ≤ Q2o κ N a := by
  rw [Q2o_eq κ N a]
  have h1 : 0 ≤ ∑ n ∈ range N, tailW κ N n * a n ^ 2 :=
    sum_nonneg fun n _ => mul_nonneg (tailW_nonneg κ N n) (sq_nonneg _)
  have h2 : 0 ≤ ∑ n ∈ range N, ∑ m ∈ range N, Dm κ n m * (a n - a m) ^ 2 := by
    refine sum_nonneg fun n _ => sum_nonneg fun m _ => ?_
    by_cases h : n = m
    · subst h; simp
    · exact mul_nonneg (Dm_nonneg κ h) (sq_nonneg _)
  have h3 : ∑ n ∈ range N, (w n + tailW κ N n) * a n ^ 2
      = ∑ n ∈ range N, w n * a n ^ 2 + ∑ n ∈ range N, tailW κ N n * a n ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  linarith

/-- `2 Q^o(a) ≥ Σ a_n²`. -/
theorem lemma_odd_sq (N : ℕ) (a : ℕ → ℝ) : ∑ n ∈ range N, a n ^ 2 ≤ Q2o κ N a := by
  refine le_trans ?_ (lemma_odd κ N a)
  refine sum_le_sum fun n _ => ?_
  have : (1 : ℝ) ≤ w n := by unfold w; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  nlinarith [sq_nonneg (a n)]

end MuStar
