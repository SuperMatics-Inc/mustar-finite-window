import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Infinite-tail certification lemma (paper eq. `eq:tail`, Lemma G)

Soundness of the block + tail reduction that every Arb certificate relies on.  For a symmetric
real matrix `A` indexed by `ℕ`, a block size `M` and `θ > 0`, we show: if

* (block) `a_B^T A_BB a_B ≥ θ Σ_{n<M} ρ_n a_n²` for every `a`, where `ρ_n` dominates every
  partial tail row sum `Σ_{M ≤ m < N} |A_{nm}|`,
* (tail) for every tail index `m ≥ M` and every `N > m`,
  `Σ_{m' ∈ [M,N), m' ≠ m} |A_{mm'}| + θ⁻¹ Σ_{n<M} |A_{nm}| ≤ A_{mm}`,

then `Σ_{n,m<N} A_{nm} a_n a_m ≥ 0` for every `N` and every `a`, i.e. `A` is PSD on `ℓ²_fin`.
(The paper's form of the tail coefficient `d_m − (θ⁻¹−1) b_m` is the same condition, because
`d_m` already subtracts the block couplings `b_m`.)
-/

open Finset

namespace MuStar

/-- Quadratic form of `A` on the index sets `s × t`. -/
def bf (A : ℕ → ℕ → ℝ) (s t : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, ∑ m ∈ t, A n m * a n * a m

/-- Off-diagonal absolute value. -/
noncomputable def offAbs (A : ℕ → ℕ → ℝ) (m m' : ℕ) : ℝ := if m = m' then 0 else |A m m'|

theorem amgm_abs (θ : ℝ) (hθ : 0 < θ) (x y : ℝ) :
    2 * (|x| * |y|) ≤ θ * x ^ 2 + θ⁻¹ * y ^ 2 := by
  set t := θ⁻¹ with ht
  have hθt : θ * t = 1 := by rw [ht]; exact mul_inv_cancel₀ hθ.ne'
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have h := mul_nonneg ht0 (sq_nonneg (θ * |x| - |y|))
  have e : θ * x ^ 2 + t * y ^ 2 - 2 * (|x| * |y|) = t * (θ * |x| - |y|) ^ 2 := by
    have hx := sq_abs x
    have hy := sq_abs y
    linear_combination (-θ) * hx + (-t) * hy + (-(θ * |x| ^ 2 - 2 * (|x| * |y|))) * hθt
  linarith

theorem cross_term (θ : ℝ) (hθ : 0 < θ) (x y c : ℝ) :
    -(|c| * (θ * x ^ 2 + θ⁻¹ * y ^ 2)) ≤ 2 * (c * x * y) := by
  have h := amgm_abs θ hθ x y
  have h1 : -|c * x * y| ≤ c * x * y := neg_abs_le _
  have h2 : |c * x * y| = |c| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
  have h3 := mul_le_mul_of_nonneg_left h (abs_nonneg c)
  linarith

theorem cross_sum (A : ℕ → ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ) (s t : Finset ℕ) (a : ℕ → ℝ) :
    -(θ * ∑ n ∈ s, (∑ m ∈ t, |A n m|) * a n ^ 2
      + θ⁻¹ * ∑ m ∈ t, (∑ n ∈ s, |A n m|) * a m ^ 2) ≤ 2 * bf A s t a := by
  have p1 : ∑ n ∈ s, ∑ m ∈ t, |A n m| * (θ * a n ^ 2)
      = θ * ∑ n ∈ s, (∑ m ∈ t, |A n m|) * a n ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_mul, mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have p2 : ∑ n ∈ s, ∑ m ∈ t, |A n m| * (θ⁻¹ * a m ^ 2)
      = θ⁻¹ * ∑ m ∈ t, (∑ n ∈ s, |A n m|) * a m ^ 2 := by
    rw [mul_sum]
    refine sum_comm.trans (sum_congr rfl fun m _ => ?_)
    rw [sum_mul, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hle : ∑ n ∈ s, ∑ m ∈ t, -(|A n m| * (θ * a n ^ 2 + θ⁻¹ * a m ^ 2))
      ≤ ∑ n ∈ s, ∑ m ∈ t, 2 * (A n m * a n * a m) :=
    sum_le_sum fun n _ => sum_le_sum fun m _ => cross_term θ hθ (a n) (a m) (A n m)
  have hsplit : ∀ n m, -(|A n m| * (θ * a n ^ 2 + θ⁻¹ * a m ^ 2))
      = -(|A n m| * (θ * a n ^ 2)) - |A n m| * (θ⁻¹ * a m ^ 2) := fun n m => by ring
  have hl : ∑ n ∈ s, ∑ m ∈ t, -(|A n m| * (θ * a n ^ 2 + θ⁻¹ * a m ^ 2))
      = -(θ * ∑ n ∈ s, (∑ m ∈ t, |A n m|) * a n ^ 2
          + θ⁻¹ * ∑ m ∈ t, (∑ n ∈ s, |A n m|) * a m ^ 2) := by
    simp only [hsplit, sum_sub_distrib, sum_neg_distrib, p1, p2]
    ring
  have hr : ∑ n ∈ s, ∑ m ∈ t, 2 * (A n m * a n * a m) = 2 * bf A s t a := by
    unfold bf
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by rw [mul_sum]
  rw [hl, hr] at hle
  exact hle

theorem offAbs_symm (A : ℕ → ℕ → ℝ) (hsym : ∀ n m, A n m = A m n) (m m' : ℕ) :
    offAbs A m m' = offAbs A m' m := by
  unfold offAbs
  by_cases h : m = m'
  · subst h; rfl
  · have h' : ¬ m' = m := fun e => h e.symm
    simp [h, h', hsym m m']

/-- Diagonal-dominance lower bound inside an index set. -/
theorem diag_bound (A : ℕ → ℕ → ℝ) (hsym : ∀ n m, A n m = A m n) (t : Finset ℕ) (a : ℕ → ℝ) :
    ∑ m ∈ t, (A m m - ∑ m' ∈ t, offAbs A m m') * a m ^ 2 ≤ bf A t t a := by
  have key : ∀ m m', -(1 / 2 * (offAbs A m m' * (a m ^ 2 + a m' ^ 2)))
      + (if m = m' then A m' m' * a m' ^ 2 else 0) ≤ A m m' * a m * a m' := by
    intro m m'
    by_cases h : m = m'
    · subst h
      have h0 : offAbs A m m = 0 := by simp [offAbs]
      have h2 : (if m = m then A m m * a m ^ 2 else 0) = A m m * a m ^ 2 := by simp
      rw [h0, h2]; nlinarith
    · have ho : offAbs A m m' = |A m m'| := by simp [offAbs, h]
      have h2 : (if m = m' then A m' m' * a m' ^ 2 else 0) = 0 := by simp [h]
      rw [ho, h2]
      have h1 : -|A m m' * a m * a m'| ≤ A m m' * a m * a m' := neg_abs_le _
      have h2 : |A m m' * a m * a m'| = |A m m'| * (|a m| * |a m'|) := by
        rw [abs_mul, abs_mul]; ring
      have h3 : 2 * (|a m| * |a m'|) ≤ a m ^ 2 + a m' ^ 2 := by
        nlinarith [sq_nonneg (|a m| - |a m'|), sq_abs (a m), sq_abs (a m')]
      have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg (A m m'))
      linarith
  have hsum := sum_le_sum fun m (_ : m ∈ t) => sum_le_sum fun m' (_ : m' ∈ t) => key m m'
  have hS : ∀ m', ∑ m ∈ t, offAbs A m m' = ∑ m ∈ t, offAbs A m' m :=
    fun m' => sum_congr rfl fun m _ => offAbs_symm A hsym m m'
  have c1 : ∑ m ∈ t, ∑ m' ∈ t, offAbs A m m' * a m ^ 2
      = ∑ m ∈ t, (∑ m' ∈ t, offAbs A m m') * a m ^ 2 :=
    sum_congr rfl fun m _ => by rw [← sum_mul]
  have c2 : ∑ m ∈ t, ∑ m' ∈ t, offAbs A m m' * a m' ^ 2
      = ∑ m ∈ t, (∑ m' ∈ t, offAbs A m m') * a m ^ 2 := by
    refine sum_comm.trans (sum_congr rfl fun m' _ => ?_)
    rw [← sum_mul, hS m']
  have c3 : ∑ m ∈ t, ∑ m' ∈ t, (if m = m' then A m' m' * a m' ^ 2 else 0)
      = ∑ m ∈ t, A m m * a m ^ 2 := by
    refine sum_congr rfl fun m hm => ?_
    rw [sum_ite_eq t m (fun j => A j j * a j ^ 2)]; simp [hm]
  have c4 : ∑ m ∈ t, ∑ m' ∈ t, (-(1 / 2 * (offAbs A m m' * (a m ^ 2 + a m' ^ 2)))
      + (if m = m' then A m' m' * a m' ^ 2 else 0))
      = -(∑ m ∈ t, (∑ m' ∈ t, offAbs A m m') * a m ^ 2) + ∑ m ∈ t, A m m * a m ^ 2 := by
    have e : ∀ m m', (-(1 / 2 * (offAbs A m m' * (a m ^ 2 + a m' ^ 2)))
        + (if m = m' then A m' m' * a m' ^ 2 else 0))
        = -(1 / 2 * (offAbs A m m' * a m ^ 2)) - 1 / 2 * (offAbs A m m' * a m' ^ 2)
          + (if m = m' then A m' m' * a m' ^ 2 else 0) := fun m m' => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum, c3]
    rw [c2, c1]
    ring
  have hlhs : ∑ m ∈ t, (A m m - ∑ m' ∈ t, offAbs A m m') * a m ^ 2
      = ∑ m ∈ t, A m m * a m ^ 2 - ∑ m ∈ t, (∑ m' ∈ t, offAbs A m m') * a m ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [c4] at hsum
  unfold bf
  linarith

theorem bf_split (A : ℕ → ℕ → ℝ) (a : ℕ → ℝ) {M N : ℕ} (h : M ≤ N) :
    bf A (range N) (range N) a
      = bf A (range M) (range M) a + bf A (range M) (Ico M N) a
        + bf A (Ico M N) (range M) a + bf A (Ico M N) (Ico M N) a := by
  unfold bf
  have e1 : ∀ n, ∑ m ∈ range N, A n m * a n * a m
      = ∑ m ∈ range M, A n m * a n * a m + ∑ m ∈ Ico M N, A n m * a n * a m :=
    fun n => (sum_range_add_sum_Ico (fun m => A n m * a n * a m) h).symm
  simp only [e1, sum_add_distrib]
  rw [← sum_range_add_sum_Ico (fun n => ∑ m ∈ range M, A n m * a n * a m) h,
    ← sum_range_add_sum_Ico (fun n => ∑ m ∈ Ico M N, A n m * a n * a m) h]
  ring

theorem bf_swap (A : ℕ → ℕ → ℝ) (hsym : ∀ n m, A n m = A m n) (s t : Finset ℕ) (a : ℕ → ℝ) :
    bf A t s a = bf A s t a := by
  unfold bf
  refine sum_comm.trans (sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_)
  rw [hsym m n]; ring

/-- The block + tail criterion for blocks of size `N ≥ M`. -/
theorem tail_main (A : ℕ → ℕ → ℝ) (hsym : ∀ n m, A n m = A m n) (M : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (ρ : ℕ → ℝ)
    (hρ : ∀ N n, n < M → ∑ m ∈ Ico M N, |A n m| ≤ ρ n)
    (hblock : ∀ a : ℕ → ℝ, θ * ∑ n ∈ range M, ρ n * a n ^ 2 ≤ bf A (range M) (range M) a)
    (htail : ∀ N m, M ≤ m → m < N →
      ∑ m' ∈ Ico M N, offAbs A m m' + θ⁻¹ * ∑ n ∈ range M, |A n m| ≤ A m m)
    {N : ℕ} (hMN : M ≤ N) (a : ℕ → ℝ) : 0 ≤ bf A (range N) (range N) a := by
  rw [bf_split A a hMN, bf_swap A hsym (range M) (Ico M N) a]
  have hBB := hblock a
  have hX : ∑ n ∈ range M, (∑ m ∈ Ico M N, |A n m|) * a n ^ 2 ≤ ∑ n ∈ range M, ρ n * a n ^ 2 :=
    sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (hρ N n (mem_range.mp hn)) (sq_nonneg _)
  have hX' := mul_le_mul_of_nonneg_left hX hθ.le
  have hBT := cross_sum A θ hθ (range M) (Ico M N) a
  have hTT := diag_bound A hsym (Ico M N) a
  have hcoef : 0 ≤ ∑ m ∈ Ico M N,
      (A m m - ∑ m' ∈ Ico M N, offAbs A m m' - θ⁻¹ * ∑ n ∈ range M, |A n m|) * a m ^ 2 := by
    refine sum_nonneg fun m hm => mul_nonneg ?_ (sq_nonneg _)
    rw [mem_Ico] at hm
    have := htail N m hm.1 hm.2
    linarith
  have hz : ∑ m ∈ Ico M N,
      (A m m - ∑ m' ∈ Ico M N, offAbs A m m' - θ⁻¹ * ∑ n ∈ range M, |A n m|) * a m ^ 2
      = ∑ m ∈ Ico M N, (A m m - ∑ m' ∈ Ico M N, offAbs A m m') * a m ^ 2
        - θ⁻¹ * ∑ m ∈ Ico M N, (∑ n ∈ range M, |A n m|) * a m ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by ring
  linarith

/-- **Lemma G** (soundness of the block + infinite-tail certificate). -/
theorem tail_psd (A : ℕ → ℕ → ℝ) (hsym : ∀ n m, A n m = A m n) (M : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (ρ : ℕ → ℝ)
    (hρ : ∀ N n, n < M → ∑ m ∈ Ico M N, |A n m| ≤ ρ n)
    (hblock : ∀ a : ℕ → ℝ, θ * ∑ n ∈ range M, ρ n * a n ^ 2 ≤ bf A (range M) (range M) a)
    (htail : ∀ N m, M ≤ m → m < N →
      ∑ m' ∈ Ico M N, offAbs A m m' + θ⁻¹ * ∑ n ∈ range M, |A n m| ≤ A m m)
    (N : ℕ) (a : ℕ → ℝ) : 0 ≤ bf A (range N) (range N) a := by
  set L := N + M with hL
  have hML : M ≤ L := by omega
  have hNL : N ≤ L := by omega
  set a' : ℕ → ℝ := fun n => if n < N then a n else 0 with ha'
  have hz : ∀ n, N ≤ n → a' n = 0 := fun n hn => by simp [ha', not_lt.mpr hn]
  have inner : ∀ n, ∑ m ∈ range L, A n m * a' n * a' m = ∑ m ∈ range N, A n m * a' n * a' m := by
    intro n
    refine (sum_subset (range_subset_range.mpr hNL) fun m _ hm => ?_).symm
    rw [hz m (not_lt.mp (mem_range.not.mp hm))]; ring
  have hpad : bf A (range L) (range L) a' = bf A (range N) (range N) a := by
    unfold bf
    simp only [inner]
    have h1 : ∑ n ∈ range L, ∑ m ∈ range N, A n m * a' n * a' m
        = ∑ n ∈ range N, ∑ m ∈ range N, A n m * a' n * a' m := by
      refine (sum_subset (range_subset_range.mpr hNL) fun n _ hn => ?_).symm
      rw [hz n (not_lt.mp (mem_range.not.mp hn))]
      exact sum_eq_zero fun m _ => by ring
    rw [h1]
    refine sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_
    have hn' := mem_range.mp hn
    have hm' := mem_range.mp hm
    simp [ha', hn', hm']
  rw [← hpad]
  exact tail_main A hsym M θ hθ ρ hρ hblock htail hML a'

end MuStar
