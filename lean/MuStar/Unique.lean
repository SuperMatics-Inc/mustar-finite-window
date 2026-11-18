import MuStar.I2

/-!
# Two-form uniqueness criterion (paper Theorem `thm:unique`) and monotonicity in `u`
-/

open Finset

namespace MuStar

variable (κ : Kernel)

/-- A one-variable quadratic `c s² - 2 s B` that is nonnegative for all `s` forces `B = 0`. -/
theorem quad_aux (c B : ℝ) (hc : 0 < c) (h : ∀ s : ℝ, 0 ≤ c * s ^ 2 - 2 * s * B) : B = 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, B = c * s := ⟨B / c, by field_simp⟩
  have h1 := h s
  rw [hs] at h1 ⊢
  have h2 : c * s ^ 2 ≤ 0 := by nlinarith
  have h3 : s ^ 2 ≤ 0 := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_pos hc hcon'
    linarith
  have h5 : s ^ 2 = 0 := le_antisymm h3 (sq_nonneg s)
  have h4 : s = 0 := (pow_eq_zero_iff two_ne_zero).mp h5
  rw [h4]; ring

/-- Enlarging the block by one site carrying the value `s`. -/
theorem Gform_succ (N : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    Gform κ (N + 1) (fun n => if n = N then s else a n)
      = Gform κ N a + c κ N * s ^ 2 - 2 * s * ∑ n ∈ range N, T κ N n * a n := by
  set a' : ℕ → ℝ := fun n => if n = N then s else a n with ha'
  have hlt : ∀ n ∈ range N, a' n = a n := fun n hn => by
    have := mem_range.mp hn
    simp [ha', ne_of_lt this]
  have hN : a' N = s := by simp [ha']
  unfold Gform bil
  have e1 : ∑ n ∈ range N, c κ n * a' n ^ 2 = ∑ n ∈ range N, c κ n * a n ^ 2 :=
    sum_congr rfl fun n hn => by rw [hlt n hn]
  have hin : ∀ n ∈ range N, ∑ m ∈ range (N + 1), T κ n m * a' n * a' m
      = ∑ m ∈ range N, T κ n m * a n * a m + T κ n N * a n * s := by
    intro n hn
    rw [sum_range_succ, hN, hlt n hn]
    congr 1
    exact sum_congr rfl fun m hm => by rw [hlt m hm]
  have hlast : ∑ m ∈ range (N + 1), T κ N m * a' N * a' m
      = s * ∑ m ∈ range N, T κ N m * a m := by
    rw [sum_range_succ, hN, T_self, mul_sum]
    simp only [zero_mul, add_zero]
    exact sum_congr rfl fun m hm => by rw [hlt m hm]; ring
  have hx : ∑ n ∈ range N, T κ n N * a n * s = s * ∑ n ∈ range N, T κ N n * a n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by rw [T_symm κ n N]; ring
  have e2 : ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1), T κ n m * a' n * a' m
      = ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * a n * a m
        + 2 * (s * ∑ n ∈ range N, T κ N n * a n) := by
    rw [sum_range_succ, sum_congr rfl hin, hlast, sum_add_distrib]
    linarith [hx]
  rw [sum_range_succ (fun n => c κ n * a' n ^ 2) N, e1, e2, hN]
  ring

/-- For a PSD `G`, a nonnegative vector with `G(a) = 0` vanishes on its block. -/
theorem Gform_zero_imp (hG : PsdG κ) (N : ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h0 : Gform κ N a = 0) : ∀ n < N, a n = 0 := by
  have hB : ∑ n ∈ range N, T κ N n * a n = 0 := by
    refine quad_aux (c κ N) _ (c_pos κ N) fun s => ?_
    have h := hG (N + 1) (fun n => if n = N then s else a n)
    rw [Gform_succ κ N a s, h0] at h
    linarith
  intro n hn
  have hterm := (sum_eq_zero_iff_of_nonneg
    (fun m _ => mul_nonneg (T_nonneg κ N m) (ha m))).mp hB n (mem_range.mpr hn)
  have hpos : 0 < T κ N n := by
    unfold T
    have h1 : ¬ N < n := by omega
    simp [h1, hn, κ.pos]
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hpos)

theorem alpha_nonneg (S : Cfg) (hU : S.Unit) (n : ℕ) : 0 ≤ S.alpha n := by
  obtain ⟨h1, _⟩ := hU n
  unfold Cfg.alpha
  nlinarith [sq_nonneg (S.xx n), sq_nonneg (S.xy n)]

theorem beta_nonneg (S : Cfg) (hU : S.Unit) (n : ℕ) : 0 ≤ S.beta n := by
  obtain ⟨_, h2⟩ := hU n
  unfold Cfg.beta
  nlinarith [sq_nonneg (S.ex n), sq_nonneg (S.ey n)]

/-- The normal state has zero energy. -/
theorem energy_normal (Nc : ℕ) (u : ℝ) (N : ℕ) : energy κ Nc u N Cfg.normal = 0 := by
  norm_num [energy, Cfg.normal, Cfg.alpha, Cfg.beta]

/-- **Theorem (two-form uniqueness).**  If `Q_u` and `G` are PSD then, for every block, every
unit-spin configuration has `E ≥ 0`, with `E = 0` only at the normal state. -/
theorem thm_unique (Nc : ℕ) (u : ℝ) (hQ : PsdQu κ Nc u) (hG : PsdG κ)
    (N : ℕ) (S : Cfg) (hU : S.Unit) :
    0 ≤ energy κ Nc u N S ∧ (energy κ Nc u N S = 0 → S.NormalOn N) := by
  have hI := energy_I2 κ Nc u N S hU
  have t1 := hQ N S.Px
  have t2 := hQ N S.Py
  have t3 : 0 ≤ Q2o κ N S.Rx :=
    le_trans (sum_nonneg fun n _ => sq_nonneg (S.Rx n)) (lemma_odd_sq κ N S.Rx)
  have t4 : 0 ≤ Q2o κ N S.Ry :=
    le_trans (sum_nonneg fun n _ => sq_nonneg (S.Ry n)) (lemma_odd_sq κ N S.Ry)
  have t5 := hG N S.alpha
  have t6 := hG N S.beta
  have t7 : 0 ≤ bil (H κ) N S.alpha S.beta :=
    sum_nonneg fun n _ => sum_nonneg fun m _ =>
      mul_nonneg (mul_nonneg (H_pos κ n m).le (alpha_nonneg S hU n)) (beta_nonneg S hU m)
  refine ⟨by rw [hI]; linarith, ?_⟩
  intro h0
  rw [hI] at h0
  have hGa : Gform κ N S.alpha = 0 := by linarith
  have hGb : Gform κ N S.beta = 0 := by linarith
  have hα := Gform_zero_imp κ hG N S.alpha (alpha_nonneg S hU) hGa
  have hβ := Gform_zero_imp κ hG N S.beta (beta_nonneg S hU) hGb
  intro n hn
  have h1 : S.xz n = 1 := by have := hα n hn; unfold Cfg.alpha at this; linarith
  have h2 : S.ez n = 1 := by have := hβ n hn; unfold Cfg.beta at this; linarith
  obtain ⟨e1, e2⟩ := hU n
  rw [h1] at e1
  rw [h2] at e2
  have hxx : S.xx n = 0 := by
    have h : S.xx n ^ 2 = 0 := by nlinarith [sq_nonneg (S.xx n), sq_nonneg (S.xy n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  have hxy : S.xy n = 0 := by
    have h : S.xy n ^ 2 = 0 := by nlinarith [sq_nonneg (S.xx n), sq_nonneg (S.xy n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  have hex : S.ex n = 0 := by
    have h : S.ex n ^ 2 = 0 := by nlinarith [sq_nonneg (S.ex n), sq_nonneg (S.ey n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  have hey : S.ey n = 0 := by
    have h : S.ey n ^ 2 = 0 := by nlinarith [sq_nonneg (S.ex n), sq_nonneg (S.ey n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  exact ⟨hxx, hxy, h1, hex, hey, h2⟩

/-- `Q_u` is nondecreasing in the Coulomb strength `u`. -/
theorem Q2u_mono (Nc : ℕ) (N : ℕ) (a : ℕ → ℝ) {u u' : ℝ} (h : u ≤ u') :
    Q2u κ Nc u N a ≤ Q2u κ Nc u' N a := by
  unfold Q2u
  have := sq_nonneg (∑ n ∈ range N, chi Nc n * a n)
  nlinarith

/-- Increasing `u` preserves positive semidefiniteness of `Q_u`. -/
theorem psdQu_mono (Nc : ℕ) {u u' : ℝ} (h : u ≤ u') (hP : PsdQu κ Nc u) : PsdQu κ Nc u' :=
  fun N a => le_trans (hP N a) (Q2u_mono κ Nc N a h)

/-- A negative direction at `u₁` persists for every `u ≤ u₁`. -/
theorem not_psdQu_mono (Nc : ℕ) {u u' : ℝ} (h : u ≤ u') (hP : ¬ PsdQu κ Nc u') :
    ¬ PsdQu κ Nc u :=
  fun hu => hP (psdQu_mono κ Nc h hu)

end MuStar
