import MuStar.Unique

/-!
# Mirror sector (paper Theorem `thm:mirror`, Theorem A)

In the sector `η = ξ` (the second chain is the exact copy of the first) the identity
`prop:I2` collapses to `E = 2Q_u(ξ^x) + 2Q_u(ξ^y) + 2Q^o(α)`.  We prove:

* `energy_mirror`: this identity;
* `thm_mirror_pos`: if `Q_u` is PSD then `E ≥ 0` with equality only at the normal state;
* `thm_mirror_neg`: if `Q_u` is not PSD there is a mirror configuration with `E < 0`
  (constructive tilt `ξ = (ε a, 0, √(1-ε²a²))`);
* `thm_mirror`: the equivalence `Q_u PSD ↔ N is a global minimiser in the mirror sector`.
-/

open Finset

namespace MuStar

variable (κ : Kernel)

/-- The mirror sector: `η_n = ξ_n`. -/
def Cfg.Mirror (S : Cfg) : Prop := ∀ n, S.ex n = S.xx n ∧ S.ey n = S.xy n ∧ S.ez n = S.xz n

theorem Q2o_zero (N : ℕ) : Q2o κ N (fun _ => 0) = 0 := by simp [Q2o, bil]

theorem Q2u_zero (Nc : ℕ) (u : ℝ) (N : ℕ) : Q2u κ Nc u N (fun _ => 0) = 0 := by
  simp [Q2u, bil]

/-- `Q^o = G + ⟨·, H ·⟩`, i.e. `T - H` splits. -/
theorem Q2o_eq_GH (N : ℕ) (a : ℕ → ℝ) : Q2o κ N a = Gform κ N a + bil (H κ) N a a := by
  unfold Q2o Gform bil Dm
  have h : ∑ n ∈ range N, ∑ m ∈ range N, (T κ n m - H κ n m) * a n * a m
      = ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * a n * a m
        - ∑ n ∈ range N, ∑ m ∈ range N, H κ n m * a n * a m := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [h]; ring

theorem energy_mirror (Nc : ℕ) (u : ℝ) (N : ℕ) (S : Cfg) (hU : S.Unit) (hM : S.Mirror) :
    energy κ Nc u N S = Q2u κ Nc u N S.xx + Q2u κ Nc u N S.xy + Q2o κ N S.alpha := by
  rw [energy_I2 κ Nc u N S hU]
  have hPx : S.Px = S.xx := funext fun n => by unfold Cfg.Px; rw [(hM n).1]; ring
  have hPy : S.Py = S.xy := funext fun n => by unfold Cfg.Py; rw [(hM n).2.1]; ring
  have hRx : S.Rx = fun _ => 0 := funext fun n => by unfold Cfg.Rx; rw [(hM n).1]; ring
  have hRy : S.Ry = fun _ => 0 := funext fun n => by unfold Cfg.Ry; rw [(hM n).2.1]; ring
  have hb : S.beta = S.alpha := funext fun n => by unfold Cfg.beta Cfg.alpha; rw [(hM n).2.2]
  rw [hPx, hPy, hRx, hRy, hb, Q2o_zero κ N, Q2o_eq_GH]
  ring

/-- Mirror sector, PSD side of Theorem A. -/
theorem thm_mirror_pos (Nc : ℕ) (u : ℝ) (hQ : PsdQu κ Nc u)
    (N : ℕ) (S : Cfg) (hU : S.Unit) (hM : S.Mirror) :
    0 ≤ energy κ Nc u N S ∧ (energy κ Nc u N S = 0 → S.NormalOn N) := by
  have hE := energy_mirror κ Nc u N S hU hM
  have t1 := hQ N S.xx
  have t2 := hQ N S.xy
  have t3 := lemma_odd_sq κ N S.alpha
  have t4 : 0 ≤ ∑ n ∈ range N, S.alpha n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  refine ⟨by rw [hE]; linarith, ?_⟩
  intro h0
  rw [hE] at h0
  have hs : ∑ n ∈ range N, S.alpha n ^ 2 = 0 := by linarith
  have hα := (sum_eq_zero_iff_of_nonneg (fun n _ => sq_nonneg (S.alpha n))).mp hs
  intro n hn
  have h1 : S.xz n = 1 := by
    have := hα n (mem_range.mpr hn)
    have h' : S.alpha n = 0 := (pow_eq_zero_iff two_ne_zero).mp this
    unfold Cfg.alpha at h'; linarith
  have h2 : S.ez n = 1 := by rw [(hM n).2.2]; exact h1
  obtain ⟨e1, _⟩ := hU n
  rw [h1] at e1
  have hxx : S.xx n = 0 := by
    have h : S.xx n ^ 2 = 0 := by nlinarith [sq_nonneg (S.xx n), sq_nonneg (S.xy n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  have hxy : S.xy n = 0 := by
    have h : S.xy n ^ 2 = 0 := by nlinarith [sq_nonneg (S.xx n), sq_nonneg (S.xy n)]
    exact (pow_eq_zero_iff two_ne_zero).mp h
  exact ⟨hxx, hxy, h1, by rw [(hM n).1]; exact hxx, by rw [(hM n).2.1]; exact hxy, h2⟩

/-! ### Tilt construction (negative direction) -/

/-- Mirror tilt with planar amplitude `b`: `ξ = η = (b, 0, √(1-b²))`. -/
noncomputable def Cfg.tilt (b : ℕ → ℝ) : Cfg :=
  ⟨b, fun _ => 0, fun n => Real.sqrt (1 - b n ^ 2), b, fun _ => 0,
    fun n => Real.sqrt (1 - b n ^ 2)⟩

theorem tilt_unit (b : ℕ → ℝ) (hb : ∀ n, b n ^ 2 ≤ 1) : (Cfg.tilt b).Unit := by
  intro n
  have h := Real.sq_sqrt (show 0 ≤ 1 - b n ^ 2 by linarith [hb n])
  constructor
  · show b n ^ 2 + (0 : ℝ) ^ 2 + Real.sqrt (1 - b n ^ 2) ^ 2 = 1
    rw [h]; ring
  · show b n ^ 2 + (0 : ℝ) ^ 2 + Real.sqrt (1 - b n ^ 2) ^ 2 = 1
    rw [h]; ring

theorem tilt_mirror (b : ℕ → ℝ) : (Cfg.tilt b).Mirror := fun _ => ⟨rfl, rfl, rfl⟩

theorem tilt_alpha_bounds (b : ℕ → ℝ) (hb : ∀ n, b n ^ 2 ≤ 1) (n : ℕ) :
    0 ≤ (Cfg.tilt b).alpha n ∧ (Cfg.tilt b).alpha n ≤ b n ^ 2 := by
  have h := Real.sq_sqrt (show 0 ≤ 1 - b n ^ 2 by linarith [hb n])
  have h0 := Real.sqrt_nonneg (1 - b n ^ 2)
  show 0 ≤ 1 - Real.sqrt (1 - b n ^ 2) ∧ 1 - Real.sqrt (1 - b n ^ 2) ≤ b n ^ 2
  generalize Real.sqrt (1 - b n ^ 2) = z at h h0 ⊢
  have hz1 : z ≤ 1 := by nlinarith [sq_nonneg (b n)]
  have hz2 : 1 - b n ^ 2 ≤ z := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hz1)]
  constructor <;> linarith

theorem Q2u_smul (Nc : ℕ) (u : ℝ) (N : ℕ) (ε : ℝ) (a : ℕ → ℝ) :
    Q2u κ Nc u N (fun n => ε * a n) = ε ^ 2 * Q2u κ Nc u N a := by
  unfold Q2u bil
  have h1 : ∑ n ∈ range N, c κ n * (ε * a n) ^ 2 = ε ^ 2 * ∑ n ∈ range N, c κ n * a n ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  have h2 : ∑ n ∈ range N, ∑ m ∈ range N, W κ n m * (ε * a n) * (ε * a m)
      = ε ^ 2 * ∑ n ∈ range N, ∑ m ∈ range N, W κ n m * a n * a m := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have h3 : ∑ n ∈ range N, chi Nc n * (ε * a n) = ε * ∑ n ∈ range N, chi Nc n * a n := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  rw [h1, h2, h3]; ring

theorem Q2u_congr (Nc : ℕ) (u : ℝ) (N : ℕ) {a b : ℕ → ℝ} (h : ∀ n < N, a n = b n) :
    Q2u κ Nc u N a = Q2u κ Nc u N b := by
  unfold Q2u bil
  have e1 : ∑ n ∈ range N, c κ n * a n ^ 2 = ∑ n ∈ range N, c κ n * b n ^ 2 :=
    sum_congr rfl fun n hn => by rw [h n (mem_range.mp hn)]
  have e2 : ∑ n ∈ range N, ∑ m ∈ range N, W κ n m * a n * a m
      = ∑ n ∈ range N, ∑ m ∈ range N, W κ n m * b n * b m :=
    sum_congr rfl fun n hn => sum_congr rfl fun m hm => by
      rw [h n (mem_range.mp hn), h m (mem_range.mp hm)]
  have e3 : ∑ n ∈ range N, chi Nc n * a n = ∑ n ∈ range N, chi Nc n * b n :=
    sum_congr rfl fun n hn => by rw [h n (mem_range.mp hn)]
  rw [e1, e2, e3]

/-- Quartic bound for `Q^o` on small nonnegative vectors. -/
theorem Q2o_le (N : ℕ) (α γ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ α n) (h1 : ∀ n, α n ≤ γ n) :
    Q2o κ N α ≤ ∑ n ∈ range N, c κ n * γ n ^ 2 + κ.K 1 * (∑ n ∈ range N, γ n) ^ 2 := by
  rw [Q2o_eq_GH]
  unfold Gform
  have hT : 0 ≤ bil (T κ) N α α :=
    sum_nonneg fun n _ => sum_nonneg fun m _ =>
      mul_nonneg (mul_nonneg (T_nonneg κ n m) (h0 n)) (h0 m)
  have hc : ∑ n ∈ range N, c κ n * α n ^ 2 ≤ ∑ n ∈ range N, c κ n * γ n ^ 2 :=
    sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
      (by nlinarith [h0 n, h1 n]) (c_pos κ n).le
  have hH : bil (H κ) N α α ≤ κ.K 1 * (∑ n ∈ range N, γ n) ^ 2 := by
    have hS0 : 0 ≤ ∑ n ∈ range N, α n := sum_nonneg fun n _ => h0 n
    have hS : ∑ n ∈ range N, α n ≤ ∑ n ∈ range N, γ n := sum_le_sum fun n _ => h1 n
    calc bil (H κ) N α α ≤ ∑ n ∈ range N, ∑ m ∈ range N, κ.K 1 * (α n * α m) := by
          unfold bil
          refine sum_le_sum fun n _ => sum_le_sum fun m _ => ?_
          have h2 : H κ n m ≤ κ.K 1 := κ.anti (by omega)
          have h3 : H κ n m * (α n * α m) ≤ κ.K 1 * (α n * α m) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (h0 n) (h0 m))
          linarith [h3]
      _ = κ.K 1 * (∑ n ∈ range N, α n) ^ 2 := by
          rw [sq, sum_mul_sum, mul_sum]
          exact sum_congr rfl fun n _ => by rw [mul_sum]
      _ ≤ κ.K 1 * (∑ n ∈ range N, γ n) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (κ.pos 1).le
  have : bil (T κ) N α α = ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * α n * α m := rfl
  linarith

/-- Mirror sector, negative side of Theorem A: a non-PSD `Q_u` yields a mirror configuration
with strictly negative energy. -/
theorem thm_mirror_neg (Nc : ℕ) (u : ℝ) (h : ¬ PsdQu κ Nc u) :
    ∃ (N : ℕ) (S : Cfg), S.Unit ∧ S.Mirror ∧ energy κ Nc u N S < 0 := by
  unfold PsdQu at h
  push Not at h
  obtain ⟨N, a0, ha0⟩ := h
  obtain ⟨a, hasupp, haeq⟩ : ∃ a : ℕ → ℝ, (∀ n, N ≤ n → a n = 0) ∧ (∀ n < N, a n = a0 n) :=
    ⟨fun n => if n < N then a0 n else 0, fun n hn => by simp [not_lt.mpr hn],
      fun n hn => by simp [hn]⟩
  have hQa : Q2u κ Nc u N a < 0 := by
    rw [Q2u_congr κ Nc u N haeq]; exact ha0
  set q : ℝ := -Q2u κ Nc u N a with hq
  have hqpos : 0 < q := by rw [hq]; linarith
  set A : ℝ := ∑ n ∈ range N, a n ^ 2 with hA
  have hA0 : 0 ≤ A := sum_nonneg fun n _ => sq_nonneg _
  set C : ℝ := ∑ n ∈ range N, c κ n * (a n ^ 2) ^ 2 + κ.K 1 * A ^ 2 with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∑ n ∈ range N, c κ n * (a n ^ 2) ^ 2 :=
      sum_nonneg fun n _ => mul_nonneg (c_pos κ n).le (sq_nonneg _)
    have := mul_nonneg (κ.pos 1).le (sq_nonneg A)
    rw [hC]; linarith
  set δ : ℝ := min (q / (2 * (C + 1))) (1 / (1 + A)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ * (C + 1) ≤ q / 2 := by
    have h1 : δ ≤ q / (2 * (C + 1)) := min_le_left _ _
    have h2 : 0 < 2 * (C + 1) := by positivity
    have := (le_div_iff₀ h2).mp h1
    linarith
  have hδ2 : δ * (1 + A) ≤ 1 := by
    have h1 : δ ≤ 1 / (1 + A) := min_le_right _ _
    exact (le_div_iff₀ (by positivity)).mp h1
  set ε : ℝ := Real.sqrt δ with hε
  have hε2 : ε ^ 2 = δ := Real.sq_sqrt hδpos.le
  have han : ∀ n, a n ^ 2 ≤ A := by
    intro n
    by_cases hn : n < N
    · exact single_le_sum (f := fun n => a n ^ 2) (fun m _ => sq_nonneg _) (mem_range.mpr hn)
    · rw [hasupp n (not_lt.mp hn)]; simpa using hA0
  set b : ℕ → ℝ := fun n => ε * a n with hb
  have hbsq : ∀ n, b n ^ 2 = δ * a n ^ 2 := fun n => by
    simp only [hb]; rw [mul_pow, hε2]
  have hb1 : ∀ n, b n ^ 2 ≤ 1 := by
    intro n
    rw [hbsq n]
    have h1 : δ * a n ^ 2 ≤ δ * A := mul_le_mul_of_nonneg_left (han n) hδpos.le
    nlinarith
  refine ⟨N, Cfg.tilt b, tilt_unit b hb1, tilt_mirror b, ?_⟩
  rw [energy_mirror κ Nc u N _ (tilt_unit b hb1) (tilt_mirror b)]
  have hx : Q2u κ Nc u N (Cfg.tilt b).xx = -(δ * q) := by
    show Q2u κ Nc u N (fun n => ε * a n) = _
    rw [Q2u_smul, hε2, hq]; ring
  have hy : Q2u κ Nc u N (Cfg.tilt b).xy = 0 := Q2u_zero κ Nc u N
  have hα := Q2o_le κ N (Cfg.tilt b).alpha (fun n => b n ^ 2)
    (fun n => (tilt_alpha_bounds b hb1 n).1) (fun n => (tilt_alpha_bounds b hb1 n).2)
  have hs1 : ∑ n ∈ range N, c κ n * (b n ^ 2) ^ 2 = δ ^ 2 * ∑ n ∈ range N, c κ n * (a n ^ 2) ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by rw [hbsq n]; ring
  have hs2 : ∑ n ∈ range N, b n ^ 2 = δ * A := by
    rw [hA, mul_sum]
    exact sum_congr rfl fun n _ => hbsq n
  rw [hx, hy]
  rw [hs1, hs2] at hα
  have hfin : δ ^ 2 * ∑ n ∈ range N, c κ n * (a n ^ 2) ^ 2 + κ.K 1 * (δ * A) ^ 2 = δ ^ 2 * C := by
    rw [hC]; ring
  have hmul := mul_le_mul_of_nonneg_left hδ1 hδpos.le
  have hlt : δ ^ 2 * C ≤ δ * (q / 2) := by nlinarith [sq_nonneg δ]
  have hdq := mul_pos hδpos hqpos
  linarith

/-- **Theorem A.**  In the mirror sector the normal state is a global minimiser iff `Q_u` is PSD
(and then it is the unique global minimiser). -/
theorem thm_mirror (Nc : ℕ) (u : ℝ) :
    PsdQu κ Nc u ↔ ∀ (N : ℕ) (S : Cfg), S.Unit → S.Mirror → 0 ≤ energy κ Nc u N S := by
  constructor
  · intro hQ N S hU hM
    exact (thm_mirror_pos κ Nc u hQ N S hU hM).1
  · intro hmin
    by_contra hnot
    obtain ⟨N, S, hU, hM, hneg⟩ := thm_mirror_neg κ Nc u hnot
    exact absurd (hmin N S hU hM) (not_le.mpr hneg)

end MuStar
