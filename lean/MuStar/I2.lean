import MuStar.Sums

/-!
# The exact identity (paper Proposition `prop:I2`)

For every block `N` and every unit-spin configuration `S`,
`E = 2Q_u(P) + 2Q^o(R) + ½ G(α) + ½ G(β) + ⟨α, H β⟩`
with `P = (ξ^⊥ + η^⊥)/2`, `R = (ξ^⊥ - η^⊥)/2`, `α = 1 - ξ^z`, `β = 1 - η^z`.
-/

open Finset

namespace MuStar

variable (κ : Kernel)

namespace Cfg
/-- `P^x = (ξ^x + η^x)/2`. -/
noncomputable def Px (S : Cfg) (n : ℕ) : ℝ := (S.xx n + S.ex n) / 2
/-- `P^y = (ξ^y + η^y)/2`. -/
noncomputable def Py (S : Cfg) (n : ℕ) : ℝ := (S.xy n + S.ey n) / 2
/-- `R^x = (ξ^x - η^x)/2`. -/
noncomputable def Rx (S : Cfg) (n : ℕ) : ℝ := (S.xx n - S.ex n) / 2
/-- `R^y = (ξ^y - η^y)/2`. -/
noncomputable def Ry (S : Cfg) (n : ℕ) : ℝ := (S.xy n - S.ey n) / 2
end Cfg

/-- Ordered pairs `n < m` versus the symmetric full double sum with `T`. -/
theorem pair_eq (N : ℕ) (g : ℕ → ℕ → ℝ) (hg : ∀ n m, g n m = g m n) :
    ∑ n ∈ range N, ∑ m ∈ (range N).filter (fun m => n < m), κ.K (m - n) * g n m
      = (1 / 2) * ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * g n m := by
  have hT : ∀ n m, T κ n m * g n m
      = (if n < m then κ.K (m - n) * g n m else 0)
        + (if m < n then κ.K (n - m) * g n m else 0) := by
    intro n m
    unfold T
    by_cases h1 : n < m
    · have h2 : ¬ m < n := by omega
      simp [h1, h2]
    · by_cases h2 : m < n
      · simp [h1, h2]
      · simp [h1, h2]
  have hA : ∑ n ∈ range N, ∑ m ∈ (range N).filter (fun m => n < m), κ.K (m - n) * g n m
      = ∑ n ∈ range N, ∑ m ∈ range N, (if n < m then κ.K (m - n) * g n m else 0) :=
    sum_congr rfl fun n _ => sum_filter _ _
  have hB : ∑ n ∈ range N, ∑ m ∈ range N, (if m < n then κ.K (n - m) * g n m else 0)
      = ∑ n ∈ range N, ∑ m ∈ range N, (if n < m then κ.K (m - n) * g n m else 0) := by
    refine sum_comm.trans ?_
    exact sum_congr rfl fun n _ => sum_congr rfl fun m _ => by rw [hg m n]
  have hTot : ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * g n m
      = ∑ n ∈ range N, ∑ m ∈ range N, (if n < m then κ.K (m - n) * g n m else 0)
        + ∑ n ∈ range N, ∑ m ∈ range N, (if m < n then κ.K (n - m) * g n m else 0) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => hT n m
  rw [hA, hTot, hB]
  ring

/-- Pointwise combination whose double sum vanishes (see `energy_I2`). -/
noncomputable def Psi (S : Cfg) (n m : ℕ) : ℝ :=
  H κ n m * (S.alpha n + S.beta n)
  + (1 / 2) * (T κ n m * (2 - (S.xx n * S.xx m + S.xy n * S.xy m + S.xz n * S.xz m)
                            - (S.ex n * S.ex m + S.ey n * S.ey m + S.ez n * S.ez m)))
  + W κ n m * S.Px n * S.Px m + W κ n m * S.Py n * S.Py m
  + Dm κ n m * S.Rx n * S.Rx m + Dm κ n m * S.Ry n * S.Ry m
  + (1 / 2) * (T κ n m * S.alpha n * S.alpha m) + (1 / 2) * (T κ n m * S.beta n * S.beta m)
  - T κ n m * (S.alpha n + S.beta n)
  - H κ n m * (1 + (S.xx n * S.ex m + S.xy n * S.ey m) - S.xz n * S.ez m)
  - H κ n m * S.alpha n * S.beta m

/-- The antisymmetric form that `Psi` equals pointwise. -/
noncomputable def Phi (S : Cfg) (n m : ℕ) : ℝ :=
  (1 / 2) * T κ n m * (S.alpha m - S.alpha n + S.beta m - S.beta n)
  + H κ n m * (S.beta n - S.beta m + S.Px n * S.Rx m + S.Py n * S.Ry m
                - S.Rx n * S.Px m - S.Ry n * S.Py m)

theorem Psi_eq_Phi (S : Cfg) (n m : ℕ) : Psi κ S n m = Phi κ S n m := by
  unfold Psi Phi W Dm Cfg.alpha Cfg.beta Cfg.Px Cfg.Py Cfg.Rx Cfg.Ry
  ring

theorem Phi_antisymm (S : Cfg) (n m : ℕ) : Phi κ S n m = -Phi κ S m n := by
  unfold Phi
  rw [T_symm κ m n, H_symm κ m n]
  ring

theorem sum_Psi (N : ℕ) (S : Cfg) : ∑ n ∈ range N, ∑ m ∈ range N, Psi κ S n m = 0 := by
  rw [sum_congr rfl fun n _ => sum_congr rfl fun m _ => Psi_eq_Phi κ S n m]
  exact sum_antisymm N _ (Phi_antisymm κ S)

/-- **Proposition (exact identity).**  For every block and every unit-spin configuration,
`E = 2Q_u(P) + 2Q^o(R) + ½ G(α) + ½ G(β) + ⟨α, Hβ⟩`. -/
theorem energy_I2 (Nc : ℕ) (u : ℝ) (N : ℕ) (S : Cfg) (hU : S.Unit) :
    energy κ Nc u N S =
      Q2u κ Nc u N S.Px + Q2u κ Nc u N S.Py + Q2o κ N S.Rx + Q2o κ N S.Ry
        + (1 / 2) * Gform κ N S.alpha + (1 / 2) * Gform κ N S.beta
        + bil (H κ) N S.alpha S.beta := by
  -- (1) free weights via the row-sum identity
  have hE1 : ∑ n ∈ range N, (w n + tailW κ N n) * (S.alpha n + S.beta n)
      = ∑ n ∈ range N, c κ n * (S.alpha n + S.beta n)
        - ∑ n ∈ range N, ∑ m ∈ range N, T κ n m * (S.alpha n + S.beta n)
        + ∑ n ∈ range N, ∑ m ∈ range N, H κ n m * (S.alpha n + S.beta n) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_mul, ← sum_mul]
    have hr := rowsum κ N n (mem_range.mp hn)
    have e : w n + tailW κ N n
        = c κ n - ∑ m ∈ range N, T κ n m + ∑ m ∈ range N, H κ n m := by
      unfold c; linarith
    rw [e]; ring
  -- (2) ordered pair sum as a symmetric double sum
  have hE2 : ∑ n ∈ range N, ∑ m ∈ (range N).filter (fun m => n < m),
      κ.K (m - n) * (2 - (S.xx n * S.xx m + S.xy n * S.xy m + S.xz n * S.xz m)
                       - (S.ex n * S.ex m + S.ey n * S.ey m + S.ez n * S.ez m))
      = (1 / 2) * ∑ n ∈ range N, ∑ m ∈ range N, T κ n m *
        (2 - (S.xx n * S.xx m + S.xy n * S.xy m + S.xz n * S.xz m)
           - (S.ex n * S.ex m + S.ey n * S.ey m + S.ez n * S.ez m)) :=
    pair_eq κ N (fun n m => 2 - (S.xx n * S.xx m + S.xy n * S.xy m + S.xz n * S.xz m)
                           - (S.ex n * S.ex m + S.ey n * S.ey m + S.ez n * S.ez m))
      (fun n m => by ring)
  -- (3) Hankel term
  have hE3 : ∑ n ∈ range N, ∑ m ∈ range N,
      κ.K (n + m + 1) * (1 + (S.xx n * S.ex m + S.xy n * S.ey m) - S.xz n * S.ez m)
      = ∑ n ∈ range N, ∑ m ∈ range N,
        H κ n m * (1 + (S.xx n * S.ex m + S.xy n * S.ey m) - S.xz n * S.ez m) := rfl
  -- (4) diagonal coefficients, using the unit constraint
  have hC : ∑ n ∈ range N, c κ n * (S.alpha n + S.beta n)
      = ∑ n ∈ range N, c κ n * S.Px n ^ 2 + ∑ n ∈ range N, c κ n * S.Py n ^ 2
        + ∑ n ∈ range N, c κ n * S.Rx n ^ 2 + ∑ n ∈ range N, c κ n * S.Ry n ^ 2
        + (1 / 2) * ∑ n ∈ range N, c κ n * S.alpha n ^ 2
        + (1 / 2) * ∑ n ∈ range N, c κ n * S.beta n ^ 2 := by
    have hpt : ∀ n ∈ range N, c κ n * (S.alpha n + S.beta n)
        = c κ n * S.Px n ^ 2 + c κ n * S.Py n ^ 2 + c κ n * S.Rx n ^ 2 + c κ n * S.Ry n ^ 2
          + (1 / 2) * (c κ n * S.alpha n ^ 2) + (1 / 2) * (c κ n * S.beta n ^ 2) := by
      intro n _
      obtain ⟨h1, h2⟩ := hU n
      unfold Cfg.Px Cfg.Py Cfg.Rx Cfg.Ry Cfg.alpha Cfg.beta
      linear_combination (-(1 / 2) * c κ n) * h1 + (-(1 / 2) * c κ n) * h2
    rw [sum_congr rfl hpt]
    simp only [sum_add_distrib, ← mul_sum]
  -- (5) Coulomb window
  have hcx : ∑ n ∈ range N, chi Nc n * (S.xx n + S.ex n)
      = 2 * ∑ n ∈ range N, chi Nc n * S.Px n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by unfold Cfg.Px; ring
  have hcy : ∑ n ∈ range N, chi Nc n * (S.xy n + S.ey n)
      = 2 * ∑ n ∈ range N, chi Nc n * S.Py n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by unfold Cfg.Py; ring
  -- (6) the vanishing double sum, expanded into atoms
  have hY := sum_Psi κ N S
  unfold Psi at hY
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hY
  unfold energy Q2u Q2o Gform bil
  rw [hcx, hcy]
  linarith [hE1, hE2, hE3, hC, hY]

end MuStar
