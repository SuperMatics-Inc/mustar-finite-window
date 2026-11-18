import MuStar.Mirror

/-!
# Threshold corollary (paper Corollary `cor:threshold`)

For a temperature-indexed family of kernels `κ T` (and a temperature-dependent index cutoff
`Nc T`, which covers both the fixed-index and the fixed-frequency settings), put

* `I u = {T | ¬ PsdQu (κ T) (Nc T) u}`  (linear instability),
* `J   = {T | ¬ PsdG (κ T)}`  (the `G` form fails to be PSD),
* `F u = {T | ∃ N S, S.Unit ∧ energy < 0}` (a unit-spin configuration with negative energy).

Theorem A gives `I ⊆ F` and Theorem C gives `F ⊆ I ∪ J`.  Hence, when `J` lies strictly
below `sup I`, the thermodynamic transition temperature `sup F` equals the linear threshold
`sup I`, and a negative direction at `u₁` at a temperature `T_b` above `J` pins the equality
for every `u ≤ u₁`.
-/

open Finset

namespace MuStar

/-- Linear-instability set. -/
def linSet (κ : ℝ → Kernel) (Nc : ℝ → ℕ) (u : ℝ) : Set ℝ := {T | ¬ PsdQu (κ T) (Nc T) u}

/-- `G`-instability set. -/
def gSet (κ : ℝ → Kernel) : Set ℝ := {T | ¬ PsdG (κ T)}

/-- Set of temperatures at which some unit-spin configuration has negative energy. -/
def negSet (κ : ℝ → Kernel) (Nc : ℝ → ℕ) (u : ℝ) : Set ℝ :=
  {T | ∃ (N : ℕ) (S : Cfg), S.Unit ∧ energy (κ T) (Nc T) u N S < 0}

theorem linSet_subset_negSet (κ : ℝ → Kernel) (Nc : ℝ → ℕ) (u : ℝ) :
    linSet κ Nc u ⊆ negSet κ Nc u := by
  intro T hT
  obtain ⟨N, S, hU, _, hneg⟩ := thm_mirror_neg (κ T) (Nc T) u hT
  exact ⟨N, S, hU, hneg⟩

theorem negSet_subset (κ : ℝ → Kernel) (Nc : ℝ → ℕ) (u : ℝ) :
    negSet κ Nc u ⊆ linSet κ Nc u ∪ gSet κ := by
  intro T ⟨N, S, hU, hneg⟩
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hQ : PsdQu (κ T) (Nc T) u := not_not.mp h1
  have hG : PsdG (κ T) := not_not.mp h2
  exact absurd (thm_unique (κ T) (Nc T) u hQ hG N S hU).1 (not_le.mpr hneg)

/-- **Corollary D (first assertion).**  If every `T` with `¬PsdG` lies strictly below
`sSup I`, then `sSup F = sSup I`. -/
theorem threshold_eq (κ : ℝ → Kernel) (Nc : ℝ → ℕ) (u : ℝ)
    (hne : (linSet κ Nc u).Nonempty) (hbdd : BddAbove (linSet κ Nc u))
    (hJ : ∀ T ∈ gSet κ, T < sSup (linSet κ Nc u)) :
    sSup (negSet κ Nc u) = sSup (linSet κ Nc u) := by
  have hFne : (negSet κ Nc u).Nonempty := hne.mono (linSet_subset_negSet κ Nc u)
  apply le_antisymm
  · refine csSup_le hFne fun T hT => ?_
    rcases negSet_subset κ Nc u hT with h | h
    · exact le_csSup hbdd h
    · exact (hJ T h).le
  · have hbddF : BddAbove (negSet κ Nc u) := by
      refine ⟨sSup (linSet κ Nc u), fun T hT => ?_⟩
      rcases negSet_subset κ Nc u hT with h | h
      · exact le_csSup hbdd h
      · exact (hJ T h).le
    exact csSup_le_csSup hbddF hne (linSet_subset_negSet κ Nc u)

/-- **Corollary D (persistence).**  If `Q_{u₁}` has a negative direction at `T_b` and `G` is
PSD at every temperature `≥ T_b`, then for every `u ≤ u₁` (with a finite linear threshold)
the transition temperature equals the linear threshold. -/
theorem threshold_persist (κ : ℝ → Kernel) (Nc : ℝ → ℕ) {u₁ : ℝ} (Tb : ℝ)
    (hb : Tb ∈ linSet κ Nc u₁) (hG : ∀ T, Tb ≤ T → PsdG (κ T))
    (u : ℝ) (hu : u ≤ u₁) (hbdd : BddAbove (linSet κ Nc u)) :
    sSup (negSet κ Nc u) = sSup (linSet κ Nc u) := by
  have hTb : Tb ∈ linSet κ Nc u := not_psdQu_mono (κ Tb) (Nc Tb) hu hb
  have hne : (linSet κ Nc u).Nonempty := ⟨Tb, hTb⟩
  refine threshold_eq κ Nc u hne hbdd fun T hT => ?_
  have hlt : T < Tb := by
    by_contra hcon
    exact hT (hG T (not_lt.mp hcon))
  exact lt_of_lt_of_le hlt (le_csSup hbdd hTb)

end MuStar
