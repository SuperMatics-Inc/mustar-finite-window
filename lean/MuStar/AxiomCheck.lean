import MuStar

/-!
Axiom audit.  Every main theorem must depend only on `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`, no custom axiom).
-/

#print axioms MuStar.lemma_odd
#print axioms MuStar.lemma_odd_sq
#print axioms MuStar.energy_I2
#print axioms MuStar.thm_unique
#print axioms MuStar.not_psdQu_mono
#print axioms MuStar.thm_mirror_pos
#print axioms MuStar.thm_mirror_neg
#print axioms MuStar.thm_mirror
#print axioms MuStar.tail_psd
#print axioms MuStar.linSet_subset_negSet
#print axioms MuStar.negSet_subset
#print axioms MuStar.threshold_eq
#print axioms MuStar.threshold_persist
