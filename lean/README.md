# Selective Lean formalization

The `MuStar` modules use Lean 4.35.0 and Mathlib v4.35.0, with `autoImplicit=false` and a 4096 MB memory limit. `Defs` defines the kernel and block energy. `Sums` proves the odd-square bound, and `I2` gives the exact unit-spin decomposition. `Unique` proves the two-form criterion, and `Mirror` proves both directions of the mirror criterion, including the small-tilt construction. `Tail` gives an abstract Schur bound for all finite blocks. `Threshold` proves negative-set inclusions and conditional supremum equality, and `AxiomCheck` reports the axioms of thirteen theorems.

With elan installed, run the following commands from this directory. The supplied `lake-manifest.json` records the dependency revisions used by GitHub Actions.

```sh
lake exe cache get
lake build MuStar.AxiomCheck
lake env lean MuStar/AxiomCheck.lean
```

The first command fetches precompiled Mathlib files. The expected axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`. The proofs use no `sorry`, custom axiom or `native_decide`.

The extension from finite support to the infinite chain remains a written argument. This includes identification of the infinite sums, exterior padding, AZ form closure, coercivity, compactness, attainment, separation and coexistence. The concrete tail estimates and interval calculations are separate from Lean. The threshold results assume boundedness and the stated ordering of the `G`-instability set, and allow arbitrary temperature-dependent cutoffs.
