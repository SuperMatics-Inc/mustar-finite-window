# Selective Lean formalization

Lean 4.35.0 / Mathlib v4.35.0; autoImplicit=false; maxMemory=4096 MB. Modules: Defs (kernel, block energy), Sums (odd-square bound), I2 (exact unit-spin decomposition), Unique (two-form criterion), Mirror (both directions including small-tilt construction), Tail (abstract all-finite-block Schur bound), Threshold (negative-set inclusions and conditional supremum equality), AxiomCheck (13 theorem axiom reports).

The standalone release specifies a portable Mathlib git requirement at v4.35.0. A resolved lake-manifest.json is supplied; CI builds it on GitHub. Earlier builds of the proof-bearing sources used a local Mathlib path. Subsequent edits to Defs.lean change only a documentation link, not declarations or proofs. With elan installed, in this directory:

```sh
lake exe cache get
lake build MuStar.AxiomCheck
lake env lean MuStar/AxiomCheck.lean
```

Acquire precompiled Mathlib artifacts first. Expected axiom lists contain only propext, Classical.choice and Quot.sound; no sorry, custom axiom or native_decide is used.

These are finite-support/block proofs, not a formalization of the entire infinite-chain paper. Infinite-sum identification, exterior padding, AZ form closure, coercivity/compactness/attainment, separation and coexistence remain written arguments. Concrete tail bounds and certificate arithmetic are not Lean-checked. Threshold boundedness and G-set ordering are explicit hypotheses; arbitrary temperature-dependent cutoff functions are supported. The root README gives the module scope table and numerical trust bases.
