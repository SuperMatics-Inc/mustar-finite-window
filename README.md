# Linear versus global stability in a Coulomb-penalized Matsubara spin chain

Davis Rens, SuperMatics Inc. Software supplement for
[SuperMatics-Inc/mustar-finite-window](https://github.com/SuperMatics-Inc/mustar-finite-window), version 1.0.0.
DOI: [10.5281/zenodo.24326113](https://doi.org/10.5281/zenodo.24326113).

## Results and hypotheses

In the mirror sector of the finite-window Matsubara spin chain, a nonnegative pairing form is equivalent to global stability and uniqueness of the normal state. The two criteria can separate outside the mirror sector. The model uses the normal-state-subtracted Einstein-kernel energy for unit spins and a symmetric transverse Coulomb penalty restricted to the window in both indices. Its weighted finite-defect domain allows nonplanar spins, violations of the mirror relation `eta = xi`, and longitudinal reversals.

The written proof separates the energy into even, odd and longitudinal-defect terms. It includes the semidefinite case in the mirror sector. In the unrestricted class, positivity of both the pairing form and the longitudinal form suffices for unique global normal-state minimization. With compactness, a uniformly positive Hessian on `[T1,T2]`, a negative witness at `T1` and global positivity above `T2`, the last global-stability boundary has separated coexistence. The quantitative separation holds on `[T1,T2]`.

Interval calculations certify sufficient ranges `0 <= mu* <= u1` for equality of the last linear and global negative-energy suprema at twenty fixed-index and sixteen fixed-frequency parameter cells. The search caps were 1 and 2, respectively. The resulting endpoints are sufficient bounds, not optima or interpolants between couplings. The cap of 1 in Table 2 of the report was used in the exploratory search that selected `GRID` in `scripts/certify_threshold.py`. That search and the generators of the exploratory `data/numeric_*.json` files are not included.

At `lambda = 8`, fixed index window `Nc = 5`, and `mu* = 20`, the certificates show that the normal Hessian is strictly positive for every `T >= 1/40`, even though finite-support competitors have negative energy. In that temperature range every negative-energy state violates `eta = xi`. The last boundary satisfies `1/37 < T* <= 4/13`. Certified competitors with 64 sites per half have lower energy than the initial witness with 40 sites per half.

The counterexample uses longitudinal reversals and an extreme pseudopotential. It establishes a property of the spin model; it does not predict a physical first-order transition, latent heat or a material property. The weighted no-flip diagnostics and 240-cell multistart searches are exploratory. They give neither a causal no-flip counterexample nor a no-flip nonexistence theorem. There are no experimental data.

## Reproduce the certificates

With Python 3.13 and uv, from the repository root:

```sh
uv run --no-project --with numpy --with scipy --with mpmath --with python-flint --with sympy python scripts/replay.py
```

Alternatively install `requirements.txt` in an isolated environment and run `python scripts/replay.py`. All ten child processes must exit 0. The independent verifier runs 87 checks, including 21 perturbations of inputs or claims as negative controls, and must report `TOTAL: 0 failed checks`. The controls leave the code unchanged. The driver limits BLAS to one thread and writes logs to `logs/`. Inputs and regenerated outputs are in `scripts/`; `certificates/` holds the reference outputs and their checksums.

The primary calculations use Arb ball arithmetic. Floating-point Cholesky factors supply candidates, and interval residual bounds and explicit infinite-tail estimates establish positivity. The independent verifier uses interval kernel bounds and shifted Cholesky residual bounds, with an explicit allowance for binary64 roundoff. Its conclusions depend on that library error model. The binary64 values in the JSON files display interval centres rather than exact outward enclosures.

To regenerate the interval map:

```sh
uv run --no-project --with numpy --with matplotlib python scripts/plot_certified_intervals.py
```

The script loads `figures/pub.mplstyle` and writes a vector PDF and PNG from the 36 committed certified cell limits. No interpolation or new parameter search is performed.

## Lean scope

The modules in `lean/` use Lean 4.35.0 and Mathlib v4.35.0. They formalize the finite-block arguments and the conditional implications listed below.

| Module | Formalized scope | Not covered |
|---|---|---|
| `Defs`, `Sums`, `I2` | Abstract positive antitone kernel, finite-support/block energy, odd-square positivity and exact unit-spin algebra | Infinite-sum identification and extension to the weighted domain |
| `Unique`, `Mirror` | All-finite-block two-form implication, mirror comparison and constructive small-tilt instability | Infinite-chain closure and compactness |
| `Tail` | Abstract all-finite-section Schur-tail implication with explicit hypotheses | Concrete Einstein-kernel interval arithmetic |
| `Threshold` | Conditional set inclusions and supremum equality with explicit boundedness and ordering hypotheses | Temperature analysis, attainment, separation and coexistence |
| `AxiomCheck` | Thirteen theorem axiom reports | Full-paper formalization |

With elan installed, run `lake exe cache get` in `lean/` to fetch the precompiled Mathlib files. Then run `lake build MuStar.AxiomCheck` and `lake env lean MuStar/AxiomCheck.lean`. The expected axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`, with no custom axiom or `sorry`. The supplied `lake-manifest.json` records the dependency revisions used by GitHub Actions.

## Contents and citation

The accompanying paper is SuperMatics Technical Report SM-TR-2026-03, [10.5281/zenodo.24326111](https://doi.org/10.5281/zenodo.24326111), distributed separately. `figures/` contains the interval map and its style file. The authored code, Lean sources, inputs, certificates, figures and documentation are licensed under Apache-2.0. Dependencies retain their own licenses. Cite this supplement as [10.5281/zenodo.24326113](https://doi.org/10.5281/zenodo.24326113), using `CITATION.cff`.

The companion bounds paper is [arXiv:2611.20496](https://arxiv.org/abs/2611.20496), with software at [10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482). The companion preprint *Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion* is available at [10.5281/zenodo.24326099](https://doi.org/10.5281/zenodo.24326099).

## AI use

AI agents generated proofs, certificates, code, Lean sources and manuscript drafts and edits under Davis Rens's direction and review. No AI agent is an author.
