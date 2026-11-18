# Linear versus global stability in a Coulomb-penalized Matsubara spin chain

Davis Rens, SuperMatics Inc. Software supplement for
[SuperMatics-Inc/mustar-finite-window](https://github.com/SuperMatics-Inc/mustar-finite-window), version 1.0.0.
DOI: [10.5281/zenodo.24326113](https://doi.org/10.5281/zenodo.24326113).

## Results and hypotheses

The energy is the normal-state-subtracted Einstein-kernel unit-spin functional with a symmetric, both-index finite-window transverse Coulomb penalty. Its weighted finite-defect domain permits nonplanar, mirror-breaking and longitudinally reversed spins. The mirror relation is `eta = xi`.

- **PROVED:** An exact even/odd/longitudinal-defect decomposition. In the mirror sector, positivity of the pairing form is equivalent to global normal-state stability and uniqueness, including semidefinite boundary cases.
- **PROVED:** In the unrestricted spin class, positivity of both the pairing form and the longitudinal form suffices for unique global normal-state minimization. With compactness, a uniformly positive Hessian on `[T1,T2]`, a negative witness at `T1` and global positivity above `T2`, a last global-stability boundary has separated coexistence. The quantitative separation applies on `[T1,T2]`, not at arbitrary lower temperatures.
- **CERTIFIED:** Twenty fixed-index and sixteen fixed-frequency coupling/window cells give sufficient intervals `0 <= mu* <= u1` for equality of the last linear and global negative-energy suprema. Search caps are 1 and 2 respectively. These limits are not optimal endpoints and do not interpolate between couplings.
- **CERTIFIED:** At `lambda = 8`, fixed index window `Nc = 5`, and `mu* = 20`, the normal Hessian is strictly positive for every `T >= 1/40`, yet finite-support competitors have negative energy. Every negative-energy state in that temperature range breaks the mirror relation. The last boundary satisfies `1/37 < T* <= 4/13`. The initial 40-site-per-half witness is not minimizing; certified 64-site-per-half competitors have lower energy.
- **NUMERICAL:** Weighted no-flip diagnostics and 240-cell multistart searches. No causal/no-flip counterexample or no-flip nonexistence theorem is established. Stored search outputs are exploratory data, not interval certificates.

The fixed-index search cap of 1 (manuscript Table 2) is the exploratory selection limit used to assemble the hard-coded `GRID` in `scripts/certify_threshold.py`, not a computed optimal endpoint. The original exploratory search that selected that grid is not shipped. The generators of the retained exploratory `data/numeric_*.json` outputs are also not shipped; certificate reproduction does not regenerate those numerical searches.

The counterexample has longitudinal reversals and an extreme pseudopotential. It is a spin-model result, not a physical first-order superconducting-transition prediction, latent-heat calculation or materials claim. No experimental or measured data occur here.

## Reproduce the certificates

With Python 3.13 and uv, from the repository root:

```sh
uv run --no-project --with numpy --with scipy --with mpmath --with python-flint --with sympy python scripts/replay.py
```

Alternatively install `requirements.txt` in an isolated environment, then run `python scripts/replay.py`. All ten child processes must exit 0. The independent verifier runs 87 checks, including 21 negative-control input/claim perturbations, and must report `TOTAL: 0 failed checks`. These are not code mutation tests. The driver limits BLAS threads to one and writes execution records into a newly created `logs/` directory. Inputs and regenerated outputs are in `scripts/`; `certificates/` holds reference outputs and content hashes; `data/` holds witness and numerical-search data.

Primary certificates use Arb ball arithmetic. Floating Cholesky factors propose certificates; interval residual bounds and explicit infinite-tail estimates establish positivity. The independent verifier uses interval kernel bounds and shifted Cholesky residual bounds with an explicit binary64 roundoff allowance; that numerical-library error model is part of its trust base. Binary64 interval displays stored in JSON are diagnostic centers, not exact standalone outward enclosures.

To regenerate the interval map:

```sh
uv run --no-project --with numpy --with matplotlib python scripts/plot_certified_intervals.py
```

The script loads `figures/pub.mplstyle` and writes a vector PDF and PNG from the 36 committed certified cell limits. No interpolation or new parameter search is performed.

## Lean scope

Lean 4.35.0 and Mathlib at git revision `v4.35.0` are specified in `lean/`. The formalization is selective, not a machine proof of the whole paper.

| Module | Formalized scope | Not covered |
|---|---|---|
| `Defs`, `Sums`, `I2` | Abstract positive antitone kernel, finite-support/block energy, odd-square positivity and exact unit-spin algebra | Infinite-sum identification and extension to the weighted domain |
| `Unique`, `Mirror` | All-finite-block two-form implication, mirror comparison and constructive small-tilt instability | Infinite-chain closure and compactness |
| `Tail` | Abstract all-finite-section Schur-tail implication with explicit hypotheses | Concrete Einstein-kernel interval arithmetic |
| `Threshold` | Conditional set inclusions and supremum equality with explicit boundedness and ordering hypotheses | Temperature analysis, attainment, separation and coexistence |
| `AxiomCheck` | Thirteen theorem axiom reports | Full-paper formalization |

With elan installed, inside `lean/` use `lake exe cache get`, then `lake build MuStar.AxiomCheck` and `lake env lean MuStar/AxiomCheck.lean`. Acquire precompiled Mathlib artifacts first. Expected axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`, with no custom axiom or `sorry`. A resolved `lake-manifest.json` is supplied; CI builds it on GitHub. Earlier builds of the proof-bearing sources used a local Mathlib path. Subsequent edits to `Defs.lean` change only a documentation link, not declarations or proofs.

## Contents and citation

This software tree contains no manuscript sources or manuscript PDF. The accompanying paper is SuperMatics Technical Report **SM-TR-2026-03**, [10.5281/zenodo.24326111](https://doi.org/10.5281/zenodo.24326111). `figures/` contains the generated summary map and its style. Authored code, Lean sources, inputs, certificates, figures and documentation are licensed under Apache-2.0; dependencies retain their own licenses. Cite this software supplement as [10.5281/zenodo.24326113](https://doi.org/10.5281/zenodo.24326113), using `CITATION.cff`.

The companion bounds paper is [arXiv:2611.20496](https://arxiv.org/abs/2611.20496), with supplement [10.5281/zenodo.24270482](https://doi.org/10.5281/zenodo.24270482). The merged companion, *Global uniqueness of the superconducting state in multiband and anisotropic Eliashberg models without Coulomb repulsion*, is a Zenodo preprint, [10.5281/zenodo.24326099](https://doi.org/10.5281/zenodo.24326099). The hidden-convexity companion is submitted and is not on arXiv.
