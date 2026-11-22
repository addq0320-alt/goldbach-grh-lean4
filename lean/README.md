# Quaternionic spectral hypotheses for binary Goldbach — Lean 4 companion

**Lei · Version 1.0.0 · MIT license**

This project formalizes the spectral product, implications between norm and zero-free conditions, and selected lemmas in the subsequent analytic reductions. The global Dirichlet GRH estimates and the one-sided estimate for long prefixes are mathematical inputs or open problems in the paper. Read the assumptions in each declaration when using it.

## Reproduce the checks

Install Lean's elan toolchain manager and Git. From this directory (the one containing `lean-toolchain`), run:

```sh
lake exe cache get
lake build
lake env lean --trust=0 -DwarningAsError=true SpectralAudit.lean
lake env lean --trust=0 -DwarningAsError=true Audit.lean
```

The project uses Lean 4.19.0 with mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Lake reads all dependency revisions from `lake-manifest.json`. A fresh machine needs network access for the toolchain, dependencies and compiled mathlib cache. Compiled dependencies are excluded from the source archive.

The default target is `GoldbachResearch`. It imports all eleven analytic stage modules and the eight-module spectral core. The targeted spectral audit checks 28 explicitly named results. The project-wide audit inspects every theorem declaration whose root namespace belongs to the project and rejects transitive dependencies outside `propext`, `Classical.choice` and `Quot.sound`. The release run reported **287 declarations**, including generated helpers. The two audit counts overlap. The logs from the release build are in `verification/`.

## Finding the proofs

| Module or directory | Examples of what is checked |
| --- | --- |
| `GoldbachSpectral/Product.lean` | Summable infinite product, quaternionic slice, critical real part and the open half-space criterion. |
| `GoldbachSpectral/Obstruction.lean`, `WeakS.lean` | Norm dictionary, consequences of a supplied eigenvalue lower bound, and the rank-one weak-hypothesis model. |
| `GoldbachSpectral/KernelTest.lean`, `Cancellation.lean`, `Interior.lean`, `Covariance.lean`, `Buchstab.lean` | Dense finite tests, same-side cancellation, interior reflection, rank-one perturbations and a Buchstab-function lemma. |
| `GoldbachDefect`, `GoldbachFarey`, `GoldbachWindows` | Compact test families, exceptional-set deductions, finite Farey bookkeeping and window averages. |
| `GoldbachDuality` | Green-kernel identities, moment weights and steps in the dual formulation. |
| `GoldbachMinorArcs`, `GoldbachMellin` | Fourier identities, incidence and exponent bounds, convolution and Mellin reductions. |
| `GoldbachFreeLabels`, `GoldbachFiveModuli` | Matched-label estimates at the finite-algebra level, modulus counting and exponent arithmetic. |
| `GoldbachZeroCorrelations`, `GoldbachThreeRoutes` | Sampling and finite arrays, reflected convolution, phases and resolvent estimates. |
| `GoldbachSeparationSieve` | Weighted cell Cauchy–Schwarz, the Schur bound, the radial count, sieve tests, cutoff geometry and the weighted exceptional-set implication. |

For a direct entry point, look up `GoldbachSpectral.zeroFree_iff`, `GoldbachSpectral.norm_dictionary`, `GoldbachSeparationSieve.incidence_schur` and `GoldbachSeparationSieve.weighted_witness_count`. The last theorem accepts an explicitly supplied witness inequality. It does not construct the missing arithmetic estimate.

The license covers this original project. Dependencies retain their own licenses.
