# Quaternionic Spectral Hypotheses for the Binary Goldbach Problem

*Balanced operator compressions, separated zero sums, and a three-cut criterion*  
Lei · Research preprint · Version 1.0.0 · 22 November 2026

[Read the English paper](Quaternionic-Goldbach-Lei.pdf) · [Lean reproduction guide](lean/README.md) · [Zenodo record text](Zenodo.md)

The paper follows the quaternionic spectral product of Jiamin Li and Jianya Liu through the balanced compression and its arithmetic sixth moment. The main arithmetic estimates assume global Dirichlet GRH. Theorem 6.1 states the additional one-sided hypothesis at three long cutoffs that would yield balanced prime pairs for every sufficiently large even integer. Corollary 6.2 controls a fixed relative operator defect outside a weighted exceptional set. Theorems 7.1 and 8.1 give the short-cutoff bound and the restricted height-incidence bound, respectively. The general long-cutoff estimate and weak spectral hypothesis on the full Hardy space remain open.

## Contents

| File | Purpose |
| --- | --- |
| `Quaternionic-Goldbach-Lei.pdf` | English preprint with abstract, definitions, proofs, analytic appendix and bibliography. |
| `paper.tex` | Complete editable XeLaTeX source. The bibliography is included in the file. |
| `derivations/` | Thirteen earlier stages with detailed calculations in Chinese. The index below gives the English subject of each file. Equation numbers are local to each stage. The page markers in notes 02–13 preserve the original page references. |
| `lean/` | Standalone Lake project, pinned manifest, theorem audits, verification logs and MIT license. |
| `Zenodo.md` | Suggested public record fields, abstract, rights and appropriate scope. |
| `LICENSE-paper.txt` | Full CC BY 4.0 legal text for the paper, TeX source and the mathematical notes. |

## Supporting derivations

| Stage | Derivation |
| --- | --- |
| 01 | [Quaternionic zeros, the strong and weak hypotheses](derivations/01-quaternion.md) |
| 02 | [Compression, singular values, spectral truncation and boundary blocks](derivations/02-operator.md) |
| 03 | [The first exceptional-set estimate](derivations/03-defect.md) |
| 04 | [Farey dissection and the square-root exceptional bound](derivations/04-farey.md) |
| 05 | [Signed triangular averages and local representations](derivations/05-windows.md) |
| 06 | [Physical weights, Green kernel, exact duality and the signed remainder](derivations/06-duality.md) |
| 07 | [Major-arc error, collective minor-arc resonance and the Kloosterman phase](derivations/07-arcs.md) |
| 08 | [Mellin decomposition, Vaughan's identity and Type II zeros](derivations/08-mellin.md) |
| 09 | [Free character labels and joint second moments](derivations/09-labels.md) |
| 10 | [Five moduli and the two-match bound](derivations/10-moduli.md) |
| 11 | [Disjoint zero ordinates and the radial phase](derivations/11-zeros.md) |
| 12 | [Reflections, four-prime geometry and positive traces](derivations/12-routes.md) |
| 13 | [Two large sieves, three long cuts and the defect criterion](derivations/13-sieve.md) |

## Rebuild the paper

With a standard TeX Live installation including XeLaTeX, Latin Modern Roman and Latin Modern Math, run from this directory:

```sh
xelatex -halt-on-error paper.tex
xelatex -halt-on-error paper.tex
xelatex -halt-on-error paper.tex
```

The output is `paper.pdf`. The distributed PDF uses the descriptive filename above. The third run stabilizes the table of contents and cross-references. To rebuild the formal companion, follow the commands in [the Lean guide](lean/README.md).

## Rights and attribution

Copyright © 2026 Lei. The manuscript, its TeX source and the accompanying mathematical derivations are available under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The original Lean code and its project documentation are available under the [MIT license](lean/LICENSE). Third-party papers in the bibliography and external software dependencies retain their respective rights. Suggested citation: Lei (2026), *Quaternionic Spectral Hypotheses for the Binary Goldbach Problem: Balanced operator compressions, separated zero sums, and a three-cut criterion*, version 1.0.0, research preprint.
