# Quaternionic Spectral Hypotheses for the Binary Goldbach Problem

📄 **Archived Preprint & DOI:** [10.5281/zenodo.24432235](https://doi.org/10.5281/zenodo.24432235)

## 📌 Overview
This repository contains the LaTeX manuscript and the Lean 4 formalization of a conditional proof for the Binary Goldbach Conjecture (for sufficiently large even integers). 

The mathematical framework is based on the recent "Quaternionic Spectral Hypotheses" introduced by **Jiamin Li and Jianya Liu** (2026 preprint). The core contribution of this repository is the **independent formalization and verification of the logical framework in Lean 4**, resolving structural bottlenecks (such as the four-free-label configuration) via a novel separation scale \(B = X^{9/10}\).

## 📂 Repository Structure
- 📑 **[Read the English paper](Quaternionic-Goldbach-Lei.pdf)**: The complete mathematical manuscript.
- 📂 **`derivations/`**: Detailed calculation steps and intermediate lemmas (13 stages).
- 💻 **`lean/`**: The complete Lean 4 formalization source code.
- ⚖️ **License**: MIT for code, CC-BY 4.0 for the manuscript.

## 🛠️ Lean 4 Compilation Guide
To verify the Lean 4 code, ensure you have `elan` installed and run:
```bash
cd lean
lake exe cache get
lake build
Note: All main theorems have been checked against the standard Lean axioms (propext, Classical.choice, Quot.sound). The project is self-contained with lake-manifest.json locking the dependencies.

 Author

. Lei Yu - Independent Researcher (Formalization & Verification)

 Acknowledgments

This work builds upon the theoretical framework by Jiamin Li and Jianya Liu. Special thanks to the Lean community for their foundational tools.