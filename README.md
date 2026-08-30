# Truncations, Circuit Layers, and Quantum Boundary Charts for Totally Nonnegative Toeplitz Positroids

Lean 4 formalization accompanying *Truncations, Circuit Layers, and Quantum
Boundary Charts for Totally Nonnegative Toeplitz Positroids*.

The formal manuscript source is
`toeplitz_positroids_truncations_boundary_charts.tex`; the compiled paper is
placed in `output/pdf/toeplitz_positroids_truncations_boundary_charts.pdf`.

This repository is Paper C in the Toeplitz-positroid project. It reuses
[Paper B](https://github.com/Cheng-Yaoyu/paving-toeplitz-positroids-formalization),
which in turn imports the checked matrix, Toeplitz, low-rank, and finite-Edrei
infrastructure from
[Paper A](https://github.com/Cheng-Yaoyu/toeplitz-positroids-ranks-2-3-formalization).

The project is pinned to Lean and mathlib `v4.29.0`. Build the checked library
with:

```sh
lake build
```

The conjectures and open question in Section 8 are documented in
`OPEN_PROBLEMS.md`. They are not asserted as proved Lean theorems.

The substantive proved results in Sections 2--7 are fully formalized, including the
original-matrix circuit transfer in Theorem 3.6, the exact normalized
autocorrelation Jacobian in Theorem 5.4, and the full matroid-truncation form
of Corollary 3.5. The research conjectures and question in Section 8 remain
deliberately open. See `FORMALIZATION.md` for the theorem crosswalk and
correctness audit.
