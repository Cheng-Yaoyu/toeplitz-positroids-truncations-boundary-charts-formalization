# Truncations, Circuit Layers, and Quantum Boundary Charts for Totally Nonnegative Toeplitz Positroids

Lean 4 formalization accompanying *Truncations, Circuit Layers, and Quantum
Boundary Charts for Totally Nonnegative Toeplitz Positroids*.

## Paper

- [Manuscript PDF](paper/toeplitz_positroids_truncations_boundary_charts.pdf)
- [LaTeX source](paper/toeplitz_positroids_truncations_boundary_charts.tex)

## Toeplitz-positroid series

- **Paper A:** [Toeplitz Positroids in Ranks Two and Three](https://github.com/Cheng-Yaoyu/toeplitz-positroids-ranks-2-3-formalization)
- **Paper B:** [Positive Consecutive-Minor Interpolation and Paving Toeplitz Positroids](https://github.com/Cheng-Yaoyu/paving-toeplitz-positroids-formalization)
- **Paper C:** this repository

Paper C reuses Paper B, which in turn imports the checked matrix, Toeplitz,
low-rank, and finite-Edrei infrastructure from Paper A.

## Formalization

The substantive proved results in Sections 2--7 are formalized, including the
original-matrix circuit transfer in Theorem 3.6, the exact normalized
autocorrelation Jacobian in Theorem 5.4, and the full matroid-truncation form
of Corollary 3.5. The conjectures and open question in Section 8 are documented
in `OPEN_PROBLEMS.md` and are not asserted as Lean theorems.

See `FORMALIZATION.md` for the theorem crosswalk and correctness audit.

## Reproducibility

The project is pinned to Lean and mathlib `v4.29.0`. Build the checked library
with:

```sh
lake build
```

## Repository layout

- `FurtherToeplitzPositroids/`: Paper C theorem modules;
- `FurtherToeplitzPositroids.lean`: root import;
- `AlgebraicCombinatorics/`: pinned vendored support modules;
- `paper/`: current manuscript PDF and LaTeX source;
- `FORMALIZATION.md`: paper-to-Lean crosswalk and audit;
- `CITATION.cff`: machine-readable citation metadata.

## Citation

Use the citation metadata in [`CITATION.cff`](CITATION.cff). Until an arXiv or
journal identifier is assigned, cite the manuscript together with this GitHub
repository.
