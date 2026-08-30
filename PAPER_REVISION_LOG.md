# Paper C revision log

The manuscript is now titled *Truncations, Circuit Layers, and Quantum
Boundary Charts for Totally Nonnegative Toeplitz Positroids*. Its source is
`toeplitz_positroids_truncations_boundary_charts.tex`. This revision covers
the directions independent of companion papers [3] and [4]; revision of
those two papers is deliberately deferred.

## Mathematical and expository changes

- Clarified the novelty boundary: the Rietsch root-of-unity point, the
  Toeplitz--Schur identity, and the loop-free paving classification are stated
  explicitly as inputs, while the exact rectangular support, actual
  autocorrelation derivative, loop-paving chart, and truncation consequences
  are identified as the new contributions.
- Defined a nonstructural two-by-two minor explicitly and corrected the
  cofactor wording in Theorem 5.4 to refer to the distinguished principal
  cofactor sequence, not all entries of the adjugate.
- Added background citations for total nonnegativity, positroids, interval
  positroids, and symmetric functions, and added persistent repository links
  for both companion preprints.
- Repositioned the quantum-binomial point as a refinement of Rietsch's
  Grassmannian root-of-unity Toeplitz point. The manuscript now identifies
  the new contribution as exact rectangular lower-minor support, the
  transverse autocorrelation Jacobian, the inverse-function boundary chart,
  and the loop-paving application.
- Expanded the flat argument in Theorem 3.4. The proof now chooses an
  independent spanning `r`-set and uses the interval-intersection bound to
  exclude every exterior element from the closure.
- Made the original-matrix transfer in Theorem 3.6 explicit. Appending each
  row of the original matrix and expanding the selected determinant shows
  that the projected circuit vectors already lie in the original kernel.
- Filled the positivity step in Theorem 5.2 by explicitly constructing a
  semistandard tableau from vertical ranks under the band-feasibility
  condition.
- Clarified the determinant-one companion-matrix step in Theorem 5.4, hence
  the adjugate identity and the exact autocorrelation Jacobian.
- Added the relevant Rietsch and Chung-Halpern--Rietsch references and
  tightened the novelty claims throughout the abstract and introduction.
- Recorded that the checked Lean 4 development covers Sections 2--7, while
  the conjectures and rank-four question in Section 8 remain outside the
  theorem API.

## Validation

- The complete Lean project builds without `sorry` or `admit`.
- The revised LaTeX source compiles to a 22-page PDF with resolved
  references and metadata.
- Every page of the final PDF was rendered and visually checked; no clipping,
  overfull boxes, header collisions, or orphaned display introductions remain.
