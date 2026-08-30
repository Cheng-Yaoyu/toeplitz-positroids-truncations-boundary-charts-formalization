# Formalization status

This project formalizes *Truncations, Circuit Layers, and Quantum Boundary
Charts for Totally Nonnegative Toeplitz Positroids* in Lean 4.

## Reproducible environment

- Lean: `v4.29.0`
- mathlib: `v4.29.0`
- Paper B: local clean dependency at the companion repository
- Paper A: the commit pinned transitively by Paper B
- Algebraic-combinatorics support: seven vendored, placeholder-free modules
  pinned at `b6022318e986a0c20764569208ba8ebbe1c04dbf`; see
  `VENDORED_DEPENDENCIES.md`
- No theorem may rely on `sorry`, `admit`, a new mathematical `axiom`, or an
  unchecked external computation.

## Scope

Sections 2--7 contain the proved mathematical results and are formalization
targets. Their substantive implications are checked below; some paper-level
equivalences are deliberately split into necessity, support, realization, and
counting theorems rather than bundled as a single statement about an abstract
matroid. Conjectures 8.1--8.3 and Question 8.4 are open problems; they are not
introduced as axioms or theorems.

## Theorem crosswalk

| Paper material | Lean module | Status |
| --- | --- | --- |
| Lemma 2.1, positive expansion, maximal-minor nonnegativity, and zero support | `PositiveCompletion` | Checked |
| Proposition 3.1 and Corollary 3.3, rectangular Cauchy--Binet and truncation independence sets | `PositiveCompression` | Checked |
| Theorem 3.4(i)--(iii), proper zero set, run intervals, original-matroid flats, exhaustion, and intersection bound | `FirstCircuitLayer` | Checked |
| Corollary 3.5, Toeplitz realization of the first circuit layer | `FirstCircuitLayer` | Checked in full matroid form: the classified Toeplitz realization is proved to satisfy `IsRankTruncationOf (p+2)` |
| Theorem 3.6, positive alternating-circuit subdivision | `FirstCircuitLayer` | Checked in the original matrix: the projection-normalized alternating vectors for the circuit and every anchor are proved to lie in the kernel of `A` |
| Proposition 4.1, coefficient criterion, cross-product inequality, and equality characterization | `RectangularTN2` | Checked |
| Corollary 4.2, nonloop interval | `RectangularTN2` | Checked |
| Theorem 4.3, interval property, endpoint exclusion, and loop-adjacent singleton classes | `LowSkeleton` | Checked in the raw maximal-block representation |
| Lemma 4.4, endpoint protection | `LowSkeleton` | Checked for both endpoints in the explicit simplification-embedding representation, including reversal |
| Theorem 4.5, `k=1` | `LowSkeleton` | Checked |
| Theorem 4.5, `k=2` | `LowSkeleton` | Checked, including canonical projective-coordinate data extraction and Paper A realization |
| Theorem 4.5, `k=3` | `LowSkeleton`, `ThreeSkeletonClassification` | Checked: canonical simplification, raw loop and endpoint-class inflation, exact triple-nonbasis support identification, both endpoint-protection arguments, compatible-support assembly, and Paper A realization |
| Equations (15)--(16), coefficient positivity, endpoint normalization, and structural band zeros | `QuantumBinomial` | Checked |
| Lemma 5.1, centered alphabets and rank--level identities | `QuantumBinomial`, `QuantumRankLevel`, `QuantumSchur` | Checked completely: alphabet inversion/product-one, geometric-progression form, Gaussian-binomial specialization, quantum-integer sine formula, phase cancellation, `b_t=h_t(X)=e_t(Y)` for `0≤t≤d`, the vanishing string `h_{d+1}(X)=⋯=h_{d+r-1}(X)=0`, and endpoint normalization |
| Theorem 5.2 in rank two | `QuantumBinomial` | Checked |
| Theorem 5.2 in rank three (`d ≥ 2`) | `QuantumBinomial` | Checked, including exact lower-order support and pair independence, via Paper A's sine point |
| Theorem 5.2 for width `d = 1` in arbitrary rank | `QuantumBinomial` | Total nonnegativity and exact all-order band-feasible support checked via the one-letter Edrei factor |
| Theorem 5.2 in arbitrary rank | `QuantumBinomial`, `QuantumSchur`, `DualJacobiTrudi`, `DualTableaux`, `SchurStability`, `QuantumMinorSchur` | Checked completely: dual Jacobi--Trudi via weighted LGV, path/column-tableau and transpose-tableau equivalences, zero-padding stability, Littlewood--Richardson/Weyl strict positivity for every band-feasible minor of order at most `r`, structural zeros otherwise, total nonnegativity in all orders, full row rank, and independence of every set of at most `r` columns |
| Theorem 5.4, autocorrelation formula and positive definiteness | `Autocorrelation`, `QuantumJacobian`, `QuantumRecurrence`, `QuantumChart` | Checked completely: Newton--Girard recurrence, determinant-one shift companion, constant Casoratian `κ_t=1`, exact rank-one adjugates, equality of the actual Jacobian with the symmetric positive-definite autocorrelation kernel, positive determinant, and identification with the actual Frechet derivative |
| Example 5.5 | `QuantumBinomial` | Checked exhaustively |
| Theorem 5.6, IFT and positive-completion step | `QuantumLocalRealization`, `QuantumChart` | Checked completely: fixed endpoint coefficients, open stable-support neighborhood, invertible strict derivative, local inverse, prescribed interior consecutive minors, persistent exact lower support, total nonnegativity, full row rank, and all lower-order column independence |
| Theorem 6.2, support necessity and zero-run/interval-hyperplane equivalence | `LoopPavingClassification` | Checked, including loop-boundary maximal minors, properness, endpoint translation, size, and intersection bounds |
| Theorem 6.2, realization direction | `LoopPavingRealization` | Checked completely: arithmetic window data (38)--(39), arbitrary compatible interior zero sets for `d≥2`, exact support (34), low-bandwidth uniform cases `d=1` and `d=0`, translated finite Toeplitz sections, arbitrary loop-prefix/suffix lengths, exact loops, total nonnegativity, full row rank, and the interval-hyperplane form via the checked zero-run equivalence |
| Corollary 6.3 | `LoopPavingEnumeration` | Checked |
| Proposition 7.1 and Corollary 7.2 | `LatticePathFamilies` | Checked in exact index and explicit zero-based lattice-path-bound forms using Paper A's Edrei theorem |
| Theorem 7.3, intermediate-index feasibility | `LatticePathFamilies` | Checked |
| Theorem 7.3, Laurent factorization, exact bi-infinite support (45), and finite-section total nonnegativity | `LatticePathFamilies` | Checked |
| Theorem 7.3, local lattice-path bounds (46) | `LatticePathFamilies` | Checked in zero-based local coordinates |

The conjectures and question in Section 8 are deliberately excluded from the
theorem API and are recorded as open statements in `OPEN_PROBLEMS.md`.

## Current audit gates

- `lake build FurtherToeplitzPositroids` succeeds (8412 build jobs, including
  the vendored algebraic-combinatorics closure).
- The Paper C Lean sources contain no `sorry`, `admit`, or new `axiom`
  declaration.
- `#print axioms` on representative headline theorems from every proved
  section reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Warnings printed by the full build are style, deprecation, and unused-code
  lints in imported, vendored, and Paper C sources; there are no proof errors.

## Correctness findings during formalization

- In the arbitrary-rank trap reparameterization, setting
  `u = m-k-1` and `v = k-2` gives `m = u+v+3`. The checked determinant is
  `c^3 * lambda^u * (lambda^(u+v+s+2)-f) * (e*lambda-1)`.
  This agrees with equation (13) after restoring `e = E*lambda⁻¹` and
  `f = F*lambda^(m+s-1)`. An initial scratch transcription used `u+v+2`;
  Lean rejected the index alignment, and the project source now contains the
  corrected formula.
- The distinguished principal cofactor in equation (33) is now checked
  directly, rather than retained as an unspecified positive scale.  Its
  order-`r` Toeplitz blocks advance by a determinant-one companion matrix and
  start from an upper-triangular unit-diagonal block.  Hence this principal
  cofactor is exactly `1` for every interior block, and the actual Jacobian in
  equation (30) is itself the symmetric positive-definite autocorrelation
  kernel.
- The final kernel transfer in Theorem 3.6 is explicit.  Appending any row
  of `A` to the positive projection gives a row transform of `A`; dependence
  of the selected columns makes its determinant zero, and Laplace expansion
  proves that the projection-normalized alternating vector lies in the
  original kernel.  The same argument applies to every consecutive anchor.
