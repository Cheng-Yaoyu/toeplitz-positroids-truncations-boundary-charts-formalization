# Open problems from Section 8

Section 8 of *Further Structure in the Toeplitz Positroid Problem* is outside
the proved theorem scope of this formalization. The statements below are
recorded as research targets only. They are not Lean axioms, definitions that
encode assumed truth, or theorem declarations.

## Conjecture 8.1: Toeplitz truncation closure

If a matroid has an all-minor totally nonnegative Toeplitz representation,
then every rank truncation of that matroid also has an all-minor totally
nonnegative Toeplitz representation.

Theorem 4.5 establishes the conjecture through rank three. The first-layer and
loop-paving results cover additional cases in which deleting loops from the
target truncation leaves a paving matroid.

## Conjecture 8.2: Linear interval-rank characterization

Every all-minor totally nonnegative Toeplitz positroid should be an interval
positroid in its displayed linear column order. Equivalently, its matroid
should be determined by rank conditions on ordinary column intervals.

This is stronger than merely being a positroid: it specifies the natural
linear order rather than only the ambient cyclic order.

## Conjecture 8.3: Stratified consecutive interpolation

After contracting the maximal lower-rank interval flats visible in a rank
truncation of an all-minor totally nonnegative matrix, every circuit in the
next rank should admit a positive subdivision into adapted consecutive
circuits. The vanishing next-rank minors should then be controlled by finitely
many consecutive anchors on the contracted intervals.

Together with suitable Toeplitz Jacobian charts on every stratum, this would
provide an induction along the truncation tower. The quantum-binomial chart
suggests root-of-unity Schur specializations as possible boundary base points.

## Question 8.4: The rank-four core

Classify rank-four Toeplitz positroids whose rank-three truncation has fixed
compatible rank-three data. In particular, determine whether an admissible
rank-three interval-flat pattern extends precisely when its maximal
rank-three flats form a nested ordinary-interval erection.

This is the smallest case not covered by the current truncation results.

