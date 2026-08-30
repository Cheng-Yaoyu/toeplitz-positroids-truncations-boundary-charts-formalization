import PavingToeplitzPositroids.ConcreteExchange
import PavingToeplitzPositroids.LocalRealization
import PavingToeplitzPositroids.Refinement

/-!
# Positive completion from consecutive maximal minors

This module formalizes Lemma 2.1.  The hypotheses control minors only through
codimension one; positive interpolation then supplies every maximal minor.
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- The projected codimension-one minors are positive under the weaker
`TNUpTo` hypothesis used in Lemma 2.1. -/
theorem projectedMatrix_orderedMinor_pos_of_tnUpTo
    {k n : ℕ} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (hA : TNUpTo A k) (cols : Fin k ↪o Fin n)
    (hind : LinearIndependent ℝ (fun j : Fin k ↦ A.col (cols j))) :
    0 < orderedMinor (projectedMatrix A) (allRows k) cols := by
  rw [projectedMatrix_orderedMinor_eq_sum]
  apply Finset.sum_pos'
  · intro rows _
    exact hA.orderedMinor_nonneg le_rfl rows cols
  · let B : Matrix (Fin (k + 1)) (Fin k) ℝ := A.submatrix id cols
    have hBind : LinearIndependent ℝ B.col := by
      simpa [B, Matrix.col, Matrix.submatrix] using hind
    obtain ⟨rows, hrows⟩ :=
      exists_orderedRowMinor_ne_zero_of_linearIndependent_columns B hBind
    refine ⟨rows, Finset.mem_univ rows, ?_⟩
    have hnonneg := hA.orderedMinor_nonneg le_rfl rows cols
    exact lt_of_le_of_ne hnonneg fun hzero ↦ by
      apply hrows
      change (B.submatrix rows (allRows k)).det = 0
      have hzero' : orderedMinor A rows cols = 0 := hzero.symm
      change (A.submatrix rows cols).det = 0 at hzero'
      simpa [B, allRows, Matrix.submatrix_submatrix] using hzero'

/-- The first row block of the determinant-one transform is strictly positive
under the exact lower-order hypotheses of Lemma 2.1. -/
theorem firstRows_projectionTransform_maximalMinor_pos_of_tnUpTo
    {r n : ℕ} {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TNUpTo A (r + 1))
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (cols : Fin (r + 1) ↪o Fin n) :
    0 < orderedMinor (firstRows (projectionTransform A))
      (allRows (r + 1)) cols := by
  rw [firstRows_projectionTransform]
  exact projectedMatrix_orderedMinor_pos_of_tnUpTo hA cols (hind cols)

/-- Lemma 2.1, equation (1): every maximal minor is a positive combination
of all consecutive anchors in its endpoint span. -/
theorem exists_positive_completion_expansion
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TNUpTo A (r + 1))
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (J : Fin (r + 2) ↪o Fin n) :
    Nonempty (FullPositiveAnchorExpansion (matrixMaximalMinor A J)
      (matrixConsecutiveMinor hrn A) (anchorFinset J)) := by
  let E : MatrixLocalPositiveExchange hrn (projectionTransform A) :=
    matrixLocalPositiveExchange_of_firstRows_pos hrn (projectionTransform A)
      (firstRows_projectionTransform_maximalMinor_pos_of_tnUpTo hA hind)
  obtain ⟨F⟩ := E.exists_interpolation J
  rw [projectionTransform_matrixMaximalMinor A J] at F
  have hD : matrixConsecutiveMinor hrn (projectionTransform A) =
      matrixConsecutiveMinor hrn A := by
    funext t
    exact projectionTransform_matrixConsecutiveMinor hrn A t
  rw [hD] at F
  exact ⟨F⟩

/-- Lemma 2.1: lower-order total nonnegativity and nonnegative consecutive
maximal minors force every maximal minor to be nonnegative. -/
theorem positive_completion_maximalMinor_nonneg
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TNUpTo A (r + 1))
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (hconsecutive : ∀ t : Fin (n - (r + 1)),
      0 ≤ matrixConsecutiveMinor hrn A t)
    (J : Fin (r + 2) ↪o Fin n) :
    0 ≤ matrixMaximalMinor A J := by
  obtain ⟨E⟩ := exists_positive_completion_expansion hrn hA hind J
  exact E.value_nonneg hconsecutive

/-- Lemma 2.1, equation (2): a maximal minor vanishes exactly when all of
its consecutive anchors vanish. -/
theorem positive_completion_maximalMinor_eq_zero_iff
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TNUpTo A (r + 1))
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (hconsecutive : ∀ t : Fin (n - (r + 1)),
      0 ≤ matrixConsecutiveMinor hrn A t)
    (J : Fin (r + 2) ↪o Fin n) :
    matrixMaximalMinor A J = 0 ↔
      ∀ t ∈ anchorFinset J, matrixConsecutiveMinor hrn A t = 0 := by
  obtain ⟨E⟩ := exists_positive_completion_expansion hrn hA hind J
  exact E.value_eq_zero_iff hconsecutive

/-- The full matrix form of Lemma 2.1. -/
theorem positive_completion_totallyNonnegative
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TNUpTo A (r + 1))
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (hconsecutive : ∀ t : Fin (n - (r + 1)),
      0 ≤ matrixConsecutiveMinor hrn A t) :
    TotallyNonnegative A := by
  intro q rows cols
  have hq : q ≤ r + 2 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  by_cases hlow : q ≤ r + 1
  · exact hA.orderedMinor_nonneg hlow rows cols
  · have hqeq : q = r + 2 := by omega
    subst q
    rw [orderEmbedding_fin_self_eq_allRows rows]
    exact positive_completion_maximalMinor_nonneg hrn hA hind hconsecutive cols

end

end FurtherToeplitzPositroids
