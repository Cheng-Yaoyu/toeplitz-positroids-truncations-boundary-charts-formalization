import FurtherToeplitzPositroids.QuantumRecurrence
import FurtherToeplitzPositroids.QuantumLocalRealization
import PavingToeplitzPositroids.DeterminantDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.Matrix

/-!
# The concrete quantum boundary chart

This module fixes the endpoint coefficients at one, varies the `d-1`
interior coefficients, and proves that the actual strict derivative of the
interior consecutive-minor map is the invertible autocorrelation Jacobian.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Matrix PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- Interior quantum-binomial coefficient coordinates. -/
def quantumInteriorBase (r d : ℕ) : Fin (d - 1) → ℝ :=
  fun t => quantumBinomialCoefficient r d (t.val + 1)

/-- A coefficient inside the fixed-endpoint slice. -/
def quantumSliceBandValue {d : ℕ} (x : Fin (d - 1) → ℝ)
    (t : Fin (d + 1)) : ℝ :=
  if h0 : t.val = 0 then 1
  else if hd : t.val = d then 1
  else x ⟨t.val - 1, by omega⟩

/-- Bi-infinite coefficient function of the fixed-endpoint slice. -/
def quantumSliceCoefficient {d : ℕ} (x : Fin (d - 1) → ℝ)
    (z : ℤ) : ℝ :=
  if hz : 0 ≤ z ∧ z ≤ d then
    quantumSliceBandValue x ⟨z.toNat, by omega⟩
  else 0

/-- Toeplitz matrix in the fixed-endpoint coefficient slice. -/
def quantumSliceMatrix (r d : ℕ) (x : Fin (d - 1) → ℝ) :
    Matrix (Fin (r + 1)) (Fin (d + r + 1)) ℝ :=
  toeplitzMatrix (r + 1) (d + r + 1) (quantumSliceCoefficient x)

theorem quantumSliceBandValue_base
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d + 1)) :
    quantumSliceBandValue (quantumInteriorBase r d) t =
      quantumBinomialCoefficient r d t.val := by
  unfold quantumSliceBandValue quantumInteriorBase
  split_ifs with h0 hright
  · have ht0 : t = 0 := Fin.ext h0
    subst t
    exact (quantumBinomialCoefficient_zero hr (by omega)).symm
  · rw [hright]
    exact (quantumBinomialCoefficient_right hr (by omega)).symm
  · apply congrArg (quantumBinomialCoefficient r d)
    change (t.val - 1) + 1 = t.val
    exact Nat.sub_add_cancel (by omega)

theorem quantumSliceCoefficient_base
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (z : ℤ) :
    quantumSliceCoefficient (quantumInteriorBase r d) z =
      quantumBandCoefficient r d z := by
  unfold quantumSliceCoefficient quantumBandCoefficient
  by_cases hz : 0 ≤ z ∧ z ≤ d
  · rw [dif_pos hz, dif_pos hz, quantumSliceBandValue_base hr hd]
  · rw [dif_neg hz, dif_neg hz]

/-- At the quantum base coordinates, the slice recovers the quantum band
matrix. -/
theorem quantumSliceMatrix_base
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumSliceMatrix r d (quantumInteriorBase r d) =
      quantumBandMatrix r d := by
  ext i j
  simp only [quantumSliceMatrix, toeplitzMatrix_apply,
    quantumBandMatrix_apply]
  exact quantumSliceCoefficient_base hr hd _

/-- Interior anchor `t+1` among the `d+1` consecutive maximal minors. -/
def quantumInteriorAnchor {r d : ℕ} (hd : 1 < d) :
    Fin (d - 1) ↪o Fin (d + r + 1 - r) :=
  OrderEmbedding.ofStrictMono
    (fun t => ⟨t.val + 1, by have ht := t.isLt; omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_right (Fin.mk_lt_mk.mp hij) 1)

/-- The interior consecutive-maximal-minor map `Phi`. -/
def quantumInteriorConsecutiveMap
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (x : Fin (d - 1) → ℝ) : Fin (d - 1) → ℝ := fun t =>
  matrixConsecutiveMinor (show r < d + r + 1 by omega)
    (quantumSliceMatrix r d x) (quantumInteriorAnchor (r := r) hd t)

/-- The selected square block at the quantum base is the recurrence block. -/
theorem quantumSliceMatrix_base_interiorBlock
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    (quantumSliceMatrix r d (quantumInteriorBase r d)).submatrix
      (allRows (r + 1))
      (consecutiveColumns (show r < d + r + 1 by omega)
        (quantumInteriorAnchor (r := r) hd t)) = quantumInteriorBlock r d t := by
  rw [quantumSliceMatrix_base hr hd]
  ext i j
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    quantumBandMatrix_apply, consecutiveColumns_apply_val,
    quantumInteriorAnchor, quantumInteriorBlock]
  congr 2

@[simp] theorem quantumInteriorConsecutiveMap_base
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumInteriorConsecutiveMap hr hd (quantumInteriorBase r d) = 0 := by
  funext t
  unfold quantumInteriorConsecutiveMap matrixConsecutiveMinor
    matrixMaximalMinor orderedMinor
  rw [quantumSliceMatrix_base_interiorBlock hr hd t,
    quantumInteriorBlock_det_eq_zero hr hd t]
  rfl

/-- Every entry of the coefficient slice is continuous. -/
theorem continuous_quantumSliceMatrix (r d : ℕ) :
    Continuous (quantumSliceMatrix r d) := by
  apply continuous_matrix
  intro i j
  simp only [quantumSliceMatrix, toeplitzMatrix_apply,
    quantumSliceCoefficient, quantumSliceBandValue]
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem contDiff_quantumSliceMatrix_apply
    (r d : ℕ) (i : Fin (r + 1)) (j : Fin (d + r + 1)) :
    ContDiff ℝ 1 (fun x => quantumSliceMatrix r d x i j) := by
  simp only [quantumSliceMatrix, toeplitzMatrix_apply,
    quantumSliceCoefficient, quantumSliceBandValue]
  split_ifs
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ _
  · exact contDiff_const

/-- The interior consecutive-minor map is smooth. -/
theorem contDiff_quantumInteriorConsecutiveMap
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    ContDiff ℝ 1 (quantumInteriorConsecutiveMap hr hd) := by
  apply contDiff_pi'
  intro t
  unfold quantumInteriorConsecutiveMap matrixConsecutiveMinor
    matrixMaximalMinor orderedMinor
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro sigma hsigma
  apply ContDiff.const_smul
  apply contDiff_prod
  intro i hi
  exact contDiff_quantumSliceMatrix_apply r d _ _

/-- The actual Frechet derivative at the quantum point. -/
def quantumInteriorFDeriv
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    (Fin (d - 1) → ℝ) →L[ℝ] (Fin (d - 1) → ℝ) :=
  fderiv ℝ (quantumInteriorConsecutiveMap hr hd)
    (quantumInteriorBase r d)

theorem quantumInteriorConsecutiveMap_hasStrictFDerivAt
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    HasStrictFDerivAt (quantumInteriorConsecutiveMap hr hd)
      (quantumInteriorFDeriv hr hd) (quantumInteriorBase r d) := by
  exact (contDiff_quantumInteriorConsecutiveMap hr hd).contDiffAt
    |>.hasStrictFDerivAt one_ne_zero

/-! ## Identification of the actual derivative -/

/-- Coordinate line through the quantum base. -/
def quantumCoordinateLine {r d : ℕ} (s : Fin (d - 1)) (ρ : ℝ) :
    Fin (d - 1) → ℝ :=
  quantumInteriorBase r d +
    ρ • (Pi.single s 1 : Fin (d - 1) → ℝ)

theorem quantumCoordinateLine_hasDerivAt
    {r d : ℕ} (s : Fin (d - 1)) :
    HasDerivAt (quantumCoordinateLine (r := r) s) (Pi.single s 1) 0 := by
  change HasDerivAt (fun ρ : ℝ => quantumInteriorBase r d +
    ρ • (Pi.single s 1 : Fin (d - 1) → ℝ)) (Pi.single s 1) 0
  simpa only [one_smul] using
    ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single s 1)).const_add
      (quantumInteriorBase r d)

theorem quantumSliceBandValue_coordinateLine
    {r d : ℕ} (hd : 1 < d) (s : Fin (d - 1)) (ρ : ℝ)
    (u : Fin (d + 1)) :
    quantumSliceBandValue (quantumCoordinateLine (r := r) s ρ) u =
      quantumSliceBandValue (quantumInteriorBase r d) u +
        if u.val = s.val + 1 then ρ else 0 := by
  unfold quantumSliceBandValue quantumCoordinateLine
  by_cases h0 : u.val = 0
  · rw [dif_pos h0, dif_pos h0, if_neg]
    · simp
    · omega
  · rw [dif_neg h0, dif_neg h0]
    by_cases hright : u.val = d
    · rw [dif_pos hright, dif_pos hright, if_neg]
      · simp
      · have hs := s.isLt
        omega
    · rw [dif_neg hright, dif_neg hright]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul]
      by_cases heq : u.val = s.val + 1
      · rw [if_pos heq, if_pos]
        · ring
        · apply Fin.ext
          change u.val - 1 = s.val
          omega
      · rw [if_neg heq, if_neg]
        · ring
        · intro hidx
          apply heq
          have hval := congrArg Fin.val hidx
          change u.val - 1 = s.val at hval
          omega

theorem quantumSliceCoefficient_coordinateLine
    {r d : ℕ} (hd : 1 < d) (s : Fin (d - 1)) (ρ : ℝ) (z : ℤ) :
    quantumSliceCoefficient (quantumCoordinateLine (r := r) s ρ) z =
      quantumSliceCoefficient (quantumInteriorBase r d) z +
        if z = (s.val + 1 : ℕ) then ρ else 0 := by
  unfold quantumSliceCoefficient
  by_cases hz : 0 ≤ z ∧ z ≤ d
  · rw [dif_pos hz, dif_pos hz,
      quantumSliceBandValue_coordinateLine hd]
    by_cases heq : z = (s.val + 1 : ℕ)
    · rw [if_pos heq, if_pos]
      change z.toNat = s.val + 1
      have hzNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.1
      rw [← hzNat] at heq
      exact_mod_cast heq
    · rw [if_neg heq, if_neg]
      intro hnat
      apply heq
      have hzNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.1
      rw [← hzNat]
      exact_mod_cast hnat
  · rw [dif_neg hz, dif_neg hz]
    have hne : z ≠ (s.val + 1 : ℕ) := by
      intro heq
      apply hz
      constructor
      · omega
      · have hs := s.isLt
        omega
    rw [if_neg hne, add_zero]

/-- Along a coordinate line, each interior block varies in exactly the
Toeplitz diagonal direction used in the cofactor formula. -/
theorem quantumSlice_interiorBlock_coordinateLine
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (t s : Fin (d - 1)) (ρ : ℝ) :
    (quantumSliceMatrix r d (quantumCoordinateLine (r := r) s ρ)).submatrix
        (allRows (r + 1))
        (consecutiveColumns (show r < d + r + 1 by omega)
          (quantumInteriorAnchor (r := r) hd t)) =
      quantumInteriorBlock r d t + ρ • toeplitzBlockDirection t s := by
  ext i j
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    quantumSliceMatrix, toeplitzMatrix_apply, consecutiveColumns_apply_val,
    quantumInteriorAnchor, quantumInteriorBlock, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, toeplitzBlockDirection]
  rw [quantumSliceCoefficient_coordinateLine hd]
  rw [quantumSliceCoefficient_base hr hd]
  change quantumBandCoefficient r d
      (((t.val + 1 + j.val : ℕ) : ℤ) - (i.val : ℤ)) +
        (if (((t.val + 1 + j.val : ℕ) : ℤ) - (i.val : ℤ)) =
          (s.val + 1 : ℕ) then ρ else 0) =
    quantumBandCoefficient r d
      (((t.val + 1 : ℕ) : ℤ) + (j.val : ℤ) - (i.val : ℤ)) +
        ρ * (if t.val + j.val = s.val + i.val then 1 else 0)
  push_cast
  by_cases hdiag : t.val + j.val = s.val + i.val
  · have heq :
        (t.val : ℤ) + 1 + (j.val : ℤ) - (i.val : ℤ) =
          (s.val : ℤ) + 1 := by
      push_cast
      omega
    rw [if_pos heq, if_pos hdiag]
    ring
  · have hne :
        (t.val : ℤ) + 1 + (j.val : ℤ) - (i.val : ℤ) ≠
          (s.val : ℤ) + 1 := by
      intro heq
      apply hdiag
      push_cast at heq
      omega
    rw [if_neg hne, if_neg hdiag]
    ring

/-- Scalar derivative of one interior consecutive minor along one coefficient
coordinate. -/
theorem quantumInteriorConsecutiveMap_coordinateLine_hasDerivAt
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (t s : Fin (d - 1)) :
    HasDerivAt
      (fun ρ : ℝ => quantumInteriorConsecutiveMap hr hd
        (quantumCoordinateLine (r := r) s ρ) t)
      (quantumInteriorJacobian r d t s) 0 := by
  unfold quantumInteriorConsecutiveMap matrixConsecutiveMinor
    matrixMaximalMinor orderedMinor quantumInteriorJacobian
  rw [show (fun ρ : ℝ =>
      ((quantumSliceMatrix r d (quantumCoordinateLine (r := r) s ρ)).submatrix
        (allRows (r + 1))
        (consecutiveColumns (show r < d + r + 1 by omega)
          (quantumInteriorAnchor (r := r) hd t))).det) =
      (fun ρ : ℝ => (quantumInteriorBlock r d t +
        ρ • toeplitzBlockDirection t s).det) by
    funext ρ
    rw [quantumSlice_interiorBlock_coordinateLine hr hd]]
  exact hasDerivAt_det_add_smul_adjugate _ _

/-- Actual Frechet derivative on a coordinate basis vector. -/
theorem quantumInteriorFDeriv_apply_single
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (t s : Fin (d - 1)) :
    quantumInteriorFDeriv hr hd (Pi.single s 1) t =
      quantumInteriorJacobian r d t s := by
  have hphi := (quantumInteriorConsecutiveMap_hasStrictFDerivAt hr hd).hasFDerivAt
  have hline := quantumCoordinateLine_hasDerivAt (r := r) s
  have hcomp := hphi.comp_hasDerivAt_of_eq 0 hline (by
    simp [quantumCoordinateLine])
  let proj : (Fin (d - 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj t
  have hcoord := proj.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have hdirect := quantumInteriorConsecutiveMap_coordinateLine_hasDerivAt
    hr hd t s
  have heq := hcoord.unique hdirect
  simpa [proj, Function.comp_def] using heq

/-- The matrix of the actual derivative is the concrete quantum Jacobian. -/
theorem quantumInteriorFDeriv_matrix_eq
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    continuousLinearMapMatrix (quantumInteriorFDeriv hr hd) =
      quantumInteriorJacobian r d := by
  ext t s
  simp only [continuousLinearMapMatrix, LinearMap.toMatrix'_apply]
  exact quantumInteriorFDeriv_apply_single hr hd t s

theorem quantumInteriorFDeriv_injective
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    Function.Injective (quantumInteriorFDeriv hr hd) := by
  have hdet : (quantumInteriorFDeriv hr hd).toLinearMap.det ≠ 0 := by
    rw [← LinearMap.det_toMatrix']
    change (continuousLinearMapMatrix (quantumInteriorFDeriv hr hd)).det ≠ 0
    rw [quantumInteriorFDeriv_matrix_eq hr hd]
    exact (quantumInteriorJacobian_det_pos hr hd).ne'
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

/-- The actual derivative bundled as the equivalence required by the inverse
function theorem. -/
noncomputable def quantumInteriorDerivativeEquiv
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    (Fin (d - 1) → ℝ) ≃L[ℝ] (Fin (d - 1) → ℝ) := by
  have hinj := quantumInteriorFDeriv_injective hr hd
  exact ContinuousLinearEquiv.ofBijective (quantumInteriorFDeriv hr hd)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj))

theorem quantumInteriorConsecutiveMap_hasStrictFDerivAt_equiv
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    HasStrictFDerivAt (quantumInteriorConsecutiveMap hr hd)
      (quantumInteriorDerivativeEquiv hr hd).toContinuousLinearMap
      (quantumInteriorBase r d) := by
  simpa [quantumInteriorDerivativeEquiv] using
    quantumInteriorConsecutiveMap_hasStrictFDerivAt hr hd

/-! ## Stable support neighborhood -/

theorem quantumSliceMatrix_eq_zero_of_outside
    {r d : ℕ} (x : Fin (d - 1) → ℝ)
    {i : Fin (r + 1)} {j : Fin (d + r + 1)}
    (houtside : (j : ℤ) - (i : ℤ) < 0 ∨
      d < (j : ℤ) - (i : ℤ)) :
    quantumSliceMatrix r d x i j = 0 := by
  simp only [quantumSliceMatrix, toeplitzMatrix_apply,
    quantumSliceCoefficient]
  rw [dif_neg]
  omega

/-- Structural band failure kills every minor throughout the coefficient
slice. -/
theorem quantumSliceMatrix_orderedMinor_eq_zero_of_not_bandFeasible
    {q r d : ℕ} (x : Fin (d - 1) → ℝ)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1))
    (hnot : ¬BandFeasible rows cols) :
    orderedMinor (quantumSliceMatrix r d x) rows cols = 0 := by
  simp only [BandFeasible, not_forall] at hnot
  obtain ⟨t, ht⟩ := hnot
  push Not at ht
  rw [orderedMinor, Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro sigma hsigma
  by_cases hlower : (cols t).val < (rows t).val
  · obtain ⟨c, hct, htsigma⟩ := exists_le_and_le_perm_apply sigma t
    have hcol : cols c ≤ cols t := cols.monotone hct
    have hrow : rows t ≤ rows (sigma c) := rows.monotone htsigma
    have hneg : ((cols c : Fin (d + r + 1)) : ℤ) -
        ((rows (sigma c) : Fin (r + 1)) : ℤ) < 0 := by omega
    have hentry : (quantumSliceMatrix r d x).submatrix rows cols
        (sigma c) c = 0 :=
      quantumSliceMatrix_eq_zero_of_outside x (Or.inl hneg)
    have hprod : ∏ i,
        (quantumSliceMatrix r d x).submatrix rows cols (sigma i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) hentry
    rw [hprod, smul_zero]
  · have hrowcol : (rows t).val ≤ (cols t).val := by omega
    have hupper : (rows t).val + d < (cols t).val := ht hrowcol
    obtain ⟨c, htc, hsigmat⟩ := exists_le_perm_apply_of_le sigma t
    have hcol : cols t ≤ cols c := cols.monotone htc
    have hrow : rows (sigma c) ≤ rows t := rows.monotone hsigmat
    have hlarge : d < ((cols c : Fin (d + r + 1)) : ℤ) -
        ((rows (sigma c) : Fin (r + 1)) : ℤ) := by omega
    have hentry : (quantumSliceMatrix r d x).submatrix rows cols
        (sigma c) c = 0 :=
      quantumSliceMatrix_eq_zero_of_outside x (Or.inr hlarge)
    have hprod : ∏ i,
        (quantumSliceMatrix r d x).submatrix rows cols (sigma i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) hentry
    rw [hprod, smul_zero]

/-- Every fixed minor in the slice depends continuously on the interior
coefficients. -/
theorem continuous_quantumSlice_orderedMinor
    {q r d : ℕ} (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1)) :
    Continuous (fun x => orderedMinor (quantumSliceMatrix r d x) rows cols) := by
  unfold orderedMinor
  exact (continuous_quantumSliceMatrix r d).matrix_submatrix rows cols
    |>.matrix_det

/-- Positivity properties that must persist while applying the inverse
function theorem. -/
def QuantumStableProperty (r d : ℕ) (x : Fin (d - 1) → ℝ) : Prop :=
  (∀ t, 0 < x t) ∧
  ∀ q : Fin (r + 1),
    ∀ rows : Fin q.val ↪o Fin (r + 1),
    ∀ cols : Fin q.val ↪o Fin (d + r + 1),
      BandFeasible rows cols →
        0 < orderedMinor (quantumSliceMatrix r d x) rows cols

def quantumStableSet (r d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {x | QuantumStableProperty r d x}

theorem isOpen_quantumStableSet (r d : ℕ) :
    IsOpen (quantumStableSet r d) := by
  rw [show quantumStableSet r d =
      (⋂ t : Fin (d - 1), {x | 0 < x t}) ∩
      ⋂ q : Fin (r + 1),
      ⋂ rows : Fin q.val ↪o Fin (r + 1),
      ⋂ cols : Fin q.val ↪o Fin (d + r + 1),
        {x | BandFeasible rows cols →
          0 < orderedMinor (quantumSliceMatrix r d x) rows cols} by
    ext x
    simp [quantumStableSet, QuantumStableProperty]]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro t
    exact isOpen_lt continuous_const (continuous_apply t)
  · apply isOpen_iInter_of_finite
    intro q
    apply isOpen_iInter_of_finite
    intro rows
    apply isOpen_iInter_of_finite
    intro cols
    by_cases hband : BandFeasible rows cols
    · have heq : {x | BandFeasible rows cols →
          0 < orderedMinor (quantumSliceMatrix r d x) rows cols} =
          {x | 0 < orderedMinor (quantumSliceMatrix r d x) rows cols} := by
        ext x
        simp [hband]
      rw [heq]
      exact isOpen_lt continuous_const
        (continuous_quantumSlice_orderedMinor rows cols)
    · have heq : {x | BandFeasible rows cols →
          0 < orderedMinor (quantumSliceMatrix r d x) rows cols} = Set.univ := by
        ext x
        simp [hband]
      rw [heq]
      exact isOpen_univ

theorem quantumInteriorBase_mem_stableSet
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumInteriorBase r d ∈ quantumStableSet r d := by
  constructor
  · intro t
    exact quantumBinomialCoefficient_pos hr (by omega) (by
      have ht := t.isLt
      omega)
  · intro q rows cols hband
    rw [quantumSliceMatrix_base hr hd]
    have hq : q.val ≤ r := by omega
    exact quantumBandMatrix_orderedMinor_pos_of_bandFeasible
      hr (by omega) hq rows cols hband

theorem quantumStableSet_mem_nhds
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumStableSet r d ∈ nhds (quantumInteriorBase r d) :=
  (isOpen_quantumStableSet r d).mem_nhds
    (quantumInteriorBase_mem_stableSet hr hd)

theorem QuantumStableProperty.tnUpTo
    {r d : ℕ} {x : Fin (d - 1) → ℝ}
    (hx : QuantumStableProperty r d x) :
    TNUpTo (quantumSliceMatrix r d x) r := by
  intro q hq rows cols
  by_cases hband : BandFeasible rows cols
  · let q' : Fin (r + 1) := ⟨q, by omega⟩
    exact (hx.2 q' rows cols hband).le
  · rw [quantumSliceMatrix_orderedMinor_eq_zero_of_not_bandFeasible
      x rows cols hband]

/-- A nonzero selected row minor certifies independence of the selected
columns in the ambient matrix. -/
theorem linearIndependent_columns_of_nonzero_selectedMinor
    {q R C : ℕ} (A : Matrix (Fin R) (Fin C) ℝ)
    (rows : Fin q ↪o Fin R) (cols : Fin q ↪o Fin C)
    (hminor : orderedMinor A rows cols ≠ 0) :
    LinearIndependent ℝ (fun j : Fin q => A.col (cols j)) := by
  let B : Matrix (Fin q) (Fin C) ℝ := A.submatrix rows id
  have hBminor : orderedMinor B (allRows q) cols ≠ 0 := by
    change (A.submatrix rows cols).det ≠ 0
    simpa [B, allRows, Matrix.submatrix_submatrix] using hminor
  have hBind : LinearIndependent ℝ (fun j : Fin q => B.col (cols j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns B cols).mp hBminor
  let restrictRows : (Fin R → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
    LinearMap.pi fun i => LinearMap.proj (rows i)
  apply LinearIndependent.of_comp restrictRows
  have hfamily :
      (restrictRows ∘ fun j : Fin q => A.col (cols j)) =
        fun j : Fin q => B.col (cols j) := by
    funext j i
    rfl
  rw [hfamily]
  exact hBind

theorem QuantumStableProperty.columns_independent
    {r d : ℕ} {x : Fin (d - 1) → ℝ}
    (hx : QuantumStableProperty r d x)
    (cols : Fin r ↪o Fin (d + r + 1)) :
    LinearIndependent ℝ
      (fun j : Fin r => (quantumSliceMatrix r d x).col (cols j)) := by
  let rows := quantumFeasibleRows (le_refl r) cols
  apply linearIndependent_columns_of_nonzero_selectedMinor
    (quantumSliceMatrix r d x) rows cols
  exact (hx.2 ⟨r, Nat.lt_succ_self r⟩ rows cols
    (quantumFeasibleRows_bandFeasible (le_refl r) cols)).ne'

theorem QuantumStableProperty.columns_independent_le
    {q r d : ℕ} {x : Fin (d - 1) → ℝ}
    (hx : QuantumStableProperty r d x) (hq : q ≤ r)
    (cols : Fin q ↪o Fin (d + r + 1)) :
    LinearIndependent ℝ
      (fun j : Fin q => (quantumSliceMatrix r d x).col (cols j)) := by
  let rows := quantumFeasibleRows hq cols
  apply linearIndependent_columns_of_nonzero_selectedMinor
    (quantumSliceMatrix r d x) rows cols
  exact (hx.2 ⟨q, by omega⟩ rows cols
    (quantumFeasibleRows_bandFeasible hq cols)).ne'

theorem QuantumStableProperty.sliceBandValue_pos
    {r d : ℕ} {x : Fin (d - 1) → ℝ}
    (hx : QuantumStableProperty r d x) (u : Fin (d + 1)) :
    0 < quantumSliceBandValue x u := by
  unfold quantumSliceBandValue
  split_ifs
  · norm_num
  · norm_num
  · exact hx.1 _

/-! ## Protected endpoint minors -/

@[simp] theorem quantumSliceBandValue_zero
    {d : ℕ} (x : Fin (d - 1) → ℝ) :
    quantumSliceBandValue x ⟨0, by omega⟩ = 1 := by
  simp [quantumSliceBandValue]

@[simp] theorem quantumSliceBandValue_right
    {d : ℕ} (x : Fin (d - 1) → ℝ) :
    quantumSliceBandValue x ⟨d, by omega⟩ = 1 := by
  simp [quantumSliceBandValue]

@[simp] theorem quantumSliceCoefficient_zero
    {d : ℕ} (x : Fin (d - 1) → ℝ) :
    quantumSliceCoefficient x 0 = 1 := by
  unfold quantumSliceCoefficient
  rw [dif_pos]
  · exact quantumSliceBandValue_zero x
  · omega

@[simp] theorem quantumSliceCoefficient_right
    {d : ℕ} (x : Fin (d - 1) → ℝ) :
    quantumSliceCoefficient x d = 1 := by
  unfold quantumSliceCoefficient
  rw [dif_pos]
  · exact quantumSliceBandValue_right x
  · omega

/-- The protected first consecutive maximal minor is identically one. -/
theorem quantumSlice_firstConsecutiveMinor
    {r d : ℕ} (hd : 0 < d) (x : Fin (d - 1) → ℝ) :
    matrixConsecutiveMinor (show r < d + r + 1 by omega)
      (quantumSliceMatrix r d x) ⟨0, by omega⟩ = 1 := by
  unfold matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    (quantumSliceMatrix r d x).submatrix (allRows (r + 1))
      (consecutiveColumns (show r < d + r + 1 by omega) ⟨0, by omega⟩)
  change B.det = 1
  have htri : B.BlockTriangular id := by
    intro i j hji
    have hneg : (j : ℤ) - (i : ℤ) < 0 := by
      have hji' : j.val < i.val := by simpa using hji
      omega
    change quantumSliceMatrix r d x (allRows (r + 1) i)
      (consecutiveColumns (show r < d + r + 1 by omega)
        ⟨0, by omega⟩ j) = 0
    apply quantumSliceMatrix_eq_zero_of_outside x
    left
    simpa [consecutiveColumns_apply_val, allRows_apply_eq_self] using hneg
  rw [Matrix.det_of_upperTriangular htri]
  have hdiag : ∀ i : Fin (r + 1), B i i = 1 := by
    intro i
    change quantumSliceCoefficient x
      (((consecutiveColumns (show r < d + r + 1 by omega)
        ⟨0, by omega⟩ i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = 1
    rw [show (((consecutiveColumns (show r < d + r + 1 by omega)
        ⟨0, by omega⟩ i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = 0 by
      simp [consecutiveColumns_apply_val, allRows_apply_eq_self]]
    exact quantumSliceCoefficient_zero x
  simp_rw [hdiag]
  simp

/-- The protected last consecutive maximal minor is identically one. -/
theorem quantumSlice_lastConsecutiveMinor
    {r d : ℕ} (hd : 0 < d) (x : Fin (d - 1) → ℝ) :
    matrixConsecutiveMinor (show r < d + r + 1 by omega)
      (quantumSliceMatrix r d x) ⟨d, by omega⟩ = 1 := by
  unfold matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    (quantumSliceMatrix r d x).submatrix (allRows (r + 1))
      (consecutiveColumns (show r < d + r + 1 by omega) ⟨d, by omega⟩)
  change B.det = 1
  have htri : B.BlockTriangular OrderDual.toDual := by
    intro i j hji
    have hlarge : d < (d : ℤ) + (j : ℤ) - (i : ℤ) := by
      have hij : i.val < j.val := by simpa using hji
      omega
    change quantumSliceMatrix r d x (allRows (r + 1) i)
      (consecutiveColumns (show r < d + r + 1 by omega)
        ⟨d, by omega⟩ j) = 0
    apply quantumSliceMatrix_eq_zero_of_outside x
    right
    simpa [consecutiveColumns_apply_val, allRows_apply_eq_self] using hlarge
  rw [Matrix.det_of_lowerTriangular B htri]
  have hdiag : ∀ i : Fin (r + 1), B i i = 1 := by
    intro i
    change quantumSliceCoefficient x
      (((consecutiveColumns (show r < d + r + 1 by omega)
        ⟨d, by omega⟩ i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = 1
    rw [show (((consecutiveColumns (show r < d + r + 1 by omega)
        ⟨d, by omega⟩ i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = d by
      simp [consecutiveColumns_apply_val, allRows_apply_eq_self]]
    exact quantumSliceCoefficient_right x
  simp_rw [hdiag]
  simp

/-! ## Theorem 5.6 -/

/-- A concrete realization of one interior consecutive-minor target. -/
structure QuantumTargetRealization
    (r d : ℕ) (hd : 1 < d) (delta : Fin (d - 1) → ℝ) where
  source : Fin (d - 1) → ℝ
  coefficient_pos : ∀ u : Fin (d + 1),
    0 < quantumSliceBandValue source u
  interiorConsecutive_eq : ∀ t,
    matrixConsecutiveMinor (show r < d + r + 1 by omega)
      (quantumSliceMatrix r d source)
      (quantumInteriorAnchor (r := r) hd t) = delta t
  firstConsecutive_eq :
    matrixConsecutiveMinor (show r < d + r + 1 by omega)
      (quantumSliceMatrix r d source) ⟨0, by omega⟩ = 1
  lastConsecutive_eq :
    matrixConsecutiveMinor (show r < d + r + 1 by omega)
      (quantumSliceMatrix r d source) ⟨d, by omega⟩ = 1
  lowerMinor_pos_iff : ∀ q, q ≤ r →
    ∀ rows : Fin q ↪o Fin (r + 1),
    ∀ cols : Fin q ↪o Fin (d + r + 1),
      0 < orderedMinor (quantumSliceMatrix r d source) rows cols ↔
        BandFeasible rows cols
  totallyNonnegative : TotallyNonnegative (quantumSliceMatrix r d source)
  fullRowRank : HasFullRowRank (quantumSliceMatrix r d source)
  columns_independent : ∀ q, q ≤ r →
    ∀ cols : Fin q ↪o Fin (d + r + 1),
      LinearIndependent ℝ
        (fun j : Fin q => (quantumSliceMatrix r d source).col (cols j))

/-- Theorem 5.6: every sufficiently small nonnegative interior target is
realized in the fixed-endpoint quantum coefficient slice. -/
theorem exists_quantumTargetRealization
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin (d - 1) → ℝ,
        (∀ t, 0 ≤ delta t ∧ delta t < eta) →
          Nonempty (QuantumTargetRealization r d hd delta) := by
  obtain ⟨eta, heta, hbox⟩ :=
    exists_local_preimage_nonnegative_box_zero
      (quantumInteriorConsecutiveMap_hasStrictFDerivAt_equiv hr hd)
      (quantumInteriorConsecutiveMap_base hr hd)
      (quantumStableSet_mem_nhds hr hd)
  refine ⟨eta, heta, fun delta hdelta => ?_⟩
  obtain ⟨x, hx, hphi⟩ := hbox delta hdelta
  have hstable : QuantumStableProperty r d x := hx
  have hconsecutive : ∀ t : Fin (d + r + 1 - r),
      0 ≤ matrixConsecutiveMinor (show r < d + r + 1 by omega)
        (quantumSliceMatrix r d x) t := by
    intro t
    by_cases hzero : t.val = 0
    · have ht : t = ⟨0, by omega⟩ := Fin.ext hzero
      rw [ht]
      rw [quantumSlice_firstConsecutiveMinor (by omega)]
      norm_num
    · by_cases hlast : t.val = d
      · have ht : t = ⟨d, by omega⟩ := Fin.ext hlast
        rw [ht]
        rw [quantumSlice_lastConsecutiveMinor (by omega)]
        norm_num
      · let s : Fin (d - 1) := ⟨t.val - 1, by
          have ht := t.isLt
          omega⟩
        have hanchor : quantumInteriorAnchor (r := r) hd s = t := by
          apply Fin.ext
          change (t.val - 1) + 1 = t.val
          omega
        rw [← hanchor]
        change 0 ≤ quantumInteriorConsecutiveMap hr hd x s
        rw [congrFun hphi s]
        exact (hdelta s).1
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have htn : TotallyNonnegative (quantumSliceMatrix (p + 1) d x) := by
    apply positive_completion_totallyNonnegative
      (r := p) (n := d + (p + 1) + 1) (by omega)
    · exact hstable.tnUpTo
    · exact hstable.columns_independent
    · exact hconsecutive
  have hfull : HasFullRowRank (quantumSliceMatrix (p + 1) d x) := by
    let cols := consecutiveColumns
      (show p + 1 < d + (p + 1) + 1 by omega)
      (⟨0, by omega⟩ : Fin (d + (p + 1) + 1 - (p + 1)))
    refine ⟨cols, ?_⟩
    change matrixConsecutiveMinor
      (show p + 1 < d + (p + 1) + 1 by omega)
      (quantumSliceMatrix (p + 1) d x) ⟨0, by omega⟩ ≠ 0
    rw [quantumSlice_firstConsecutiveMinor (by omega)]
    norm_num
  refine ⟨{
    source := x
    coefficient_pos := hstable.sliceBandValue_pos
    interiorConsecutive_eq := fun t => by
      change quantumInteriorConsecutiveMap (by omega) hd x t = delta t
      exact congrFun hphi t
    firstConsecutive_eq := quantumSlice_firstConsecutiveMinor (by omega) x
    lastConsecutive_eq := quantumSlice_lastConsecutiveMinor (by omega) x
    lowerMinor_pos_iff := fun q hq rows cols => ?_
    totallyNonnegative := htn
    fullRowRank := hfull
    columns_independent := fun q hq cols =>
      hstable.columns_independent_le hq cols }⟩
  constructor
  · intro hpos
    by_contra hnot
    rw [quantumSliceMatrix_orderedMinor_eq_zero_of_not_bandFeasible
      x rows cols hnot] at hpos
    exact (lt_irrefl 0 hpos)
  · intro hband
    exact hstable.2 ⟨q, by omega⟩ rows cols hband

/-- Zero-pattern form of Theorem 5.6. -/
theorem exists_quantumZeroPatternRealization
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (Z : Finset (Fin (d - 1))) :
    ∃ delta : Fin (d - 1) → ℝ,
      Nonempty (QuantumTargetRealization r d hd delta) ∧
      ∀ t, delta t = 0 ↔ t ∈ Z := by
  obtain ⟨eta, heta, hbox⟩ := exists_quantumTargetRealization hr hd
  let delta := zeroPatternTarget eta Z
  refine ⟨delta, hbox delta (zeroPatternTarget_nonneg_lt heta Z), ?_⟩
  intro t
  exact zeroPatternTarget_eq_zero_iff heta Z t

end

end FurtherToeplitzPositroids
