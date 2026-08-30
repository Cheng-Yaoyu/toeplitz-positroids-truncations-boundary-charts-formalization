import FurtherToeplitzPositroids.SchurStability

/-!
# Arbitrary quantum Toeplitz minors as skew Schur specializations

This module instantiates the dual Jacobi--Trudi identity for an ordered minor
of the quantum band matrix.  The transpose partitions use the reversed row
and column selections from equation (23).
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Finset Matrix MvPolynomial AlgebraicCombinatorics
open ToeplitzPositroids

noncomputable section

/-- The gap `f(i)-i` of an order embedding is monotone. -/
theorem orderEmbedding_indexGap_monotone
    {k n : ℕ} (f : Fin k ↪o Fin n) :
    Monotone (fun i : Fin k => (f i).val - i.val) := by
  cases k with
  | zero =>
      intro i
      exact i.elim0
  | succ k =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      change (f i.castSucc).val - i.val ≤
        (f i.succ).val - (i.val + 1)
      have h := f.strictMono i.castSucc_lt_succ
      have hf := Fin.mk_lt_mk.mp h
      omega

/-- The outer transpose partition associated with selected columns. -/
def quantumMinorOuterTranspose
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) : Fin q → ℕ :=
  fun p => (cols (Fin.rev p)).val - (Fin.rev p).val

/-- The inner transpose partition associated with selected rows. -/
def quantumMinorInnerTranspose
    {q r : ℕ} (rows : Fin q ↪o Fin (r + 1)) : Fin q → ℕ :=
  fun p => (rows (Fin.rev p)).val - (Fin.rev p).val

theorem quantumMinorOuterTranspose_antitone
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    Antitone (quantumMinorOuterTranspose cols) := by
  intro p q hpq
  apply orderEmbedding_indexGap_monotone cols
  apply Fin.mk_le_mk.mpr
  have hp := Fin.mk_le_mk.mp hpq
  omega

theorem quantumMinorInnerTranspose_antitone
    {q r : ℕ} (rows : Fin q ↪o Fin (r + 1)) :
    Antitone (quantumMinorInnerTranspose rows) := by
  intro p q hpq
  apply orderEmbedding_indexGap_monotone rows
  apply Fin.mk_le_mk.mpr
  have hp := Fin.mk_le_mk.mp hpq
  omega

theorem quantumMinorTranspose_contained
    {q r d : ℕ}
    {rows : Fin q ↪o Fin (r + 1)}
    {cols : Fin q ↪o Fin (d + r + 1)}
    (hband : BandFeasible rows cols) :
    ∀ p, quantumMinorInnerTranspose rows p ≤
      quantumMinorOuterTranspose cols p := by
  intro p
  have hb := (hband (Fin.rev p)).1
  have hr := orderEmbedding_fin_val_lower_bound rows (Fin.rev p)
  have hc := orderEmbedding_fin_val_lower_bound cols (Fin.rev p)
  unfold quantumMinorInnerTranspose quantumMinorOuterTranspose
  omega

/-- The transpose partitions fit in the ambient `d+r+1` row bound. -/
theorem quantumMinorOuterTranspose_height
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    ∀ p, quantumMinorOuterTranspose cols p ≤ d + r + 1 := by
  intro p
  unfold quantumMinorOuterTranspose
  exact (Nat.sub_le _ _).trans (cols (Fin.rev p)).isLt.le

/-- Every skew column has height at most the bandwidth `d`. -/
theorem quantumMinorTranspose_columnHeight
    {q r d : ℕ}
    {rows : Fin q ↪o Fin (r + 1)}
    {cols : Fin q ↪o Fin (d + r + 1)}
    (hband : BandFeasible rows cols) (p : Fin q) :
    quantumMinorOuterTranspose cols p -
      quantumMinorInnerTranspose rows p ≤ d := by
  have hb := hband (Fin.rev p)
  have hr := orderEmbedding_fin_val_lower_bound rows (Fin.rev p)
  have hc := orderEmbedding_fin_val_lower_bound cols (Fin.rev p)
  unfold quantumMinorOuterTranspose quantumMinorInnerTranspose
  omega

/-! ## Fixed-length transpose partitions -/

/-- Transpose a fixed-width tuple into an ambient fixed number of rows. -/
def transposeWithin (N : ℕ) {k : ℕ} (partT : Fin k → ℕ) :
    Fin N → ℕ := fun r =>
  (Finset.univ.filter fun c : Fin k => r.val + 1 ≤ partT c).card

theorem transposeWithin_antitone (N : ℕ) {k : ℕ}
    (partT : Fin k → ℕ) : Antitone (transposeWithin N partT) := by
  intro r₁ r₂ hr
  apply Finset.card_le_card
  intro c hc
  simp only [transposeWithin, Finset.mem_filter, Finset.mem_univ,
    true_and] at hc ⊢
  exact (Nat.add_le_add_right (Fin.mk_le_mk.mp hr) 1).trans hc

/-- There are exactly `m` indices of `Fin N` whose values are below `m`. -/
theorem card_filter_fin_val_lt (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < m).card = m := by
  let S := Finset.univ.filter fun i : Fin N => i.val < m
  let e : S ≃ Fin m :=
    { toFun := fun i => ⟨i.val.val, by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          using i.property⟩
      invFun := fun i => ⟨⟨i.val, i.isLt.trans_le hm⟩, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact i.isLt⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  change S.card = m
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- Box membership for the explicitly constructed transpose. -/
theorem transposeWithin_box_equiv (N : ℕ) {k : ℕ}
    {partT : Fin k → ℕ} (hpartT : Antitone partT)
    (r : Fin N) (c : Fin k) :
    c.val + 1 ≤ transposeWithin N partT r ↔
      r.val + 1 ≤ partT c := by
  constructor
  · intro hcard
    by_contra hnot
    have hsubset : (Finset.univ.filter fun j : Fin k =>
        r.val + 1 ≤ partT j) ⊆ Finset.Iio c := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hjc
      have hcj : c ≤ j := by omega
      exact hnot (hj.trans (hpartT hcj))
    have hc := Finset.card_le_card hsubset
    rw [Fin.card_Iio] at hc
    unfold transposeWithin at hcard
    omega
  · intro hbox
    have hsubset : (Finset.univ.filter fun j : Fin k => j ≤ c) ⊆
        (Finset.univ.filter fun j : Fin k =>
          r.val + 1 ≤ partT j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hbox.trans (hpartT hj)
    have hc := Finset.card_le_card hsubset
    rw [card_filter_fin_le] at hc
    unfold transposeWithin
    exact hc

/-- The explicit fixed-row transpose satisfies the canonical transpose
predicate. -/
theorem transposeWithin_isTranspose (N : ℕ) {k : ℕ}
    {partT : Fin k → ℕ} (hpartT : Antitone partT)
    (hheight : ∀ c, partT c ≤ N) :
    NPartition.IsTranspose (transposeWithin N partT) partT := by
  constructor
  · intro c
    have heq : (Finset.univ.filter fun r : Fin N =>
        c.val + 1 ≤ transposeWithin N partT r) =
      Finset.univ.filter fun r : Fin N => r.val < partT c := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [transposeWithin_box_equiv N hpartT]
      omega
    rw [heq, card_filter_fin_val_lt N (partT c) (hheight c)]
  · intro r
    rfl

/-! ## Skew shapes attached to a quantum minor -/

/-- Outer skew-shape partition in the ambient `d+r+1` row type. -/
def quantumMinorOuterShape
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    Fin (d + r + 1) → ℕ :=
  transposeWithin (d + r + 1) (quantumMinorOuterTranspose cols)

/-- Inner skew-shape partition in the ambient `d+r+1` row type. -/
def quantumMinorInnerShape
    {q r d : ℕ} (rows : Fin q ↪o Fin (r + 1)) :
    Fin (d + r + 1) → ℕ :=
  transposeWithin (d + r + 1) (quantumMinorInnerTranspose rows)

theorem quantumMinorOuterShape_antitone
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    Antitone (quantumMinorOuterShape cols) :=
  transposeWithin_antitone _ _

theorem quantumMinorInnerShape_antitone
    {q r d : ℕ} (rows : Fin q ↪o Fin (r + 1)) :
    Antitone (quantumMinorInnerShape (d := d) rows) :=
  transposeWithin_antitone _ _

theorem quantumMinorOuterShape_isTranspose
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    NPartition.IsTranspose (quantumMinorOuterShape cols)
      (quantumMinorOuterTranspose cols) :=
  transposeWithin_isTranspose _ (quantumMinorOuterTranspose_antitone cols)
    (quantumMinorOuterTranspose_height cols)

theorem quantumMinorInnerShape_isTranspose
    {q r d : ℕ} (rows : Fin q ↪o Fin (r + 1)) :
    NPartition.IsTranspose (quantumMinorInnerShape (d := d) rows)
      (quantumMinorInnerTranspose rows) :=
  transposeWithin_isTranspose _ (quantumMinorInnerTranspose_antitone rows)
    (fun p => by
      unfold quantumMinorInnerTranspose
      have hp := (rows (Fin.rev p)).isLt
      omega)

theorem quantumMinorOuterShape_width
    {q r d : ℕ} (cols : Fin q ↪o Fin (d + r + 1)) :
    ∀ a, quantumMinorOuterShape cols a ≤ q := by
  intro a
  unfold quantumMinorOuterShape transposeWithin
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun c : Fin q =>
      a.val + 1 ≤ quantumMinorOuterTranspose cols c) Finset.univ)

theorem quantumMinorShape_contained
    {q r d : ℕ}
    {rows : Fin q ↪o Fin (r + 1)}
    {cols : Fin q ↪o Fin (d + r + 1)}
    (hband : BandFeasible rows cols) :
    ∀ a, quantumMinorInnerShape (d := d) rows a ≤
      quantumMinorOuterShape cols a := by
  intro a
  unfold quantumMinorInnerShape quantumMinorOuterShape transposeWithin
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact hc.trans (quantumMinorTranspose_contained hband c)

/-! ## Evaluation of the dual Jacobi--Trudi matrix -/

theorem quantumMinor_dualIndex_eq
    {q r d : ℕ}
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1)) (p s : Fin q) :
    ((quantumMinorOuterTranspose cols p : ℕ) : ℤ) -
        (quantumMinorInnerTranspose rows s : ℕ) - p.val + s.val =
      ((cols (Fin.rev p)).val : ℤ) - (rows (Fin.rev s)).val := by
  have hc := orderEmbedding_fin_val_lower_bound cols (Fin.rev p)
  have hr := orderEmbedding_fin_val_lower_bound rows (Fin.rev s)
  unfold quantumMinorOuterTranspose quantumMinorInnerTranspose
  rw [Nat.cast_sub hc, Nat.cast_sub hr]
  simp only [Fin.val_rev]
  push_cast
  omega

/-- Entrywise evaluation of the dual Jacobi--Trudi matrix is the reversed
transpose of the selected quantum band submatrix. -/
theorem aeval_dualJacobiTrudiMatrixE_quantum_apply
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1)) (p s : Fin q) :
    MvPolynomial.aeval (finZeroPad (r + 1) (quantumAlphabetY r d))
        (dualJacobiTrudiMatrixE ℂ (d + r + 1)
          (quantumMinorOuterTranspose cols)
          (quantumMinorInnerTranspose rows) p s) =
      (quantumBandMatrix r d (rows (Fin.rev s))
        (cols (Fin.rev p)) : ℂ) := by
  simp only [dualJacobiTrudiMatrixE, Matrix.of_apply]
  change MvPolynomial.aeval (finZeroPad (r + 1) (quantumAlphabetY r d))
      (elementarySymmetricExt ℂ (d + (r + 1)) _) = _
  rw [aeval_elementarySymmetricExt_zeroPad_quantum hr hd]
  rw [quantumBandMatrix_apply]
  congr 2
  exact quantumMinor_dualIndex_eq rows cols p s

/-- Equation (23), specialized to the quantum alphabet: the selected minor
is the evaluation of its dual Jacobi--Trudi determinant. -/
theorem aeval_det_dualJacobiTrudiMatrixE_quantum
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1)) :
    MvPolynomial.aeval (finZeroPad (r + 1) (quantumAlphabetY r d))
        (dualJacobiTrudiMatrixE ℂ (d + r + 1)
          (quantumMinorOuterTranspose cols)
          (quantumMinorInnerTranspose rows)).det =
      ((orderedMinor (quantumBandMatrix r d) rows cols : ℝ) : ℂ) := by
  let J := dualJacobiTrudiMatrixE ℂ (d + r + 1)
    (quantumMinorOuterTranspose cols) (quantumMinorInnerTranspose rows)
  let MR : Matrix (Fin q) (Fin q) ℝ :=
    (quantumBandMatrix r d).submatrix rows cols
  let MC : Matrix (Fin q) (Fin q) ℂ :=
    (Complex.ofRealHom.mapMatrix MR)
  let Mrev : Matrix (Fin q) (Fin q) ℂ :=
    (Matrix.reindex Fin.revPerm Fin.revPerm) MC
  rw [show MvPolynomial.aeval
      (finZeroPad (r + 1) (quantumAlphabetY r d)) J.det =
      ((MvPolynomial.aeval
        (finZeroPad (r + 1) (quantumAlphabetY r d))).toRingHom.mapMatrix J).det by
    exact RingHom.map_det _ J]
  have hmat :
      (MvPolynomial.aeval
          (finZeroPad (r + 1) (quantumAlphabetY r d))).toRingHom.mapMatrix J =
        Mrev.transpose := by
    ext p s
    change MvPolynomial.aeval
        (finZeroPad (r + 1) (quantumAlphabetY r d)) (J p s) =
      Mrev.transpose p s
    rw [aeval_dualJacobiTrudiMatrixE_quantum_apply hr hd]
    rfl
  rw [hmat, Matrix.det_transpose]
  change Mrev.det = (MR.det : ℂ)
  rw [show Mrev.det = MC.det by
    exact Matrix.det_reindex_self Fin.revPerm MC]
  exact (RingHom.map_det Complex.ofRealHom MR).symm

/-- Exact skew-Schur expression for every band-feasible quantum minor. -/
theorem quantumBandMatrix_orderedMinor_eq_aeval_skewSchurPoly
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1))
    (hband : BandFeasible rows cols) :
    ((orderedMinor (quantumBandMatrix r d) rows cols : ℝ) : ℂ) =
      MvPolynomial.aeval (finZeroPad (r + 1) (quantumAlphabetY r d))
        (skewSchurPoly (quantumMinorOuterShape cols)
          (quantumMinorInnerShape (d := d) rows) :
            MvPolynomial (Fin (d + r + 1)) ℂ) := by
  let lam := quantumMinorOuterShape cols
  let mu := quantumMinorInnerShape (d := d) rows
  let lamT := quantumMinorOuterTranspose cols
  let muT := quantumMinorInnerTranspose rows
  have hdual := det_dualJacobiTrudiMatrixE_eq_skewSchurPoly
    (R := ℂ)
    (lam := lam) (mu := mu) (lamt := lamT) (muT := muT)
    (quantumMinorOuterShape_antitone cols)
    (quantumMinorInnerShape_antitone (d := d) rows)
    (quantumMinorOuterTranspose_antitone cols)
    (quantumMinorInnerTranspose_antitone rows)
    (quantumMinorOuterShape_isTranspose cols)
    (quantumMinorInnerShape_isTranspose (d := d) rows)
    (quantumMinorOuterShape_width cols)
    (quantumMinorTranspose_contained hband)
    (quantumMinorOuterTranspose_height cols)
  rw [← hdual]
  exact (aeval_det_dualJacobiTrudiMatrixE_quantum hr hd rows cols).symm

/-! ## Arbitrary-order positivity -/

/-- Every band-feasible minor of order at most `r` is strictly positive. -/
theorem quantumBandMatrix_orderedMinor_pos_of_bandFeasible
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hq : q ≤ r)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1))
    (hband : BandFeasible rows cols) :
    0 < orderedMinor (quantumBandMatrix r d) rows cols := by
  let lam := quantumMinorOuterShape cols
  let mu := quantumMinorInnerShape (d := d) rows
  let lamT := quantumMinorOuterTranspose cols
  let muT := quantumMinorInnerTranspose rows
  have hwidth : lam ⟨0, by omega⟩ ≤ r :=
    (quantumMinorOuterShape_width cols ⟨0, by omega⟩).trans hq
  obtain ⟨x, hx, heval⟩ :=
    aeval_skewSchurPoly_zeroPad_quantum_eq_coe_pos
      hr hd (Nat.succ_pos r)
      (lam := lam) (mu := mu) (lamt := lamT) (muT := muT)
      (quantumMinorOuterShape_antitone cols)
      (quantumMinorInnerShape_antitone (d := d) rows)
      (quantumMinorOuterTranspose_antitone cols)
      (quantumMinorInnerTranspose_antitone rows)
      (quantumMinorOuterShape_isTranspose cols)
      (quantumMinorInnerShape_isTranspose (d := d) rows)
      (quantumMinorOuterShape_width cols)
      (quantumMinorTranspose_contained hband)
      (quantumMinorTranspose_columnHeight hband)
      hwidth
  have hminor := quantumBandMatrix_orderedMinor_eq_aeval_skewSchurPoly
    hr hd rows cols hband
  have hcast :
      ((orderedMinor (quantumBandMatrix r d) rows cols : ℝ) : ℂ) =
        (x : ℂ) := hminor.trans heval
  have hreal : orderedMinor (quantumBandMatrix r d) rows cols = x := by
    exact_mod_cast hcast
  rwa [hreal]

/-- Every band-feasible minor of order at most `r+1` is nonnegative. -/
theorem quantumBandMatrix_orderedMinor_nonneg_of_bandFeasible
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hq : q ≤ r + 1)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1))
    (hband : BandFeasible rows cols) :
    0 ≤ orderedMinor (quantumBandMatrix r d) rows cols := by
  let lam := quantumMinorOuterShape cols
  let mu := quantumMinorInnerShape (d := d) rows
  have hwidth : lam ⟨0, by omega⟩ ≤ r + 1 :=
    (quantumMinorOuterShape_width cols ⟨0, by omega⟩).trans hq
  obtain ⟨x, hx, heval⟩ :=
    aeval_skewSchurPoly_zeroPad_quantum_eq_coe_nonneg
      hr hd (Nat.succ_pos r)
      (lam := lam) (mu := mu)
      (quantumMinorOuterShape_antitone cols)
      (quantumMinorInnerShape_antitone (d := d) rows)
      hwidth
  have hminor := quantumBandMatrix_orderedMinor_eq_aeval_skewSchurPoly
    hr hd rows cols hband
  have hcast :
      ((orderedMinor (quantumBandMatrix r d) rows cols : ℝ) : ℂ) =
        (x : ℂ) := hminor.trans heval
  have hreal : orderedMinor (quantumBandMatrix r d) rows cols = x := by
    exact_mod_cast hcast
  rwa [hreal]

/-- Theorem 5.2(i): strict support of every lower-order minor. -/
theorem quantumBandMatrix_minor_pos_iff_bandFeasible
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hq : q ≤ r)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1)) :
    0 < orderedMinor (quantumBandMatrix r d) rows cols ↔
      BandFeasible rows cols := by
  constructor
  · intro hpos
    by_contra hnot
    rw [quantumBandMatrix_orderedMinor_eq_zero_of_not_bandFeasible
      rows cols hnot] at hpos
    exact (lt_irrefl 0 hpos)
  · exact quantumBandMatrix_orderedMinor_pos_of_bandFeasible
      hr hd hq rows cols

/-- Theorem 5.2(ii): the quantum band matrix is totally nonnegative. -/
theorem quantumBandMatrix_totallyNonnegative
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    TotallyNonnegative (quantumBandMatrix r d) := by
  intro q rows cols
  have hq : q ≤ r + 1 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  by_cases hband : BandFeasible rows cols
  · exact quantumBandMatrix_orderedMinor_nonneg_of_bandFeasible
      hr hd hq rows cols hband
  · rw [quantumBandMatrix_orderedMinor_eq_zero_of_not_bandFeasible
      rows cols hband]

/-- Theorem 5.2(iii): every set of at most `r` columns is independent. -/
theorem quantumBandMatrix_columns_independent
    {q r d : ℕ} (hr : 0 < r) (hd : 0 < d) (hq : q ≤ r)
    (cols : Fin q ↪o Fin (d + r + 1)) :
    LinearIndependent ℝ
      (fun j : Fin q => (quantumBandMatrix r d).col (cols j)) := by
  apply quantumBandMatrix_columns_independent_of_bandFeasible_minor_pos hq cols
  intro rows hband
  exact quantumBandMatrix_orderedMinor_pos_of_bandFeasible
    hr hd hq rows cols hband

end

end FurtherToeplitzPositroids
