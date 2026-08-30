import FurtherToeplitzPositroids.DualTableaux
import FurtherToeplitzPositroids.QuantumSchur

/-!
# Stability under adjoining zero variables

This module compares symmetric-function specializations in `d` variables
with the same specializations in `d+s` variables after adjoining `s` zeros.
It is needed because the skew shape attached to a Toeplitz minor can have
more rows than the quantum alphabet has nonzero letters.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Finset MvPolynomial AlgebraicCombinatorics

noncomputable section

/-- Adjoin `s` zero entries to a finite alphabet. -/
def finZeroPad {R : Type*} [Zero R] {d : ℕ}
    (s : ℕ) (x : Fin d → R) : Fin (d + s) → R :=
  Fin.addCases x (fun _ : Fin s => 0)

@[simp] theorem finZeroPad_castAdd {R : Type*} [Zero R]
    {d s : ℕ} (x : Fin d → R) (i : Fin d) :
    finZeroPad s x (Fin.castAdd s i) = x i := by
  simp [finZeroPad]

@[simp] theorem finZeroPad_natAdd {R : Type*} [Zero R]
    {d s : ℕ} (x : Fin d → R) (i : Fin s) :
    finZeroPad s x (Fin.natAdd d i) = 0 := by
  simp [finZeroPad]

theorem finZeroPad_eq_zero_of_le {R : Type*} [Zero R]
    {d s : ℕ} (x : Fin d → R) (i : Fin (d + s))
    (hi : d ≤ i.val) : finZeroPad s x i = 0 := by
  induction i using Fin.addCases with
  | left i =>
      simp only [Fin.val_castAdd] at hi
      omega
  | right i => simp

/-- The low indices in `Fin (d+s)` are exactly the image of `Fin d`. -/
theorem finset_low_eq_map_castAdd (d s : ℕ) :
    (Finset.univ.filter fun i : Fin (d + s) => i.val < d) =
      (Finset.univ : Finset (Fin d)).map (Fin.castAddEmb s) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hi
    refine ⟨⟨i.val, hi⟩, ?_⟩
    apply Fin.ext
    rfl
  · rintro ⟨j, rfl⟩
    exact j.isLt

/-- Elementary symmetric specialization is unchanged by adjoining zeros. -/
theorem elementarySymmetricSpecialization_zeroPad
    {R : Type*} [CommRing R] {d : ℕ}
    (s t : ℕ) (x : Fin d → R) :
    MvPolynomial.aeval (finZeroPad s x)
        (MvPolynomial.esymm (Fin (d + s)) R t) =
      MvPolynomial.aeval x (MvPolynomial.esymm (Fin d) R t) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, aeval_X]
  let all : Finset (Finset (Fin (d + s))) :=
    Finset.powersetCard t (Finset.univ : Finset (Fin (d + s)))
  let low : Finset (Fin (d + s)) :=
    Finset.univ.filter fun i => i.val < d
  let good : Finset (Finset (Fin (d + s))) :=
    all.filter fun S => S ⊆ low
  have hgood : good = Finset.powersetCard t low := by
    ext S
    simp only [good, all, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    tauto
  have hbad : ∀ S ∈ all, S ∉ good →
      ∏ i ∈ S, finZeroPad s x i = 0 := by
    intro S hS hSbad
    simp only [good, Finset.mem_filter, not_and] at hSbad
    have hnsub : ¬S ⊆ low := hSbad hS
    obtain ⟨i, hiS, hiLow⟩ := Finset.not_subset.mp hnsub
    apply Finset.prod_eq_zero hiS
    apply finZeroPad_eq_zero_of_le x i
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at hiLow
    omega
  have hrestrict :
      (∑ S ∈ all, ∏ i ∈ S, finZeroPad s x i) =
        ∑ S ∈ good, ∏ i ∈ S, finZeroPad s x i := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hSall hSgood
    exact hbad S hSall hSgood
  rw [show (∑ S ∈ Finset.powersetCard t
      (Finset.univ : Finset (Fin (d + s))),
        ∏ i ∈ S, finZeroPad s x i) =
      ∑ S ∈ all, ∏ i ∈ S, finZeroPad s x i by rfl]
  rw [hrestrict, hgood]
  rw [show low = (Finset.univ : Finset (Fin d)).map
    (Fin.castAddEmb s) by exact finset_low_eq_map_castAdd d s]
  rw [Finset.powersetCard_map]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S hS
  change (∏ i ∈ S.map (Fin.castAddEmb s), finZeroPad s x i) =
    ∏ i ∈ S, x i
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- Elementary symmetric specialization vanishes above the alphabet size. -/
theorem elementarySymmetricSpecialization_eq_zero_of_card_lt
    {d t : ℕ} (x : Fin d → ℂ) (hdt : d < t) :
    elementarySymmetricSpecialization x t = 0 := by
  unfold elementarySymmetricSpecialization
  rw [Finset.powersetCard_eq_empty.mpr]
  · simp
  · simp
    exact hdt

/-- The padded quantum alphabet evaluates every elementary symmetric
polynomial to the band coefficient, including the structural zeros above
degree `d`. -/
theorem aeval_esymm_zeroPad_quantum
    {r d s t : ℕ} (hr : 0 < r) (hd : 0 < d) :
    MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (MvPolynomial.esymm (Fin (d + s)) ℂ t) =
      (quantumBandCoefficient r d (t : ℤ) : ℂ) := by
  rw [elementarySymmetricSpecialization_zeroPad]
  rw [← elementarySymmetricSpecialization_eq_aeval_esymm]
  by_cases ht : t ≤ d
  · rw [quantumAlphabetY_elementary_eq_coe_quantumBinomialCoefficient
      hr hd ht]
    unfold quantumBandCoefficient
    rw [dif_pos]
    · simp
    · constructor <;> omega
  · have hdt : d < t := by omega
    rw [elementarySymmetricSpecialization_eq_zero_of_card_lt _ hdt]
    unfold quantumBandCoefficient
    rw [dif_neg]
    simp
    omega

/-- Integer-index version of the preceding padded evaluation. -/
theorem aeval_elementarySymmetricExt_zeroPad_quantum
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d) (z : ℤ) :
    MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (elementarySymmetricExt ℂ (d + s) z) =
      (quantumBandCoefficient r d z : ℂ) := by
  unfold elementarySymmetricExt
  by_cases hz : 0 ≤ z
  · rw [if_pos hz]
    have hcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    rw [aeval_esymm_zeroPad_quantum hr hd, hcast]
  · rw [if_neg hz, map_zero]
    unfold quantumBandCoefficient
    rw [dif_neg]
    simp
    omega

/-! ## Schur stability -/

/-- Evaluation of a tableau monomial is the product of the specialized
variables over its cells. -/
theorem aeval_xPow_content_eq_prod_cells
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {N : ℕ} {lam mu : Fin N → ℕ}
    (x : Fin N → S) (T : Tableau lam mu) :
    MvPolynomial.aeval x
        (xPow (contentTableau T) : MvPolynomial (Fin N) R) =
      ∏ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
        x (T c) := by
  rw [← prod_skewCells_eq_xPow_content (R := R) T]
  rw [map_prod]
  simp

/-- If one tableau entry lies in the padded zero block, its specialized
monomial vanishes. -/
theorem aeval_xPow_content_zeroPad_eq_zero_of_entry
    {R : Type*} [CommRing R] {d s : ℕ}
    {lam mu : Fin (d + s) → ℕ}
    (x : Fin d → R) (T : Tableau lam mu)
    (c : {c : Fin (d + s) × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : d ≤ (T c).val) :
    MvPolynomial.aeval (finZeroPad s x)
        (xPow (contentTableau T) : MvPolynomial (Fin (d + s)) R) = 0 := by
  rw [aeval_xPow_content_eq_prod_cells]
  apply Finset.prod_eq_zero (Finset.mem_univ c)
  exact finZeroPad_eq_zero_of_le x (T c) hc

/-- A straight semistandard tableau whose shape has a nonempty row in the
zero-padded tail must use a tail alphabet entry. -/
theorem exists_tail_entry_of_tail_part_pos
    {d s : ℕ} (hs : 0 < s) {nu : Fin (d + s) → ℕ}
    (hnu : _root_.IsNPartition nu)
    (htail : 0 < nu (Fin.natAdd d (⟨0, hs⟩ : Fin s)))
    (T : Tableau nu 0) (hT : IsSemistandard T) :
    ∃ c, d ≤ (T c).val := by
  let row : Fin (d + 1) ↪o Fin (d + s) :=
    Fin.castLEOrderEmb (m := d + s) (n := d + 1) (by omega)
  let cell : Fin (d + 1) →
      {c : Fin (d + s) × ℕ // c ∈ skewYoungDiagram nu 0} :=
    fun u => ⟨(row u, 1), by
      change 0 < 1 ∧ 1 ≤ nu (row u)
      constructor
      · omega
      · have hrow : row u ≤ Fin.natAdd d (⟨0, hs⟩ : Fin s) := by
          apply Fin.mk_le_mk.mpr
          simp only [row, Fin.val_castLE, Fin.val_natAdd]
          have hu := u.isLt
          omega
        exact htail.trans_le (hnu (row u)
          (Fin.natAdd d (⟨0, hs⟩ : Fin s)) hrow) ⟩
  let entries : Fin (d + 1) ↪o Fin (d + s) :=
    OrderEmbedding.ofStrictMono (fun u => T (cell u)) (by
      intro u v huv
      apply hT.2 (cell u) (cell v)
      · rfl
      · exact row.strictMono huv)
  let last : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
  refine ⟨cell last, ?_⟩
  exact orderEmbedding_fin_val_lower_bound entries last

/-- The padded Schur specialization vanishes when the partition has a
nonzero part beyond the original alphabet length. -/
theorem aeval_schurPoly_zeroPad_eq_zero_of_tail_pos
    {R : Type*} [CommRing R] {d s : ℕ} (hs : 0 < s)
    {nu : Fin (d + s) → ℕ} (hnu : _root_.IsNPartition nu)
    (htail : 0 < nu (Fin.natAdd d (⟨0, hs⟩ : Fin s)))
    (x : Fin d → R) :
    MvPolynomial.aeval (finZeroPad s x)
        (schurPoly nu : MvPolynomial (Fin (d + s)) R) = 0 := by
  unfold schurPoly skewSchurPoly
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro T hTmem
  obtain ⟨c, hc⟩ := exists_tail_entry_of_tail_part_pos hs hnu htail
    T.val T.property
  exact aeval_xPow_content_zeroPad_eq_zero_of_entry x T.val c hc

/-- Restriction of a fixed-length tuple to its initial `d` entries. -/
def finInitialPart {d s : ℕ} (nu : Fin (d + s) → ℕ) : Fin d → ℕ :=
  fun i => nu (Fin.castAdd s i)

theorem finInitialPart_isNPartition
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (hnu : _root_.IsNPartition nu) :
    _root_.IsNPartition (finInitialPart nu) := by
  intro i j hij
  apply hnu _ _
  apply Fin.mk_le_mk.mpr
  exact Fin.mk_le_mk.mp hij

/-- When all tail rows are empty, the straight-shape cells in `d+s` rows
are exactly the cells in the initial `d` rows. -/
def initialStraightCellEquiv
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0) :
    {c : Fin d × ℕ // c ∈ skewYoungDiagram (finInitialPart nu) 0} ≃
      {c : Fin (d + s) × ℕ // c ∈ skewYoungDiagram nu 0} where
  toFun c := ⟨(Fin.castAdd s c.val.1, c.val.2), by
    change 0 < c.val.2 ∧ c.val.2 ≤ nu (Fin.castAdd s c.val.1)
    have hc := c.property
    change 0 < c.val.2 ∧ c.val.2 ≤
      finInitialPart nu c.val.1 at hc
    exact hc⟩
  invFun c := ⟨(⟨c.val.1.val, by
      by_contra hnot
      have hzero := htail c.val.1 (by omega)
      have hc := c.property
      change 0 < c.val.2 ∧ c.val.2 ≤ nu c.val.1 at hc
      rw [hzero] at hc
      omega⟩, c.val.2), by
    change 0 < c.val.2 ∧ c.val.2 ≤
      finInitialPart nu ⟨c.val.1.val, _⟩
    have hc := c.property
    change 0 < c.val.2 ∧ c.val.2 ≤ nu c.val.1 at hc
    exact hc⟩
  left_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl

/-- A straight tableau in the padded row type is initial-valued when every
entry belongs to the original `d`-letter alphabet. -/
def IsInitialValued {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (T : Tableau nu 0) : Prop := ∀ c, (T c).val < d

/-- Initial-valued semistandard tableaux in the padded type. -/
abbrev InitialSemistandardTableau
    {d s : ℕ} (nu : Fin (d + s) → ℕ) :=
  {T : {T : Tableau nu 0 // IsSemistandard T} // IsInitialValued T.val}

/-- Restrict an initial-valued padded tableau to the original row and
alphabet types. -/
def restrictInitialTableau
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau nu 0) (hT : IsInitialValued T) :
    Tableau (finInitialPart nu) 0 := fun c =>
  ⟨(T (initialStraightCellEquiv htail c)).val,
    hT (initialStraightCellEquiv htail c)⟩

/-- Extend a tableau in the original alphabet to the padded row and alphabet
types. -/
def extendInitialTableau
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau (finInitialPart nu) 0) : Tableau nu 0 := fun c =>
  Fin.castAdd s (T ((initialStraightCellEquiv htail).symm c))

theorem restrictInitialTableau_isSemistandard
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau nu 0) (hT : IsSemistandard T)
    (hinit : IsInitialValued T) :
    IsSemistandard (restrictInitialTableau htail T hinit) := by
  let e := initialStraightCellEquiv htail
  constructor
  · intro c₁ c₂ hrow hcol
    have hh := hT.1 (e c₁) (e c₂) (by
      change Fin.castAdd s c₁.val.1 = Fin.castAdd s c₂.val.1
      exact congrArg (Fin.castAdd s) hrow) hcol
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hh
  · intro c₁ c₂ hcol hrow
    have hh := hT.2 (e c₁) (e c₂) hcol (by
      apply Fin.mk_lt_mk.mpr
      exact Fin.mk_lt_mk.mp hrow)
    apply Fin.mk_lt_mk.mpr
    exact Fin.mk_lt_mk.mp hh

theorem extendInitialTableau_isSemistandard
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau (finInitialPart nu) 0) (hT : IsSemistandard T) :
    IsSemistandard (extendInitialTableau htail T) := by
  let e := initialStraightCellEquiv htail
  constructor
  · intro c₁ c₂ hrow hcol
    have hh := hT.1 (e.symm c₁) (e.symm c₂) (by
      apply Fin.ext
      exact congrArg (fun z : Fin (d + s) => z.val) hrow) hcol
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hh
  · intro c₁ c₂ hcol hrow
    have hh := hT.2 (e.symm c₁) (e.symm c₂) hcol (by
      apply Fin.mk_lt_mk.mpr
      exact Fin.mk_lt_mk.mp hrow)
    apply Fin.mk_lt_mk.mpr
    exact Fin.mk_lt_mk.mp hh

theorem extendInitialTableau_isInitialValued
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau (finInitialPart nu) 0) :
    IsInitialValued (extendInitialTableau htail T) := by
  intro c
  exact (T ((initialStraightCellEquiv htail).symm c)).isLt

theorem restrictInitialTableau_extendInitialTableau
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau (finInitialPart nu) 0) :
    restrictInitialTableau htail (extendInitialTableau htail T)
        (extendInitialTableau_isInitialValued htail T) = T := by
  funext c
  apply Fin.ext
  rfl

theorem extendInitialTableau_restrictInitialTableau
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (T : Tableau nu 0) (hinit : IsInitialValued T) :
    extendInitialTableau htail (restrictInitialTableau htail T hinit) = T := by
  funext c
  apply Fin.ext
  rfl

/-- Initial-valued padded tableaux are equivalent to ordinary tableaux in
the original `d` rows and alphabet. -/
noncomputable def initialSemistandardTableauEquiv
    {d s : ℕ} {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0) :
    InitialSemistandardTableau nu ≃
      {T : Tableau (finInitialPart nu) 0 // IsSemistandard T} where
  toFun T := ⟨restrictInitialTableau htail T.val.val T.property,
    restrictInitialTableau_isSemistandard htail T.val.val T.val.property
      T.property⟩
  invFun T := ⟨⟨extendInitialTableau htail T.val,
      extendInitialTableau_isSemistandard htail T.val T.property⟩,
    extendInitialTableau_isInitialValued htail T.val⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    exact extendInitialTableau_restrictInitialTableau htail T.val.val
      T.property
  right_inv T := by
    apply Subtype.ext
    exact restrictInitialTableau_extendInitialTableau htail T.val

/-- The monomial of an initial-valued tableau agrees with the monomial of
its restricted tableau after zero padding. -/
theorem aeval_xPow_content_zeroPad_eq_restrict
    {R : Type*} [CommRing R] {d s : ℕ}
    {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (x : Fin d → R) (T : Tableau nu 0) (hinit : IsInitialValued T) :
    MvPolynomial.aeval (finZeroPad s x)
        (xPow (contentTableau T) : MvPolynomial (Fin (d + s)) R) =
      MvPolynomial.aeval x
        (xPow (contentTableau (restrictInitialTableau htail T hinit)) :
          MvPolynomial (Fin d) R) := by
  rw [aeval_xPow_content_eq_prod_cells,
    aeval_xPow_content_eq_prod_cells]
  symm
  apply Fintype.prod_equiv (initialStraightCellEquiv htail)
  intro c
  let v := T (initialStraightCellEquiv htail c)
  let vd : Fin d := ⟨v.val, hinit (initialStraightCellEquiv htail c)⟩
  have hv : v = Fin.castAdd s vd := by
    apply Fin.ext
    rfl
  change x vd = finZeroPad s x v
  rw [hv, finZeroPad_castAdd]

/-- Schur evaluation is stable under zero padding when the partition has no
tail rows. -/
theorem aeval_schurPoly_zeroPad_eq_of_tail_zero
    {R : Type*} [CommRing R] {d s : ℕ}
    {nu : Fin (d + s) → ℕ}
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (x : Fin d → R) :
    MvPolynomial.aeval (finZeroPad s x)
        (schurPoly nu : MvPolynomial (Fin (d + s)) R) =
    MvPolynomial.aeval x
        (schurPoly (finInitialPart nu) : MvPolynomial (Fin d) R) := by
  classical
  unfold schurPoly skewSchurPoly
  rw [map_sum, map_sum]
  let A := {T : Tableau nu 0 // IsSemistandard T}
  let B := {T : Tableau (finInitialPart nu) 0 // IsSemistandard T}
  let f : A → R := fun T => MvPolynomial.aeval (finZeroPad s x)
    (xPow (contentTableau T.val) : MvPolynomial (Fin (d + s)) R)
  let g : B → R := fun T => MvPolynomial.aeval x
    (xPow (contentTableau T.val) : MvPolynomial (Fin d) R)
  let good : Finset A := Finset.univ.filter fun T => IsInitialValued T.val
  change (∑ T : A, f T) = ∑ T : B, g T
  have hbad : ∀ T ∈ (Finset.univ : Finset A), T ∉ good → f T = 0 := by
    intro T hT hTbad
    have hnot : ¬IsInitialValued T.val := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and]
        using hTbad
    unfold IsInitialValued at hnot
    push Not at hnot
    obtain ⟨c, hc⟩ := hnot
    apply aeval_xPow_content_zeroPad_eq_zero_of_entry x T.val c
    omega
  have hrestrict : (∑ T ∈ good, f T) = ∑ T : A, f T := by
    calc
      (∑ T ∈ good, f T) =
          ∑ T ∈ (Finset.univ : Finset A), f T := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro T hT hTgood
        exact hbad T hT hTgood
      _ = ∑ T : A, f T := by simp
  rw [← hrestrict]
  rw [← Finset.sum_attach]
  let eGood : {T // T ∈ good} ≃ InitialSemistandardTableau nu :=
    { toFun := fun T => ⟨T.val, by
        simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          using T.property⟩
      invFun := fun T => ⟨T.val, by
        simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          using T.property⟩
      left_inv := by intro T; rfl
      right_inv := by intro T; rfl }
  let e := eGood.trans (initialSemistandardTableauEquiv htail)
  apply Fintype.sum_equiv e
  intro T
  have hinit : IsInitialValued T.val.val := by
    simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      using T.property
  exact aeval_xPow_content_zeroPad_eq_restrict htail x T.val.val
    hinit

/-- A padded quantum Schur specialization is strictly positive when the
partition has no tail rows and lies in the level-`r` alcove. -/
theorem aeval_schurPoly_zeroPad_quantum_eq_coe_pos
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    {nu : Fin (d + s) → ℕ} (hnu : _root_.IsNPartition nu)
    (htail : ∀ i, d ≤ i.val → nu i = 0)
    (hbound : ∀ i, nu i ≤ r) :
    ∃ x : ℝ, 0 < x ∧
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (schurPoly nu : MvPolynomial (Fin (d + s)) ℂ) = (x : ℂ) := by
  have hpart : IsPartitionVector (finInitialPart nu) := by
    intro i j hij
    exact finInitialPart_isNPartition hnu i j hij.le
  have hbound' : ∀ i, finInitialPart nu i ≤ r := by
    intro i
    exact hbound (Fin.castAdd s i)
  obtain ⟨x, hx, heq⟩ := quantumSchurValue_eq_coe_pos hr hd hpart hbound'
  refine ⟨x, hx, ?_⟩
  rw [aeval_schurPoly_zeroPad_eq_of_tail_zero htail]
  exact heq

/-- Every padded quantum Schur specialization in the adjacent closed
alcove is a nonnegative real number; partitions with tail rows specialize
to zero. -/
theorem aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    {nu : Fin (d + s) → ℕ} (hnu : _root_.IsNPartition nu)
    (hbound : ∀ i, nu i ≤ r + 1) :
    ∃ x : ℝ, 0 ≤ x ∧
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (schurPoly nu : MvPolynomial (Fin (d + s)) ℂ) = (x : ℂ) := by
  let tailZero : Fin (d + s) := Fin.natAdd d (⟨0, hs⟩ : Fin s)
  by_cases htailPos : 0 < nu tailZero
  · refine ⟨0, le_rfl, ?_⟩
    rw [aeval_schurPoly_zeroPad_eq_zero_of_tail_pos hs hnu htailPos]
    norm_num
  · have htailZero : nu tailZero = 0 := by omega
    have htail : ∀ i, d ≤ i.val → nu i = 0 := by
      intro i hi
      have hle : tailZero ≤ i := by
        apply Fin.mk_le_mk.mpr
        simp only [tailZero, Fin.val_natAdd]
        omega
      have hpart := hnu tailZero i hle
      omega
    have hpart : IsPartitionVector (finInitialPart nu) := by
      intro i j hij
      exact finInitialPart_isNPartition hnu i j hij.le
    have hbound' : ∀ i, finInitialPart nu i ≤ r + 1 := by
      intro i
      exact hbound (Fin.castAdd s i)
    obtain ⟨x, hx, heq⟩ := quantumSchurValue_eq_coe_nonneg
      hr hd hpart hbound'
    refine ⟨x, hx, ?_⟩
    rw [aeval_schurPoly_zeroPad_eq_of_tail_zero htail]
    exact heq

/-! ## Existence of a short Littlewood--Richardson summand -/

/-- A skew shape with columns of height at most `d` has strictly positive
specialization at `d` ones followed by zeros. -/
theorem aeval_skewSchurPoly_zeroPad_one_pos_of_columnHeight
    {d s q : ℕ}
    {lam mu : Fin (d + s) → ℕ} {lamt muT : Fin q → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ q)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hcolumnHeight : ∀ c, lamt c - muT c ≤ d) :
    0 < MvPolynomial.aeval
      (finZeroPad s (fun _ : Fin d => (1 : ℤ)))
      (skewSchurPoly lam mu : MvPolynomial (Fin (d + s)) ℤ) := by
  unfold skewSchurPoly
  rw [map_sum]
  let f : {T : Tableau lam mu // IsSemistandard T} → ℤ := fun T =>
    MvPolynomial.aeval (finZeroPad s (fun _ : Fin d => (1 : ℤ)))
      (xPow (contentTableau T.val) : MvPolynomial (Fin (d + s)) ℤ)
  change 0 < ∑ T : {T : Tableau lam mu // IsSemistandard T}, f T
  apply Finset.sum_pos'
  · intro T hT
    unfold f
    rw [aeval_xPow_content_eq_prod_cells]
    apply Finset.prod_nonneg
    intro c hc
    by_cases hlow : (T.val c).val < d
    · have heq : T.val c = Fin.castAdd s
        ⟨(T.val c).val, hlow⟩ := by
        apply Fin.ext
        rfl
      rw [heq, finZeroPad_castAdd]
      norm_num
    · rw [finZeroPad_eq_zero_of_le _ _ (by omega)]
  · obtain ⟨T, hinit⟩ :=
      exists_initial_semistandard_tableau_of_columnHeight
        hlam hmu hlamt hmuT htransLam htransMu hwidth
        hcontained hcolumnHeight
    refine ⟨T, Finset.mem_univ T, ?_⟩
    unfold f
    rw [aeval_xPow_content_eq_prod_cells]
    have hone : ∀ c,
        finZeroPad s (fun _ : Fin d => (1 : ℤ)) (T.val c) = 1 := by
      intro c
      have heq : T.val c = Fin.castAdd s
          ⟨(T.val c).val, hinit c⟩ := by
        apply Fin.ext
        rfl
      rw [heq, finZeroPad_castAdd]
    simp_rw [hone]
    simp

/-- The Littlewood--Richardson expansion of a skew shape with column height
at most `d` contains a summand whose partition has no tail rows. -/
theorem exists_zeroYamanouchi_tail_zero_of_columnHeight
    {d s q : ℕ} (hs : 0 < s)
    {lam mu : Fin (d + s) → ℕ} {lamt muT : Fin q → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ q)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hcolumnHeight : ∀ c, lamt c - muT c ≤ d) :
    ∃ T : {T : Tableau lam mu // IsYamanouchi 0 T},
      contentTableau T.val (Fin.natAdd d (⟨0, hs⟩ : Fin s)) = 0 := by
  let tail : Fin (d + s) := Fin.natAdd d (⟨0, hs⟩ : Fin s)
  by_contra hnone
  push Not at hnone
  have htailPos : ∀ T : {T : Tableau lam mu // IsYamanouchi 0 T},
      0 < contentTableau T.val tail := by
    intro T
    have hne := hnone T
    have hne' : contentTableau T.val tail ≠ 0 := by
      intro hz
      apply hne
      simpa only [tail] using hz
    exact Nat.pos_of_ne_zero hne'
  let onePad : Fin (d + s) → ℤ :=
    finZeroPad s (fun _ : Fin d => (1 : ℤ))
  have hexp := aeval_skewSchurPoly_eq_sum_schur_content
    (R := ℤ) onePad lam mu hlam hmu
  have hsum : (∑ T : {T : Tableau lam mu // IsYamanouchi 0 T},
      MvPolynomial.aeval onePad
        (schurPoly (contentTableau T.val) :
          MvPolynomial (Fin (d + s)) ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    apply aeval_schurPoly_zeroPad_eq_zero_of_tail_pos hs
      T.prop.isNPartition_content_of_zero
    exact htailPos T
  rw [hsum] at hexp
  have hleft := aeval_skewSchurPoly_zeroPad_one_pos_of_columnHeight
    hlam hmu hlamt hmuT htransLam htransMu hwidth hcontained
    hcolumnHeight
  change 0 < MvPolynomial.aeval onePad
    (skewSchurPoly lam mu : MvPolynomial (Fin (d + s)) ℤ) at hleft
  rw [hexp] at hleft
  exact (lt_irrefl 0 hleft)

/-! ## Padded skew-Schur positivity -/

/-- Padded quantum skew-Schur specializations are nonnegative at outer
width `r+1`. -/
theorem aeval_skewSchurPoly_zeroPad_quantum_eq_coe_nonneg
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    {lam mu : Fin (d + s) → ℕ}
    (hlam : _root_.IsNPartition lam) (hmu : _root_.IsNPartition mu)
    (hwidth : lam ⟨0, by omega⟩ ≤ r + 1) :
    ∃ x : ℝ, 0 ≤ x ∧
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (skewSchurPoly lam mu : MvPolynomial (Fin (d + s)) ℂ) =
          (x : ℂ) := by
  let Y := {T : Tableau lam mu // IsYamanouchi 0 T}
  have hN : 0 < d + s := by omega
  let zeroN : Fin (d + s) := ⟨0, hN⟩
  have hcontentBound : ∀ T : Y, ∀ i,
      contentTableau T.val i ≤ r + 1 := by
    intro T i
    have hpart := T.prop.isNPartition_content_of_zero zeroN i (by
      apply Fin.mk_le_mk.mpr
      exact Nat.zero_le i.val)
    exact hpart.trans ((contentTableau_zero_le_firstPart hN
      hlam T.val T.prop.isSemistandard).trans hwidth)
  let termReal : Y → ℝ := fun T => Classical.choose
    (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
      T.prop.isNPartition_content_of_zero (hcontentBound T))
  let x : ℝ := ∑ T : Y, termReal T
  have hx : 0 ≤ x := by
    dsimp only [x]
    apply Finset.sum_nonneg
    intro T hT
    exact (Classical.choose_spec
      (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
        T.prop.isNPartition_content_of_zero (hcontentBound T))).1
  refine ⟨x, hx, ?_⟩
  rw [aeval_skewSchurPoly_eq_sum_schur_content
    (R := ℂ) (finZeroPad s (quantumAlphabetY r d)) lam mu hlam hmu]
  have hterm : ∀ T : Y,
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (schurPoly (contentTableau T.val) :
          MvPolynomial (Fin (d + s)) ℂ) = (termReal T : ℂ) := by
    intro T
    exact (Classical.choose_spec
      (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
        T.prop.isNPartition_content_of_zero (hcontentBound T))).2
  simp_rw [hterm]
  exact_mod_cast rfl

/-- Padded quantum skew-Schur specializations are strictly positive at outer
width `r` when every skew column has height at most `d`. -/
theorem aeval_skewSchurPoly_zeroPad_quantum_eq_coe_pos
    {r d s q : ℕ} (hr : 0 < r) (hd : 0 < d) (hs : 0 < s)
    {lam mu : Fin (d + s) → ℕ} {lamt muT : Fin q → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hshapeWidth : ∀ a, lam a ≤ q)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hcolumnHeight : ∀ c, lamt c - muT c ≤ d)
    (hwidth : lam ⟨0, by omega⟩ ≤ r) :
    ∃ x : ℝ, 0 < x ∧
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (skewSchurPoly lam mu : MvPolynomial (Fin (d + s)) ℂ) =
          (x : ℂ) := by
  let Y := {T : Tableau lam mu // IsYamanouchi 0 T}
  have hN : 0 < d + s := by omega
  let zeroN : Fin (d + s) := ⟨0, hN⟩
  have hcontentBound : ∀ T : Y, ∀ i,
      contentTableau T.val i ≤ r + 1 := by
    intro T i
    have hpart := T.prop.isNPartition_content_of_zero zeroN i (by
      apply Fin.mk_le_mk.mpr
      exact Nat.zero_le i.val)
    exact hpart.trans ((contentTableau_zero_le_firstPart hN
      hlam T.val T.prop.isSemistandard).trans (hwidth.trans (by omega)))
  let termReal : Y → ℝ := fun T => Classical.choose
    (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
      T.prop.isNPartition_content_of_zero (hcontentBound T))
  obtain ⟨Tpos, htailZero⟩ :=
    exists_zeroYamanouchi_tail_zero_of_columnHeight hs
      hlam hmu hlamt hmuT htransLam htransMu hshapeWidth
      hcontained hcolumnHeight
  have htail : ∀ i, d ≤ i.val →
      contentTableau Tpos.val i = 0 := by
    intro i hi
    let tail : Fin (d + s) := Fin.natAdd d (⟨0, hs⟩ : Fin s)
    have hle : tail ≤ i := by
      apply Fin.mk_le_mk.mpr
      simp only [tail, Fin.val_natAdd]
      omega
    have hpart := Tpos.prop.isNPartition_content_of_zero tail i hle
    have hz : contentTableau Tpos.val tail = 0 := by
      simpa only [tail] using htailZero
    omega
  have hboundPos : ∀ i, contentTableau Tpos.val i ≤ r := by
    intro i
    have hpart := Tpos.prop.isNPartition_content_of_zero
      zeroN i (by
        apply Fin.mk_le_mk.mpr
        exact Nat.zero_le i.val)
    exact hpart.trans ((contentTableau_zero_le_firstPart hN
      hlam Tpos.val Tpos.prop.isSemistandard).trans hwidth)
  obtain ⟨y, hy, hyEq⟩ :=
    aeval_schurPoly_zeroPad_quantum_eq_coe_pos hr hd hs
      Tpos.prop.isNPartition_content_of_zero htail hboundPos
  have htermPos : 0 < termReal Tpos := by
    have hxEq := (Classical.choose_spec
      (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
        Tpos.prop.isNPartition_content_of_zero (hcontentBound Tpos))).2
    have hcast : (termReal Tpos : ℂ) = (y : ℂ) := hxEq.symm.trans hyEq
    have hreal : termReal Tpos = y := by exact_mod_cast hcast
    rwa [hreal]
  let x : ℝ := ∑ T : Y, termReal T
  have hx : 0 < x := by
    dsimp only [x]
    apply Finset.sum_pos'
    · intro T hT
      exact (Classical.choose_spec
        (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
          T.prop.isNPartition_content_of_zero (hcontentBound T))).1
    · exact ⟨Tpos, Finset.mem_univ Tpos, htermPos⟩
  refine ⟨x, hx, ?_⟩
  rw [aeval_skewSchurPoly_eq_sum_schur_content
    (R := ℂ) (finZeroPad s (quantumAlphabetY r d)) lam mu hlam hmu]
  have hterm : ∀ T : Y,
      MvPolynomial.aeval (finZeroPad s (quantumAlphabetY r d))
        (schurPoly (contentTableau T.val) :
          MvPolynomial (Fin (d + s)) ℂ) = (termReal T : ℂ) := by
    intro T
    exact (Classical.choose_spec
      (aeval_schurPoly_zeroPad_quantum_eq_coe_nonneg hr hd hs
        T.prop.isNPartition_content_of_zero (hcontentBound T))).2
  simp_rw [hterm]
  exact_mod_cast rfl

end

end FurtherToeplitzPositroids
