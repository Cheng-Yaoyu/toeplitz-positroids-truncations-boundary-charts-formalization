import FurtherToeplitzPositroids.QuantumBinomial
import ToeplitzPositroids.Edrei.GammaZeroSupport
import ToeplitzPositroids.Edrei.PositroidCorollary
import ToeplitzPositroids.Matrix.Reversal

/-!
# Exact lattice-path support families

This module formalizes the index inequalities in Proposition 7.1 and the
intermediate-index feasibility calculation in Theorem 7.3.
-/

namespace FurtherToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- Translate a local finite column selection by a natural offset. -/
def shiftedNaturalSelection {r n : ℕ} (v : ℕ)
    (K : Fin r ↪o Fin n) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ v + (K i).val)
    (fun _ _ h ↦ Nat.add_lt_add_left (K.strictMono h) v)

@[simp]
theorem shiftedNaturalSelection_apply
    {r n : ℕ} (v : ℕ) (K : Fin r ↪o Fin n) (i : Fin r) :
    shiftedNaturalSelection v K i = v + (K i).val :=
  rfl

/-- Proposition 7.1, exact index form.  The first family is the lower
lattice-path bound.  When `gamma=0`, the second family is the upper hook
bound; when `gamma>0`, it is vacuous. -/
theorem finiteEdrei_rowSection_pos_iff
    {p q r n : ℕ} (D : FiniteEdreiData p q)
    (rows : Fin r ↪o ℕ) (v : ℕ) (K : Fin r ↪o Fin n) :
    0 < D.toeplitzMinor rows (shiftedNaturalSelection v K) ↔
      (∀ i, rows i ≤ v + (K i).val) ∧
        (D.gamma = 0 →
          ∀ i : Fin r, p < i.val + 1 →
            v + (K ⟨i.val - p, by omega⟩).val + p ≤ rows i + q) := by
  rcases D.gamma_nonneg.eq_or_lt with hgamma | hgamma
  · have hgamma0 : D.gamma = 0 := hgamma.symm
    rw [Edrei.FiniteEdreiData.toeplitzMinor_pos_iff_minorSupportCondition_of_explicit_gamma_zero
      D hgamma0]
    unfold FiniteEdreiData.MinorSupportCondition
    simp only [hgamma0, forall_const]
    constructor
    · rintro ⟨hstruct, hhook⟩
      refine ⟨fun i ↦ by simpa using hstruct i, ?_⟩
      intro i hi
      have h := hhook i hi
      change v + (K ⟨i.val - p, by omega⟩).val + 1 + p ≤ rows i + 1 + q at h
      omega
    · rintro ⟨hstruct, hhook⟩
      refine ⟨fun i ↦ by simpa using hstruct i, ?_⟩
      intro i hi
      have h := hhook i hi
      change v + (K ⟨i.val - p, by omega⟩).val + 1 + p ≤ rows i + 1 + q
      omega
  · rw [D.toeplitzMinor_pos_iff_componentwise_le_of_gamma_pos hgamma]
    constructor
    · intro h
      refine ⟨fun i ↦ by simpa using h i, ?_⟩
      intro hzero
      exact (hgamma.ne' hzero).elim
    · rintro ⟨h, _⟩ i
      simpa using h i

/-- Corollary 7.2: for consecutive rows, the lower bound depends only on the
row/column offset. -/
theorem finiteEdrei_consecutiveRows_lowerBound
    {p q r n : ℕ} (D : FiniteEdreiData p q)
    (u v : ℕ) (K : Fin r ↪o Fin n)
    (hpos : 0 < D.toeplitzMinor
      (OrderEmbedding.ofStrictMono (fun i : Fin r ↦ u + i.val)
        (fun _ _ h ↦ Nat.add_lt_add_left h u))
      (shiftedNaturalSelection v K)) :
    ∀ i : Fin r, u + i.val ≤ v + (K i).val := by
  exact (finiteEdrei_rowSection_pos_iff D _ v K).1 hpos |>.1

/-- For a pure finite numerator product (`p=0`, `gamma=0`), every natural
Toeplitz minor is positive exactly on the finite upper band. -/
theorem finiteEdrei_pureBeta_toeplitzMinor_pos_iff
    {q r n : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0)
    (rows : Fin r ↪o ℕ) (cols : Fin r ↪o Fin n) :
    0 < D.toeplitzMinor rows (finiteSelectionNatural cols) ↔
      ∀ i, rows i ≤ (cols i).val ∧ (cols i).val ≤ rows i + q := by
  have h := finiteEdrei_rowSection_pos_iff D rows 0 cols
  have hselection : shiftedNaturalSelection 0 cols = finiteSelectionNatural cols := by
    apply RelEmbedding.ext
    intro i
    simp
  rw [hselection] at h
  constructor
  · intro hpos
    have hs := h.1 hpos
    intro i
    refine ⟨by simpa using hs.1 i, ?_⟩
    have hu := hs.2 hgamma i (by omega)
    simpa using hu
  · intro hbounds
    apply h.2
    refine ⟨fun i ↦ by simpa using (hbounds i).1, ?_⟩
    intro _ i hi
    have hu := (hbounds i).2
    simpa using hu

/-- A pure `q`-letter beta product has no coefficient above degree `q`. -/
theorem finiteEdrei_pureBeta_coefficient_eq_zero_of_lt
    {q : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0)
    {z : ℤ} (hz : q < z) :
    D.coefficient z = 0 := by
  have hzNonneg : 0 ≤ z := by omega
  let t : ℕ := z.toNat
  have htCast : (t : ℤ) = z := Int.toNat_of_nonneg hzNonneg
  let rows : Fin 1 ↪o ℕ := singletonOrderEmbedding 0
  let cols : Fin 1 ↪o Fin (t + 1) := singletonOrderEmbedding ⟨t, by omega⟩
  have hnotPos : ¬0 < D.toeplitzMinor rows (finiteSelectionNatural cols) := by
    rw [finiteEdrei_pureBeta_toeplitzMinor_pos_iff D hgamma]
    intro h
    have ht := (h 0).2
    change t ≤ 0 + q at ht
    omega
  have hnonneg := D.toeplitzMinor_nonneg rows (finiteSelectionNatural cols)
  have hminorZero : D.toeplitzMinor rows (finiteSelectionNatural cols) = 0 :=
    le_antisymm (le_of_not_gt hnotPos) hnonneg
  rw [FiniteEdreiData.toeplitzMinor, oneSidedToeplitzMinor,
    Matrix.det_fin_one] at hminorZero
  change D.coefficient ((t : ℤ) - 0) = 0 at hminorZero
  rwa [sub_zero, htCast] at hminorZero

/-- The `i`-th value of an increasing `r`-selection is at least `i`. -/
theorem orderEmbedding_fin_lower_bound
    {r n : ℕ} (K : Fin r ↪o Fin n) (i : Fin r) :
    i.val ≤ (K i).val := by
  have aux : ∀ q : ℕ, ∀ j : Fin r, j.val = q → q ≤ (K j).val := by
    intro q
    induction q with
    | zero => intro j hj; omega
    | succ q ih =>
        intro j hj
        let pred : Fin r := ⟨q, by omega⟩
        have hpred : pred < j := by
          apply Fin.mk_lt_mk.mpr
          dsimp only [pred]
          omega
        have hstep := K.strictMono hpred
        have ihpred := ih pred rfl
        omega
  exact aux i.val i rfl

/-- The `i`-th value of an increasing `r`-selection leaves room for all
remaining selected values. -/
theorem orderEmbedding_fin_upper_bound
    {r n : ℕ} (K : Fin r ↪o Fin n) (i : Fin r) :
    (K i).val ≤ n - r + i.val := by
  let Krev : Fin r ↪o Fin n := reverseOrderEmbedding K
  have h := orderEmbedding_fin_lower_bound Krev i.rev
  have hi := i.isLt
  have hKi := (K i).isLt
  simp only [Krev, reverseOrderEmbedding_apply, Fin.rev_rev, Fin.val_rev] at h
  omega

/-- Proposition 7.1 in explicit zero-based lattice-path form, including the
automatic bounds on every increasing local selection. -/
theorem finiteEdrei_rowSection_latticePathBounds
    {p q r n : ℕ} (D : FiniteEdreiData p q)
    (rows : Fin r ↪o ℕ) (v : ℕ) (K : Fin r ↪o Fin n) :
    0 < D.toeplitzMinor rows (shiftedNaturalSelection v K) ↔
      ∀ t,
        t.val ≤ (K t).val ∧
          rows t ≤ v + (K t).val ∧
          (K t).val ≤ n - r + t.val ∧
          (D.gamma = 0 → ∀ ht : t.val + p < r,
            v + (K t).val + p ≤ rows ⟨t.val + p, ht⟩ + q) := by
  rw [finiteEdrei_rowSection_pos_iff]
  constructor
  · rintro ⟨hlower, hhook⟩ t
    refine ⟨orderEmbedding_fin_lower_bound K t, hlower t,
      orderEmbedding_fin_upper_bound K t, ?_⟩
    intro hgamma ht
    let i : Fin r := ⟨t.val + p, ht⟩
    have hi : p < i.val + 1 := by dsimp only [i]; omega
    have hu := hhook hgamma i hi
    have hindex : (⟨i.val - p, by omega⟩ : Fin r) = t := by
      apply Fin.ext
      dsimp only [i]
      omega
    rwa [hindex] at hu
  · intro hbounds
    refine ⟨fun t ↦ (hbounds t).2.1, ?_⟩
    intro hgamma i hi
    let t : Fin r := ⟨i.val - p, by omega⟩
    have ht : t.val + p < r := by
      dsimp only [t]
      have hiBound := i.isLt
      omega
    have hu := (hbounds t).2.2.2 hgamma ht
    have hindex : (⟨t.val + p, by omega⟩ : Fin r) = i := by
      apply Fin.ext
      dsimp only [t]
      omega
    rwa [hindex] at hu

/-- Equation (46), in zero-based local-column coordinates, follows from the
two-sided difference bounds together with the automatic bounds on an
increasing local selection. -/
theorem twoSided_localSelection_bounds_iff
    {r n : ℕ} (qPlus qMinus v : ℕ)
    (I : Fin r ↪o ℤ) (K : Fin r ↪o Fin n) :
    (∀ t, -(qMinus : ℤ) ≤ (v + (K t).val : ℕ) - I t ∧
        (v + (K t).val : ℕ) - I t ≤ qPlus) ↔
      ∀ t,
        max (t.val : ℤ) (I t - v - qMinus) ≤ (K t).val ∧
          (K t).val ≤
            min ((n - r + t.val : ℕ) : ℤ) (I t - v + qPlus) := by
  constructor
  · intro h t
    have ht := h t
    have hlower := orderEmbedding_fin_lower_bound K t
    have hupper := orderEmbedding_fin_upper_bound K t
    rw [max_le_iff, le_min_iff]
    constructor
    · constructor
      · exact_mod_cast hlower
      · omega
    · constructor
      · exact_mod_cast hupper
      · omega
  · intro h t
    have ht := h t
    rw [max_le_iff, le_min_iff] at ht
    constructor <;> omega

/-! ## Two-sided finite-band intermediate indices -/

/-- The componentwise inequalities that a Cauchy--Binet intermediate tuple
must satisfy in Theorem 7.3. -/
def TwoSidedIntermediateBounds {r : ℕ} (qPlus qMinus : ℕ)
    (I J K : Fin r ↪o ℤ) : Prop :=
  ∀ t, I t ≤ K t ∧ K t ≤ I t + qPlus ∧
    J t ≤ K t ∧ K t ≤ J t + qMinus

/-- The pointwise maximum of two increasing integer tuples is increasing. -/
def maxOrderEmbedding {r : ℕ} (I J : Fin r ↪o ℤ) : Fin r ↪o ℤ :=
  OrderEmbedding.ofStrictMono
    (fun t ↦ max (I t) (J t))
    (fun a b hab ↦ by
      rw [max_lt_iff]
      exact ⟨(I.strictMono hab).trans_le (le_max_left _ _),
        (J.strictMono hab).trans_le (le_max_right _ _)⟩)

/-- The interval inequalities in equation (45) are exactly the existence of
an increasing intermediate tuple satisfying both one-sided supports. -/
theorem exists_twoSidedIntermediate_iff
    {r : ℕ} (qPlus qMinus : ℕ) (I J : Fin r ↪o ℤ) :
    (∃ K : Fin r ↪o ℤ, TwoSidedIntermediateBounds qPlus qMinus I J K) ↔
      ∀ t, -(qMinus : ℤ) ≤ J t - I t ∧ J t - I t ≤ qPlus := by
  constructor
  · rintro ⟨K, hK⟩ t
    have ht := hK t
    constructor <;> omega
  · intro h
    refine ⟨maxOrderEmbedding I J, fun t ↦ ?_⟩
    have ht := h t
    change I t ≤ max (I t) (J t) ∧
      max (I t) (J t) ≤ I t + qPlus ∧
      J t ≤ max (I t) (J t) ∧
      max (I t) (J t) ≤ J t + qMinus
    constructor
    · exact le_max_left _ _
    constructor
    · exact max_le (by omega) (by omega)
    constructor
    · exact le_max_right _ _
    · exact max_le (by omega) (by omega)

/-! ## Finite Cauchy--Binet support assembly -/

/-- For a product of two totally nonnegative finite matrices, a selected
minor is positive exactly when some Cauchy--Binet intermediate minor pair is
positive.  This is the subtraction-free support step in Theorem 7.3. -/
theorem orderedMinor_mul_pos_iff_exists_intermediate
    {r m k n : ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ}
    {L : Matrix (Fin k) (Fin n) ℝ}
    (hU : TotallyNonnegative U) (hL : TotallyNonnegative L)
    (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n) :
    0 < orderedMinor (U * L) rows cols ↔
      ∃ middle : Fin r ↪o Fin k,
        0 < orderedMinor U rows middle ∧
          0 < orderedMinor L middle cols := by
  have hsubmatrix :
      (U * L).submatrix rows cols =
        U.submatrix rows id * L.submatrix id cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [orderedMinor, hsubmatrix, Matrix.det_mul_eq_sum_orderedMinor]
  let term : (Fin r ↪o Fin k) → ℝ := fun middle ↦
    orderedMinor U rows middle * orderedMinor L middle cols
  have htermNonneg : ∀ middle, 0 ≤ term middle := by
    intro middle
    exact mul_nonneg
      (hU.orderedMinor_nonneg rows middle)
      (hL.orderedMinor_nonneg middle cols)
  constructor
  · intro hsum
    have hexists : ∃ middle : Fin r ↪o Fin k, 0 < term middle := by
      simpa [term] using
        (Finset.sum_pos_iff_of_nonneg
          (s := Finset.univ) (f := term)
          (fun middle _ ↦ htermNonneg middle)).1 hsum
    obtain ⟨middle, hmiddle⟩ := hexists
    have hUminor := hU.orderedMinor_nonneg rows middle
    have hLminor := hL.orderedMinor_nonneg middle cols
    exact ⟨middle,
      pos_of_mul_pos_left hmiddle hLminor,
      pos_of_mul_pos_right hmiddle hUminor⟩
  · rintro ⟨middle, hUmiddle, hLmiddle⟩
    apply Finset.sum_pos'
    · intro q _
      exact htermNonneg q
    · refine ⟨middle, Finset.mem_univ middle, ?_⟩
      exact mul_pos hUmiddle hLmiddle

/-- Theorem 7.3 at the finite factorization interface.  Exact one-sided
minor support, total nonnegativity, and coverage of every feasible
intermediate tuple imply the stated two-sided difference bounds. -/
theorem orderedMinor_mul_pos_iff_twoSidedBounds
    {r m k n : ℕ} {qPlus qMinus : ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ}
    {L : Matrix (Fin k) (Fin n) ℝ}
    (hU : TotallyNonnegative U) (hL : TotallyNonnegative L)
    (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n)
    (I J : Fin r ↪o ℤ) (ambient : Fin k ↪o ℤ)
    (hUpos : ∀ middle : Fin r ↪o Fin k,
      0 < orderedMinor U rows middle ↔
        ∀ t, I t ≤ ambient (middle t) ∧
          ambient (middle t) ≤ I t + qPlus)
    (hLpos : ∀ middle : Fin r ↪o Fin k,
      0 < orderedMinor L middle cols ↔
        ∀ t, J t ≤ ambient (middle t) ∧
          ambient (middle t) ≤ J t + qMinus)
    (hcover : ∀ K : Fin r ↪o ℤ,
      TwoSidedIntermediateBounds qPlus qMinus I J K →
        ∃ middle : Fin r ↪o Fin k, ∀ t, ambient (middle t) = K t) :
    0 < orderedMinor (U * L) rows cols ↔
      ∀ t, -(qMinus : ℤ) ≤ J t - I t ∧ J t - I t ≤ qPlus := by
  rw [orderedMinor_mul_pos_iff_exists_intermediate hU hL rows cols,
    ← exists_twoSidedIntermediate_iff qPlus qMinus I J]
  constructor
  · rintro ⟨middle, hUmiddle, hLmiddle⟩
    let K : Fin r ↪o ℤ := middle.trans ambient
    refine ⟨K, fun t ↦ ?_⟩
    have hUt := (hUpos middle).1 hUmiddle t
    have hLt := (hLpos middle).1 hLmiddle t
    exact ⟨hUt.1, hUt.2, hLt.1, hLt.2⟩
  · rintro ⟨K, hK⟩
    obtain ⟨middle, hmiddle⟩ := hcover K hK
    refine ⟨middle, (hUpos middle).2 ?_, (hLpos middle).2 ?_⟩
    · intro t
      rw [hmiddle t]
      exact ⟨(hK t).1, (hK t).2.1⟩
    · intro t
      rw [hmiddle t]
      exact ⟨(hK t).2.2.1, (hK t).2.2.2⟩

/-! ## Concrete finite two-sided Edrei factors -/

/-- Regard a finite increasing selection as an integer-valued increasing
tuple. -/
def finiteSelectionInteger {r n : ℕ} (J : Fin r ↪o Fin n) : Fin r ↪o ℤ :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ((J i).val : ℤ))
    (fun x y hij ↦ by
      have hval : (J x).val < (J y).val := J.strictMono hij
      change ((J x).val : ℤ) < ((J y).val : ℤ)
      exact_mod_cast hval)

/-- A finite section of the factorization `U L` in Theorem 7.3. -/
def twoSidedFiniteEdreiSection
    {qPlus qMinus : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (m k n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Dplus.finiteToeplitzSection m k *
    (Dminus.finiteToeplitzSection n k).transpose

/-- The Laurent coefficient obtained by multiplying the upper finite beta
polynomial by the lower reversed beta polynomial. -/
def twoSidedEdreiCoefficient
    {qPlus qMinus : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus) (z : ℤ) : ℝ :=
  ∑ t : Fin (qPlus + 1),
    Dplus.natCoefficient t.val *
      Dminus.coefficient ((t.val : ℤ) - z)

/-- With enough intermediate columns to contain the upper band from every
displayed row, the finite factor product is literally the corresponding
Toeplitz section of the Laurent coefficient function. -/
theorem twoSidedFiniteEdreiSection_eq_toeplitzMatrix
    {qPlus qMinus m k n : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0)
    (hbuffer : ∀ i : Fin m, i.val + qPlus < k) :
    twoSidedFiniteEdreiSection Dplus Dminus m k n =
      toeplitzMatrix m n (twoSidedEdreiCoefficient Dplus Dminus) := by
  ext i j
  rw [twoSidedFiniteEdreiSection, Matrix.mul_apply,
    toeplitzMatrix_apply]
  simp only [FiniteEdreiData.finiteToeplitzSection_apply,
    Matrix.transpose_apply]
  let shift : Fin (qPlus + 1) → Fin k := fun t ↦
    ⟨i.val + t.val, by have ht := t.isLt; have hi := hbuffer i; omega⟩
  let support : Finset (Fin k) := Finset.univ.image shift
  let term : Fin k → ℝ := fun s ↦
    Dplus.coefficient ((s : ℤ) - (i : ℤ)) *
      Dminus.coefficient ((s : ℤ) - (j : ℤ))
  have hzeroOutside : ∀ s ∈ Finset.univ, s ∉ support → term s = 0 := by
    intro s hs hsSupport
    have hplusZero : Dplus.coefficient ((s : ℤ) - (i : ℤ)) = 0 := by
      by_cases hsi : s.val < i.val
      · apply Dplus.coefficient_eq_zero_of_neg
        omega
      · have his : i.val ≤ s.val := by omega
        by_cases hdiff : s.val - i.val ≤ qPlus
        · let t : Fin (qPlus + 1) := ⟨s.val - i.val, by omega⟩
          exfalso
          apply hsSupport
          apply Finset.mem_image.mpr
          refine ⟨t, Finset.mem_univ t, ?_⟩
          apply Fin.ext
          dsimp only [shift, t]
          omega
        · have hindex : (s : ℤ) - (i : ℤ) =
              ((s.val - i.val : ℕ) : ℤ) := by omega
          rw [hindex]
          apply finiteEdrei_pureBeta_coefficient_eq_zero_of_lt
            Dplus hgammaPlus
          exact_mod_cast (lt_of_not_ge hdiff)
    simp [term, hplusZero]
  have hrestricted : (∑ s : Fin k, term s) = ∑ s ∈ support, term s := by
    symm
    exact Finset.sum_subset (Finset.subset_univ support) hzeroOutside
  change (∑ s : Fin k, term s) = twoSidedEdreiCoefficient Dplus Dminus
    ((j : ℤ) - (i : ℤ))
  rw [hrestricted]
  have hshiftInjective : Function.Injective shift := by
    intro x y hxy
    apply Fin.ext
    have hval := congrArg Fin.val hxy
    dsimp only [shift] at hval
    omega
  dsimp only [support]
  rw [Finset.sum_image]
  · unfold twoSidedEdreiCoefficient
    apply Finset.sum_congr rfl
    intro t ht
    have hplusIndex : ((shift t : Fin k) : ℤ) - (i : ℤ) = (t.val : ℤ) := by
      dsimp only [shift]
      omega
    have hminusIndex : ((shift t : Fin k) : ℤ) - (j : ℤ) =
        (t.val : ℤ) - ((j : ℤ) - (i : ℤ)) := by
      dsimp only [shift]
      omega
    dsimp only [term]
    rw [hplusIndex, hminusIndex, FiniteEdreiData.coefficient]
    simp only [Int.natCast_nonneg, if_pos, Int.toNat_natCast]
  · intro x hx y hy hxy
    exact hshiftInjective hxy

/-- Every concrete finite factorized section is totally nonnegative. -/
theorem twoSidedFiniteEdreiSection_totallyNonnegative
    {qPlus qMinus : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (m k n : ℕ) :
    TotallyNonnegative (twoSidedFiniteEdreiSection Dplus Dminus m k n) := by
  apply totallyNonnegative_mul
  · exact Dplus.finiteToeplitzSection_totallyNonnegative m k
  · exact (Dminus.finiteToeplitzSection_totallyNonnegative n k).transpose

/-- Exact support of a buffered finite section of the two-sided factorization.
The buffer hypothesis merely ensures that every feasible intermediate tuple
is present among the `k` intermediate indices. -/
theorem twoSidedFiniteEdreiSection_minor_pos_iff
    {qPlus qMinus r m k n : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0)
    (hgammaMinus : Dminus.gamma = 0)
    (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n)
    (hrowBuffer : ∀ t, (rows t).val + qPlus < k) :
    0 < orderedMinor
        (twoSidedFiniteEdreiSection Dplus Dminus m k n) rows cols ↔
      ∀ t, -(qMinus : ℤ) ≤ ((cols t).val : ℤ) - ((rows t).val : ℤ) ∧
        ((cols t).val : ℤ) - ((rows t).val : ℤ) ≤ qPlus := by
  let U : Matrix (Fin m) (Fin k) ℝ := Dplus.finiteToeplitzSection m k
  let L : Matrix (Fin k) (Fin n) ℝ :=
    (Dminus.finiteToeplitzSection n k).transpose
  let I : Fin r ↪o ℤ := finiteSelectionInteger rows
  let J : Fin r ↪o ℤ := finiteSelectionInteger cols
  let ambient : Fin k ↪o ℤ := finiteSelectionInteger (allRows k)
  have hU : TotallyNonnegative U :=
    Dplus.finiteToeplitzSection_totallyNonnegative m k
  have hL : TotallyNonnegative L :=
    (Dminus.finiteToeplitzSection_totallyNonnegative n k).transpose
  have hUpos : ∀ middle : Fin r ↪o Fin k,
      0 < orderedMinor U rows middle ↔
        ∀ t, I t ≤ ambient (middle t) ∧
          ambient (middle t) ≤ I t + qPlus := by
    intro middle
    rw [Dplus.orderedMinor_finiteToeplitzSection_eq_toeplitzMinor]
    have hsupport := finiteEdrei_pureBeta_toeplitzMinor_pos_iff
      Dplus hgammaPlus (finiteSelectionNatural rows) middle
    constructor
    · intro hpos t
      have ht := hsupport.1 hpos t
      change ((rows t).val : ℤ) ≤ ((middle t).val : ℤ) ∧
        ((middle t).val : ℤ) ≤ (rows t).val + qPlus
      constructor
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2
    · intro hbounds
      apply hsupport.2
      intro t
      have ht := hbounds t
      change ((rows t).val : ℤ) ≤ ((middle t).val : ℤ) ∧
        ((middle t).val : ℤ) ≤ (rows t).val + qPlus at ht
      constructor
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2
  have hLpos : ∀ middle : Fin r ↪o Fin k,
      0 < orderedMinor L middle cols ↔
        ∀ t, J t ≤ ambient (middle t) ∧
          ambient (middle t) ≤ J t + qMinus := by
    intro middle
    dsimp only [L]
    rw [orderedMinor_transpose,
      Dminus.orderedMinor_finiteToeplitzSection_eq_toeplitzMinor]
    have hsupport := finiteEdrei_pureBeta_toeplitzMinor_pos_iff
      Dminus hgammaMinus (finiteSelectionNatural cols) middle
    constructor
    · intro hpos t
      have ht := hsupport.1 hpos t
      change ((cols t).val : ℤ) ≤ ((middle t).val : ℤ) ∧
        ((middle t).val : ℤ) ≤ (cols t).val + qMinus
      constructor
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2
    · intro hbounds
      apply hsupport.2
      intro t
      have ht := hbounds t
      change ((cols t).val : ℤ) ≤ ((middle t).val : ℤ) ∧
        ((middle t).val : ℤ) ≤ (cols t).val + qMinus at ht
      constructor
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2
  have hcover : ∀ K : Fin r ↪o ℤ,
      TwoSidedIntermediateBounds qPlus qMinus I J K →
        ∃ middle : Fin r ↪o Fin k, ∀ t, ambient (middle t) = K t := by
    intro K hK
    have hnonneg : ∀ t, 0 ≤ K t := by
      intro t
      have ht := hK t
      have hrowNonneg : (0 : ℤ) ≤ I t := by
        simp [I, finiteSelectionInteger]
      omega
    let middle : Fin r ↪o Fin k := OrderEmbedding.ofStrictMono
      (fun t ↦ ⟨(K t).toNat, by
        have ht := hK t
        have hcast := Int.toNat_of_nonneg (hnonneg t)
        have hbuffer := hrowBuffer t
        simp [I, finiteSelectionInteger] at ht
        omega⟩)
      (by
        intro x y hxy
        apply Fin.mk_lt_mk.mpr
        have hstrict := K.strictMono hxy
        have hx := Int.toNat_of_nonneg (hnonneg x)
        have hy := Int.toNat_of_nonneg (hnonneg y)
        omega)
    refine ⟨middle, ?_⟩
    intro t
    have hcast := Int.toNat_of_nonneg (hnonneg t)
    simp [ambient, finiteSelectionInteger, middle, hcast]
  have hsupport := orderedMinor_mul_pos_iff_twoSidedBounds
    hU hL rows cols I J ambient hUpos hLpos hcover
  change 0 < orderedMinor (U * L) rows cols ↔ _
  simpa [I, J, finiteSelectionInteger] using hsupport

/-- Every canonical finite Toeplitz section of the Laurent coefficient
function is totally nonnegative. -/
theorem twoSidedEdrei_toeplitzMatrix_totallyNonnegative
    {qPlus qMinus : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0) (m n : ℕ) :
    TotallyNonnegative
      (toeplitzMatrix m n (twoSidedEdreiCoefficient Dplus Dminus)) := by
  let k : ℕ := m + qPlus
  have hbuffer : ∀ i : Fin m, i.val + qPlus < k := by
    intro i
    have hi := i.isLt
    dsimp only [k]
    omega
  have hmatrix := twoSidedFiniteEdreiSection_eq_toeplitzMatrix
    (m := m) (k := k) (n := n) Dplus Dminus hgammaPlus hbuffer
  rw [← hmatrix]
  exact twoSidedFiniteEdreiSection_totallyNonnegative Dplus Dminus m k n

/-- Theorem 7.3, exact minor support for canonical finite sections. -/
theorem twoSidedEdrei_toeplitzMatrix_minor_pos_iff
    {qPlus qMinus r m n : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0)
    (hgammaMinus : Dminus.gamma = 0)
    (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n) :
    0 < orderedMinor
        (toeplitzMatrix m n (twoSidedEdreiCoefficient Dplus Dminus)) rows cols ↔
      ∀ t, -(qMinus : ℤ) ≤ ((cols t).val : ℤ) - ((rows t).val : ℤ) ∧
        ((cols t).val : ℤ) - ((rows t).val : ℤ) ≤ qPlus := by
  let k : ℕ := m + qPlus
  have hbuffer : ∀ i : Fin m, i.val + qPlus < k := by
    intro i
    have hi := i.isLt
    dsimp only [k]
    omega
  have hmatrix := twoSidedFiniteEdreiSection_eq_toeplitzMatrix
    (m := m) (k := k) (n := n) Dplus Dminus hgammaPlus hbuffer
  rw [← hmatrix]
  exact twoSidedFiniteEdreiSection_minor_pos_iff
    Dplus Dminus hgammaPlus hgammaMinus rows cols fun t ↦ hbuffer (rows t)

/-! ## Passage to arbitrary integer row and column sets -/

/-- Every finite minor of a bi-infinite Toeplitz matrix is literally a minor
of some finite natural-indexed Toeplitz section after a common translation of
all row and column labels. -/
theorem exists_finiteSection_eq_infiniteToeplitz_minor
    {r : ℕ} (a : ℤ → ℝ) (I J : Fin r ↪o ℤ) :
    ∃ (m n : ℕ) (rows : Fin r ↪o Fin m) (cols : Fin r ↪o Fin n),
      orderedMinor (fun i j : ℤ ↦ a (j - i)) I J =
        orderedMinor (toeplitzMatrix m n a) rows cols ∧
      ∀ t, ((cols t).val : ℤ) - ((rows t).val : ℤ) = J t - I t := by
  by_cases hr : r = 0
  · subst r
    let rows : Fin 0 ↪o Fin 0 := allRows 0
    let cols : Fin 0 ↪o Fin 0 := allRows 0
    refine ⟨0, 0, rows, cols, ?_, ?_⟩
    · simp [orderedMinor]
    · intro t
      exact Fin.elim0 t
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr
    let first : Fin r := ⟨0, hrPos⟩
    let last : Fin r := ⟨r - 1, by omega⟩
    let shift : ℤ := max (-(I first)) (-(J first))
    have hfirstLe : ∀ t : Fin r, first ≤ t := by
      intro t
      apply Fin.mk_le_mk.mpr
      change 0 ≤ t.val
      omega
    have hImin : ∀ t, I first ≤ I t := fun t ↦ I.monotone (hfirstLe t)
    have hJmin : ∀ t, J first ≤ J t := fun t ↦ J.monotone (hfirstLe t)
    have hInonneg : ∀ t, 0 ≤ I t + shift := by
      intro t
      have hs := le_max_left (-(I first)) (-(J first))
      dsimp only [shift]
      have ht := hImin t
      omega
    have hJnonneg : ∀ t, 0 ≤ J t + shift := by
      intro t
      have hs := le_max_right (-(I first)) (-(J first))
      dsimp only [shift]
      have ht := hJmin t
      omega
    let rowNat : Fin r → ℕ := fun t ↦ (I t + shift).toNat
    let colNat : Fin r → ℕ := fun t ↦ (J t + shift).toNat
    have hrowCast : ∀ t, ((rowNat t : ℕ) : ℤ) = I t + shift := fun t ↦
      Int.toNat_of_nonneg (hInonneg t)
    have hcolCast : ∀ t, ((colNat t : ℕ) : ℤ) = J t + shift := fun t ↦
      Int.toNat_of_nonneg (hJnonneg t)
    have hrowStrict : StrictMono rowNat := by
      intro x y hxy
      have h := I.strictMono hxy
      have hx := hrowCast x
      have hy := hrowCast y
      omega
    have hcolStrict : StrictMono colNat := by
      intro x y hxy
      have h := J.strictMono hxy
      have hx := hcolCast x
      have hy := hcolCast y
      omega
    let m : ℕ := rowNat last + 1
    let n : ℕ := colNat last + 1
    let rows : Fin r ↪o Fin m := OrderEmbedding.ofStrictMono
      (fun t ↦ ⟨rowNat t, by
        have htlast : t ≤ last := by
          apply Fin.mk_le_mk.mpr
          dsimp only [last]
          omega
        have ht := hrowStrict.monotone htlast
        dsimp only [m]
        omega⟩)
      (fun _ _ hxy ↦ Fin.mk_lt_mk.mpr (hrowStrict hxy))
    let cols : Fin r ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun t ↦ ⟨colNat t, by
        have htlast : t ≤ last := by
          apply Fin.mk_le_mk.mpr
          dsimp only [last]
          omega
        have ht := hcolStrict.monotone htlast
        dsimp only [n]
        omega⟩)
      (fun _ _ hxy ↦ Fin.mk_lt_mk.mpr (hcolStrict hxy))
    have hdifference : ∀ t,
        ((cols t).val : ℤ) - ((rows t).val : ℤ) = J t - I t := by
      intro t
      change (colNat t : ℤ) - (rowNat t : ℤ) = J t - I t
      rw [hrowCast, hcolCast]
      ring
    have hentryDifference : ∀ x y,
        ((cols y).val : ℤ) - ((rows x).val : ℤ) = J y - I x := by
      intro x y
      change (colNat y : ℤ) - (rowNat x : ℤ) = J y - I x
      rw [hrowCast, hcolCast]
      ring
    refine ⟨m, n, rows, cols, ?_, hdifference⟩
    unfold orderedMinor
    congr 1
    ext x y
    change a (J y - I x) = a (((cols y).val : ℤ) - ((rows x).val : ℤ))
    rw [hentryDifference]

/-- Theorem 7.3 in its original bi-infinite integer-indexed form. -/
theorem twoSidedEdrei_infiniteToeplitz_minor_pos_iff
    {qPlus qMinus r : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0)
    (hgammaMinus : Dminus.gamma = 0)
    (I J : Fin r ↪o ℤ) :
    0 < orderedMinor
        (fun i j : ℤ ↦ twoSidedEdreiCoefficient Dplus Dminus (j - i)) I J ↔
      ∀ t, -(qMinus : ℤ) ≤ J t - I t ∧ J t - I t ≤ qPlus := by
  obtain ⟨m, n, rows, cols, hminor, hdifference⟩ :=
    exists_finiteSection_eq_infiniteToeplitz_minor
      (twoSidedEdreiCoefficient Dplus Dminus) I J
  rw [hminor, twoSidedEdrei_toeplitzMatrix_minor_pos_iff
    Dplus Dminus hgammaPlus hgammaMinus rows cols]
  constructor
  · intro h t
    simpa [hdifference t] using h t
  · intro h t
    simpa [hdifference t] using h t

/-- Every finite minor of the bi-infinite matrix in Theorem 7.3 is
nonnegative. -/
theorem twoSidedEdrei_infiniteToeplitz_totallyNonnegative
    {qPlus qMinus : ℕ}
    (Dplus : FiniteEdreiData 0 qPlus)
    (Dminus : FiniteEdreiData 0 qMinus)
    (hgammaPlus : Dplus.gamma = 0) :
    TotallyNonnegative
      (fun i j : ℤ ↦ twoSidedEdreiCoefficient Dplus Dminus (j - i)) := by
  intro r I J
  obtain ⟨m, n, rows, cols, hminor, hdifference⟩ :=
    exists_finiteSection_eq_infiniteToeplitz_minor
      (twoSidedEdreiCoefficient Dplus Dminus) I J
  rw [hminor]
  exact (twoSidedEdrei_toeplitzMatrix_totallyNonnegative
    Dplus Dminus hgammaPlus m n).orderedMinor_nonneg rows cols
end

end FurtherToeplitzPositroids
