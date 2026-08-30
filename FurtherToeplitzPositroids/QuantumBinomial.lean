import FurtherToeplitzPositroids.Autocorrelation
import FurtherToeplitzPositroids.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import ToeplitzPositroids.Edrei.ToeplitzMinor
import ToeplitzPositroids.Edrei.GammaZeroSupport
import ToeplitzPositroids.Edrei.PositroidCorollary
import ToeplitzPositroids.RankThree.SineBase

/-!
# The quantum-binomial band point

This module defines the coefficient vector in equation (15), proves its
strict positivity and its two normalized endpoint values, and defines the
banded Toeplitz matrix from equation (16).
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids
open ToeplitzPositroids
open scoped BigOperators

noncomputable section

/-- The root-of-unity angle `pi / (d+r)`. -/
def quantumTheta (r d : ℕ) : ℝ :=
  Real.pi / (d + r : ℝ)

/-- The coefficient in equation (15). -/
def quantumBinomialCoefficient (r d t : ℕ) : ℝ :=
  ∏ l : Fin (r - 1),
    Real.sin ((t + l.val + 1 : ℕ) * quantumTheta r d) /
      Real.sin ((l.val + 1 : ℕ) * quantumTheta r d)

/-- Every sine factor occurring in a denominator is strictly positive. -/
theorem quantum_denominator_sin_pos
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (l : Fin (r - 1)) :
    0 < Real.sin ((l.val + 1 : ℕ) * quantumTheta r d) := by
  have hden : (0 : ℝ) < (d : ℝ) + r := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by positivity)
      (div_pos Real.pi_pos hden)
  · have hlN : l.val + 1 < d + r := by
      have hl := l.isLt
      omega
    rw [quantumTheta]
    calc
      ((l.val + 1 : ℕ) : ℝ) * (Real.pi / (d + r : ℝ)) =
          Real.pi * (((l.val + 1 : ℕ) : ℝ) / (d + r : ℝ)) := by ring
      _ < Real.pi * 1 := by
        apply mul_lt_mul_of_pos_left _ Real.pi_pos
        apply (div_lt_one hden).2
        exact_mod_cast hlN
      _ = Real.pi := by ring

/-- Every numerator factor is strictly positive throughout the band. -/
theorem quantum_numerator_sin_pos
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d)
    (l : Fin (r - 1)) :
    0 < Real.sin ((t + l.val + 1 : ℕ) * quantumTheta r d) := by
  have hden : (0 : ℝ) < (d : ℝ) + r := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by positivity)
      (div_pos Real.pi_pos hden)
  · have hnum : t + l.val + 1 < d + r := by
      have hl := l.isLt
      omega
    rw [quantumTheta]
    calc
      ((t + l.val + 1 : ℕ) : ℝ) * (Real.pi / (d + r : ℝ)) =
          Real.pi * (((t + l.val + 1 : ℕ) : ℝ) / (d + r : ℝ)) := by ring
      _ < Real.pi * 1 := by
        apply mul_lt_mul_of_pos_left _ Real.pi_pos
        apply (div_lt_one hden).2
        exact_mod_cast hnum
      _ = Real.pi := by ring

/-- The quantum-binomial coefficient is positive at every displayed band
index. -/
theorem quantumBinomialCoefficient_pos
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    0 < quantumBinomialCoefficient r d t := by
  apply Finset.prod_pos
  intro l _
  exact div_pos (quantum_numerator_sin_pos hr hd ht l)
    (quantum_denominator_sin_pos hr hd l)

/-- The left endpoint coefficient is one. -/
@[simp]
theorem quantumBinomialCoefficient_zero
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    quantumBinomialCoefficient r d 0 = 1 := by
  apply Finset.prod_eq_one
  intro l _
  simp only [Nat.zero_add]
  rw [div_self (quantum_denominator_sin_pos hr hd l).ne']

/-- The sine in the right-endpoint numerator is the denominator sine with
the finite index reversed. -/
theorem quantum_right_numerator_eq_reversed_denominator
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (l : Fin (r - 1)) :
    Real.sin ((d + l.val + 1 : ℕ) * quantumTheta r d) =
      Real.sin (((Fin.rev l).val + 1 : ℕ) * quantumTheta r d) := by
  have hsum : d + r = (d + l.val + 1) + ((Fin.rev l).val + 1) := by
    simp only [Fin.val_rev]
    have hl := l.isLt
    omega
  have hN : ((d : ℝ) + r) * quantumTheta r d = Real.pi := by
    rw [quantumTheta]
    field_simp
  have hsumR :
      (d : ℝ) + r =
        ((d + l.val + 1 : ℕ) : ℝ) +
          (((Fin.rev l).val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have harg :
      ((d + l.val + 1 : ℕ) : ℝ) * quantumTheta r d =
        Real.pi - (((Fin.rev l).val + 1 : ℕ) : ℝ) * quantumTheta r d := by
    rw [← hN]
    rw [hsumR]
    ring
  rw [harg, Real.sin_pi_sub]

/-- The right endpoint coefficient is one. -/
@[simp]
theorem quantumBinomialCoefficient_right
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    quantumBinomialCoefficient r d d = 1 := by
  unfold quantumBinomialCoefficient
  rw [Finset.prod_div_distrib]
  have hnum :
      (∏ l : Fin (r - 1),
        Real.sin (((d + l.val + 1 : ℕ) : ℝ) * quantumTheta r d)) =
      ∏ l : Fin (r - 1),
        Real.sin ((((Fin.rev l).val + 1 : ℕ) : ℝ) * quantumTheta r d) := by
    apply Finset.prod_congr rfl
    intro l _
    exact quantum_right_numerator_eq_reversed_denominator hr hd l
  rw [hnum]
  have hrev :
      (∏ l : Fin (r - 1),
        Real.sin ((((Fin.rev l).val + 1 : ℕ) : ℝ) * quantumTheta r d)) =
      ∏ l : Fin (r - 1),
        Real.sin (((l.val + 1 : ℕ) : ℝ) * quantumTheta r d) := by
    simpa using (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin (r - 1)))
      (fun l : Fin (r - 1) ↦
        Real.sin (((l.val + 1 : ℕ) : ℝ) * quantumTheta r d)))
  rw [hrev]
  exact div_self (Finset.prod_ne_zero_iff.mpr fun l _ ↦
    (quantum_denominator_sin_pos hr hd l).ne')

/-- The sine-product continuation vanishes at the `r-1` indices immediately
after the right endpoint.  This is the product-form content of equation (20). -/
theorem quantumBinomialCoefficient_zero_above_right
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hs : 1 ≤ s) (hsr : s < r) :
    quantumBinomialCoefficient r d (d + s) = 0 := by
  let l : Fin (r - 1) := ⟨r - s - 1, by omega⟩
  unfold quantumBinomialCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ l)
  have hindex : d + s + l.val + 1 = d + r := by
    dsimp only [l]
    omega
  have harg : ((d + r : ℕ) : ℝ) * quantumTheta r d = Real.pi := by
    rw [quantumTheta]
    have hne : ((d + r : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hindex, harg, Real.sin_pi, zero_div]

/-! ## Weyl sine-product positivity -/

/-- A sine at an integral index strictly between zero and `d+r` is positive
at the quantum angle. -/
theorem quantum_sin_pos_of_index
    {r d u : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hu : 0 < u) (huN : u < d + r) :
    0 < Real.sin ((u : ℝ) * quantumTheta r d) := by
  have hN : (0 : ℝ) < (d : ℝ) + r := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by exact_mod_cast hu) (div_pos Real.pi_pos hN)
  · rw [quantumTheta]
    calc
      (u : ℝ) * (Real.pi / ((d : ℝ) + r)) =
          Real.pi * ((u : ℝ) / ((d : ℝ) + r)) := by ring
      _ < Real.pi * 1 := by
        apply mul_lt_mul_of_pos_left _ Real.pi_pos
        apply (div_lt_one hN).2
        exact_mod_cast huN
      _ = Real.pi := by ring

/-- A weakly decreasing natural vector, the only partition property needed
for the Weyl specialization inequalities. -/
def IsPartitionVector {d : ℕ} (nu : Fin d → ℕ) : Prop :=
  ∀ a b : Fin d, a < b → nu b ≤ nu a

/-- The sine-product side of the Weyl specialization formula (24). -/
def weylSineProduct (r d : ℕ) (nu : Fin d → ℕ) : ℝ :=
  ∏ a : Fin d, ∏ b ∈ Finset.Ioi a,
    Real.sin (((nu a - nu b) + (b.val - a.val) : ℕ) * quantumTheta r d) /
      Real.sin (((b.val - a.val : ℕ)) * quantumTheta r d)

/-- Strict positivity in formula (24) when every partition part is at most
`r`. -/
theorem weylSineProduct_pos
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {nu : Fin d → ℕ} (hnu : IsPartitionVector nu)
    (hbound : ∀ a, nu a ≤ r) :
    0 < weylSineProduct r d nu := by
  unfold weylSineProduct
  apply Finset.prod_pos
  intro a ha
  apply Finset.prod_pos
  intro b hb
  have hab : a < b := Finset.mem_Ioi.mp hb
  have hnuba : nu b ≤ nu a := hnu a b hab
  have hgap : 0 < b.val - a.val := by omega
  have hnumPos : 0 < (nu a - nu b) + (b.val - a.val) := by omega
  have hnumBound : (nu a - nu b) + (b.val - a.val) < d + r := by
    have hbBound := b.isLt
    have hnuBound := hbound a
    omega
  have hdenBound : b.val - a.val < d + r := by
    have hbBound := b.isLt
    omega
  exact div_pos
    (quantum_sin_pos_of_index hr hd hnumPos hnumBound)
    (quantum_sin_pos_of_index hr hd hgap hdenBound)

/-- Nonnegativity at the next boundary `nu_a ≤ r+1`; a numerator sine
may now equal `sin pi = 0`, but cannot be negative. -/
theorem weylSineProduct_nonneg
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {nu : Fin d → ℕ} (hnu : IsPartitionVector nu)
    (hbound : ∀ a, nu a ≤ r + 1) :
    0 ≤ weylSineProduct r d nu := by
  unfold weylSineProduct
  apply Finset.prod_nonneg
  intro a ha
  apply Finset.prod_nonneg
  intro b hb
  have hab : a < b := Finset.mem_Ioi.mp hb
  have hnuba : nu b ≤ nu a := hnu a b hab
  have hgap : 0 < b.val - a.val := by omega
  have hnumPos : 0 < (nu a - nu b) + (b.val - a.val) := by omega
  have hnumBound : (nu a - nu b) + (b.val - a.val) ≤ d + r := by
    have hbBound := b.isLt
    have hnuBound := hbound a
    omega
  have hdenBound : b.val - a.val < d + r := by
    have hbBound := b.isLt
    omega
  apply div_nonneg
  · apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact (mul_pos (by exact_mod_cast hnumPos)
        (div_pos Real.pi_pos (by positivity))).le
    · rw [quantumTheta]
      have hN : (0 : ℝ) < (d : ℝ) + r := by positivity
      calc
        (((nu a - nu b) + (b.val - a.val) : ℕ) : ℝ) *
            (Real.pi / ((d : ℝ) + r)) =
          Real.pi * ((((nu a - nu b) + (b.val - a.val) : ℕ) : ℝ) /
            ((d : ℝ) + r)) := by ring
        _ ≤ Real.pi * 1 := by
          apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
          apply (div_le_one hN).2
          exact_mod_cast hnumBound
        _ = Real.pi := by ring
  · exact (quantum_sin_pos_of_index hr hd hgap hdenBound).le

/-- The band-supported bi-infinite coefficient function. -/
def quantumBandCoefficient (r d : ℕ) (z : ℤ) : ℝ :=
  if _hz : 0 ≤ z ∧ z ≤ d then
    quantumBinomialCoefficient r d z.toNat
  else 0

/-- The banded matrix in equation (16). -/
def quantumBandMatrix (r d : ℕ) :
    Matrix (Fin (r + 1)) (Fin (d + r + 1)) ℝ :=
  toeplitzMatrix (r + 1) (d + r + 1) (quantumBandCoefficient r d)

@[simp]
theorem quantumBandMatrix_apply (r d : ℕ)
    (i : Fin (r + 1)) (j : Fin (d + r + 1)) :
    quantumBandMatrix r d i j =
      quantumBandCoefficient r d ((j : ℤ) - (i : ℤ)) := by
  simp [quantumBandMatrix]

/-- Entries outside the coefficient band are structurally zero. -/
theorem quantumBandMatrix_eq_zero_of_outside
    {r d : ℕ} {i : Fin (r + 1)} {j : Fin (d + r + 1)}
    (houtside : (j : ℤ) - (i : ℤ) < 0 ∨ d < (j : ℤ) - (i : ℤ)) :
    quantumBandMatrix r d i j = 0 := by
  rw [quantumBandMatrix_apply, quantumBandCoefficient]
  split_ifs with h
  · rcases houtside with hneg | hlarge
    · omega
    · omega
  · rfl

/-- The structural feasibility condition from equation (21). -/
def BandFeasible {k r d : ℕ}
    (rows : Fin k ↪o Fin (r + 1))
    (cols : Fin k ↪o Fin (d + r + 1)) : Prop :=
  ∀ t, (rows t).val ≤ (cols t).val ∧ (cols t).val ≤ (rows t).val + d

/-- The row choice `i_t = max(t, j_t-d)` from the final paragraph of the
proof of Theorem 5.2. -/
def quantumFeasibleRows
    {k r d : ℕ} (hk : k ≤ r)
    (cols : Fin k ↪o Fin (d + r + 1)) : Fin k ↪o Fin (r + 1) :=
  OrderEmbedding.ofStrictMono
    (fun t ↦ ⟨max t.val ((cols t).val - d), by
      have ht := t.isLt
      have hj := (cols t).isLt
      omega⟩)
    (by
      intro x y hxy
      apply Fin.mk_lt_mk.mpr
      rw [max_lt_iff]
      have hcols := cols.strictMono hxy
      constructor
      · exact lt_of_lt_of_le (show x.val < y.val by exact hxy)
          (le_max_left _ _)
      · by_cases hy : (cols y).val ≤ d
        · have hyPos : 0 < y.val := by
            have hxyVal : x.val < y.val := hxy
            omega
          have hxZero : (cols x).val - d = 0 := by omega
          rw [hxZero]
          exact lt_of_lt_of_le hyPos (le_max_left _ _)
        · have hsub : (cols x).val - d < (cols y).val - d := by omega
          exact hsub.trans_le (le_max_right _ _))

/-- Every set of at most `r` columns admits a band-feasible row selection. -/
theorem quantumFeasibleRows_bandFeasible
    {k r d : ℕ} (hk : k ≤ r)
    (cols : Fin k ↪o Fin (d + r + 1)) :
    BandFeasible (quantumFeasibleRows hk cols) cols := by
  intro t
  have hlocalLower := orderEmbedding_fin_val_lower_bound cols t
  change max t.val ((cols t).val - d) ≤ (cols t).val ∧
    (cols t).val ≤ max t.val ((cols t).val - d) + d
  constructor
  · exact max_le hlocalLower (Nat.sub_le _ _)
  · by_cases hjd : (cols t).val ≤ d
    · exact le_trans hjd (Nat.le_add_left d _)
    · have hdj : d ≤ (cols t).val := by omega
      calc
        (cols t).val = ((cols t).val - d) + d := (Nat.sub_add_cancel hdj).symm
        _ ≤ max t.val ((cols t).val - d) + d :=
          Nat.add_le_add_right (le_max_right _ _) d

/-- The column-independence conclusion of Theorem 5.2 follows formally from
strict positivity on band-feasible lower-order minors. -/
theorem quantumBandMatrix_columns_independent_of_bandFeasible_minor_pos
    {k r d : ℕ} (hk : k ≤ r)
    (cols : Fin k ↪o Fin (d + r + 1))
    (hminorPos : ∀ rows : Fin k ↪o Fin (r + 1),
      BandFeasible rows cols →
        0 < orderedMinor (quantumBandMatrix r d) rows cols) :
    LinearIndependent ℝ
      (fun j : Fin k ↦ (quantumBandMatrix r d).col (cols j)) := by
  let rows : Fin k ↪o Fin (r + 1) := quantumFeasibleRows hk cols
  have hminor : orderedMinor (quantumBandMatrix r d) rows cols ≠ 0 :=
    (hminorPos rows (quantumFeasibleRows_bandFeasible hk cols)).ne'
  let C : Matrix (Fin k) (Fin (d + r + 1)) ℝ :=
    (quantumBandMatrix r d).submatrix rows id
  have hCminor : orderedMinor C (allRows k) cols ≠ 0 := by
    change ((quantumBandMatrix r d).submatrix rows cols).det ≠ 0
    simpa [C, allRows, Matrix.submatrix_submatrix] using hminor
  have hCind : LinearIndependent ℝ (fun j : Fin k ↦ C.col (cols j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns C cols).mp hCminor
  let restrictRows : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    LinearMap.pi fun i ↦ LinearMap.proj (rows i)
  apply LinearIndependent.of_comp restrictRows
  have hfamily :
      (restrictRows ∘ fun j : Fin k ↦ (quantumBandMatrix r d).col (cols j)) =
        fun j : Fin k ↦ C.col (cols j) := by
    funext j i
    rfl
  rw [hfamily]
  exact hCind

/-- A permutation must send some element of the suffix starting at `k` to
an element no larger than `k`. -/
theorem exists_le_perm_apply_of_le
    {q : ℕ} (sigma : Equiv.Perm (Fin q)) (k : Fin q) :
    ∃ c : Fin q, k ≤ c ∧ sigma c ≤ k := by
  obtain ⟨c, hck, hkinv⟩ :=
    exists_le_and_le_perm_apply sigma.symm k
  refine ⟨sigma.symm c, hkinv, ?_⟩
  simpa using hck

/-- If the band-feasibility inequalities fail, the selected determinant is
structurally zero.  This is the zero direction preceding Theorem 5.2(i). -/
theorem quantumBandMatrix_orderedMinor_eq_zero_of_not_bandFeasible
    {q r d : ℕ}
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (d + r + 1))
    (hnot : ¬BandFeasible rows cols) :
    orderedMinor (quantumBandMatrix r d) rows cols = 0 := by
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
        ((rows (sigma c) : Fin (r + 1)) : ℤ) < 0 := by
      omega
    have hentry :
        (quantumBandMatrix r d).submatrix rows cols (sigma c) c = 0 :=
      quantumBandMatrix_eq_zero_of_outside (Or.inl hneg)
    have hprod : ∏ i,
        (quantumBandMatrix r d).submatrix rows cols (sigma i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) hentry
    rw [hprod, smul_zero]
  · have hrowcol : (rows t).val ≤ (cols t).val := by omega
    have hupper : (rows t).val + d < (cols t).val := ht hrowcol
    obtain ⟨c, htc, hsigmat⟩ := exists_le_perm_apply_of_le sigma t
    have hcol : cols t ≤ cols c := cols.monotone htc
    have hrow : rows (sigma c) ≤ rows t := rows.monotone hsigmat
    have hlarge : d < ((cols c : Fin (d + r + 1)) : ℤ) -
        ((rows (sigma c) : Fin (r + 1)) : ℤ) := by
      omega
    have hentry :
        (quantumBandMatrix r d).submatrix rows cols (sigma c) c = 0 :=
      quantumBandMatrix_eq_zero_of_outside (Or.inr hlarge)
    have hprod : ∏ i,
        (quantumBandMatrix r d).submatrix rows cols (sigma i) i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) hentry
    rw [hprod, smul_zero]

/-- Entry positivity is exactly the structural band condition. -/
theorem quantumBandMatrix_entry_pos_iff
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (i : Fin (r + 1)) (j : Fin (d + r + 1)) :
    0 < quantumBandMatrix r d i j ↔
      i.val ≤ j.val ∧ j.val ≤ i.val + d := by
  rw [quantumBandMatrix_apply, quantumBandCoefficient]
  by_cases hz : 0 ≤ (j : ℤ) - (i : ℤ) ∧
      (j : ℤ) - (i : ℤ) ≤ d
  · rw [dif_pos hz]
    constructor
    · intro _
      omega
    · intro _
      apply quantumBinomialCoefficient_pos hr hd
      have htoNat := Int.toNat_of_nonneg hz.1
      omega
  · rw [dif_neg hz]
    constructor
    · norm_num
    · intro hband
      exfalso
      apply hz
      omega

@[simp]
theorem quantumBandCoefficient_zero
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    quantumBandCoefficient r d 0 = 1 := by
  rw [quantumBandCoefficient, dif_pos]
  · simpa using quantumBinomialCoefficient_zero hr hd
  · omega

@[simp]
theorem quantumBandCoefficient_right
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    quantumBandCoefficient r d d = 1 := by
  rw [quantumBandCoefficient, dif_pos]
  · simpa using quantumBinomialCoefficient_right hr hd
  · omega

/-- The first `r+1` columns form an upper triangular block with diagonal
one.  Hence the quantum band matrix has full row rank in every rank covered
by Theorem 5.2. -/
theorem quantumBandMatrix_fullRowRank
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    HasFullRowRank (quantumBandMatrix r d) := by
  let cols : Fin (r + 1) ↪o Fin (d + r + 1) :=
    Fin.castLEOrderEmb (by omega)
  refine ⟨cols, ?_⟩
  rw [orderedMinor]
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    (quantumBandMatrix r d).submatrix (allRows (r + 1)) cols
  change B.det ≠ 0
  have htri : B.BlockTriangular id := by
    intro i j hji
    have hneg : ((cols j : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ) < 0 := by
      change (j : ℤ) - (i : ℤ) < 0
      have hji' : j.val < i.val := by simpa using hji
      omega
    change quantumBandMatrix r d (allRows (r + 1) i) (cols j) = 0
    exact quantumBandMatrix_eq_zero_of_outside (Or.inl hneg)
  rw [Matrix.det_of_upperTriangular htri]
  have hdiag : ∀ i : Fin (r + 1), B i i = 1 := by
    intro i
    change quantumBandCoefficient r d
      (((cols i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = 1
    have hindex : (((cols i : Fin (d + r + 1)) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ)) = 0 := by
      change (i : ℤ) - (i : ℤ) = 0
      ring
    rw [hindex, quantumBandCoefficient_zero hr hd]
  simp_rw [hdiag]
  simp

/-! ## The width-one band in arbitrary rank -/

/-- The one-letter pure numerator Edrei datum with parameter one. -/
def unitBetaEdreiData : FiniteEdreiData 0 1 where
  alpha := Fin.elim0
  beta := fun _ ↦ 1
  gamma := 0
  alpha_pos := fun i ↦ Fin.elim0 i
  beta_pos := fun _ ↦ by norm_num
  gamma_nonneg := by norm_num

@[simp]
theorem unitBetaEdreiData_gamma : unitBetaEdreiData.gamma = 0 := rfl

/-- The natural coefficients of the one-letter datum are exactly the
elementary beta sequence. -/
theorem unitBetaEdreiData_natCoefficient (s : ℕ) :
    unitBetaEdreiData.natCoefficient s = betaNaturalCoefficient 1 s := by
  rw [Edrei.FiniteEdreiData.natCoefficient_eq_finiteFactorCoefficient
    unitBetaEdreiData rfl]
  simp only [FiniteEdreiData.betaProduct, Fin.prod_univ_one,
    unitBetaEdreiData, FiniteEdreiData.alphaProduct,
    Fin.prod_univ_zero, mul_one]
  exact coeff_betaFactor_eq_betaNaturalCoefficient 1 s

/-- The full integer-indexed coefficient functions also agree. -/
theorem unitBetaEdreiData_coefficient (z : ℤ) :
    unitBetaEdreiData.coefficient z =
      zeroExtendedNaturalSequence (betaNaturalCoefficient 1) z := by
  rw [FiniteEdreiData.coefficient, zeroExtendedNaturalSequence]
  split_ifs with hz
  · rw [unitBetaEdreiData_natCoefficient]
  · rfl

/-- For `d=1`, the quantum coefficient function is the elementary
upper-bidiagonal beta sequence with parameter one. -/
theorem quantumBandCoefficient_oneWidth_eq_beta
    {r : ℕ} (hr : 0 < r) (z : ℤ) :
    quantumBandCoefficient r 1 z =
      zeroExtendedNaturalSequence (betaNaturalCoefficient 1) z := by
  by_cases hz : 0 ≤ z ∧ z ≤ (1 : ℤ)
  · have hzCases : z = 0 ∨ z = 1 := by omega
    rcases hzCases with rfl | rfl
    · rw [quantumBandCoefficient_zero hr (by omega)]
      simp [zeroExtendedNaturalSequence, betaNaturalCoefficient]
    · have hright := quantumBandCoefficient_right hr (by omega : 0 < (1 : ℕ))
      norm_num at hright ⊢
      rw [hright]
      simp [zeroExtendedNaturalSequence, betaNaturalCoefficient]
  · unfold quantumBandCoefficient
    split_ifs with hband
    · exact (hz hband).elim
    · by_cases hneg : z < 0
      · rw [zeroExtendedNaturalSequence_eq_zero_of_neg _ hneg]
      · have hlarge : 1 < z := by omega
        have htoNat : ((z.toNat : ℕ) : ℤ) = z :=
          Int.toNat_of_nonneg (by omega)
        have htoNatLarge : 1 < z.toNat := by omega
        rw [← htoNat, zeroExtendedNaturalSequence_ofNat]
        simp [betaNaturalCoefficient, htoNatLarge.ne']
        omega

/-- The width-one quantum band matrix is a rectangular submatrix of the
checked elementary beta-factor Toeplitz matrix. -/
theorem quantumBandMatrix_oneWidth_totallyNonnegative
    {r : ℕ} (hr : 0 < r) :
    TotallyNonnegative (quantumBandMatrix r 1) := by
  let B : Matrix (Fin (1 + r + 1)) (Fin (1 + r + 1)) ℝ :=
    fun i j ↦ zeroExtendedNaturalSequence (betaNaturalCoefficient 1)
      ((j : ℤ) - (i : ℤ))
  let rowMap : Fin (r + 1) ↪o Fin (1 + r + 1) := Fin.castLEOrderEmb (by omega)
  have hB : TotallyNonnegative B := by
    exact betaToeplitz_totallyNonnegative (b := (1 : ℝ)) (by norm_num) (1 + r)
  have hsub : B.submatrix rowMap (allRows (1 + r + 1)) = quantumBandMatrix r 1 := by
    ext i j
    change zeroExtendedNaturalSequence (betaNaturalCoefficient 1)
      ((j : ℤ) - (i : ℤ)) = quantumBandCoefficient r 1 ((j : ℤ) - (i : ℤ))
    exact (quantumBandCoefficient_oneWidth_eq_beta hr _).symm
  rw [← hsub]
  exact hB.submatrix rowMap (allRows (1 + r + 1))

/-- The width-one quantum matrix is exactly the finite Toeplitz section of
the one-letter Edrei datum. -/
theorem quantumBandMatrix_oneWidth_eq_unitBetaSection
    {r : ℕ} (hr : 0 < r) :
    quantumBandMatrix r 1 =
      unitBetaEdreiData.finiteToeplitzSection (r + 1) (1 + r + 1) := by
  ext i j
  rw [quantumBandMatrix_apply, FiniteEdreiData.finiteToeplitzSection_apply,
    quantumBandCoefficient_oneWidth_eq_beta hr,
    unitBetaEdreiData_coefficient]

/-- For `d=1`, Theorem 5.2(i) holds in every rank. -/
theorem quantumBandMatrix_oneWidth_minor_pos_iff_bandFeasible
    {q r : ℕ} (hr : 0 < r)
    (rows : Fin q ↪o Fin (r + 1))
    (cols : Fin q ↪o Fin (1 + r + 1)) :
    0 < orderedMinor (quantumBandMatrix r 1) rows cols ↔
      BandFeasible rows cols := by
  rw [quantumBandMatrix_oneWidth_eq_unitBetaSection hr,
    unitBetaEdreiData.orderedMinor_finiteToeplitzSection_eq_toeplitzMinor,
    Edrei.FiniteEdreiData.toeplitzMinor_pos_iff_minorSupportCondition_of_explicit_gamma_zero
      unitBetaEdreiData rfl]
  unfold FiniteEdreiData.MinorSupportCondition
  unfold Edrei.IndexHookInequalities BandFeasible
  simp only [unitBetaEdreiData_gamma, forall_const,
    finiteSelectionNatural_apply, Edrei.naturalIndexTuple, Nat.sub_zero]
  constructor
  · rintro ⟨hlower, hupper⟩ t
    refine ⟨hlower t, ?_⟩
    have hu := hupper t (by omega)
    change (cols t).val + 1 + 0 ≤ (rows t).val + 1 + 1 at hu
    omega
  · intro hband
    refine ⟨fun t ↦ (hband t).1, ?_⟩
    intro t ht
    have hu := (hband t).2
    change (cols t).val + 1 + 0 ≤ (rows t).val + 1 + 1
    omega

/-! ## The complete three-row quantum specialization -/

/-- Multiplication by a nonnegative scalar preserves total nonnegativity. -/
theorem totallyNonnegative_smul_of_nonneg
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hA : TotallyNonnegative A) :
    TotallyNonnegative (c • A) := by
  intro k rows cols
  rw [orderedMinor]
  change (c • A.submatrix rows cols).det ≥ 0
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  exact mul_nonneg (pow_nonneg hc k) (hA.orderedMinor_nonneg rows cols)

/-- For `r=2`, the quantum coefficient function is the normalized sine
coefficient function used in Paper A's checked rank-three base point. -/
theorem quantumBandCoefficient_two_eq_normalizedSine
    {d : ℕ} (z : ℤ) :
    quantumBandCoefficient 2 d z =
      (Real.sin (RankThree.sineAngle d))⁻¹ *
        RankThree.bandCoefficient (RankThree.sineCoefficient d) z := by
  have htheta : quantumTheta 2 d = RankThree.sineAngle d := by
    simp only [quantumTheta, RankThree.sineAngle]
    congr 2
  by_cases hz : 0 ≤ z ∧ z ≤ d
  · rw [quantumBandCoefficient, dif_pos hz,
      RankThree.bandCoefficient, dif_pos hz]
    unfold quantumBinomialCoefficient
    rw [Fin.prod_univ_one]
    simp only [Fin.val_zero, Nat.add_zero]
    rw [htheta]
    have htoNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz.1
    have hindex : z.toNat + 0 + 1 = z.toNat + 1 := by omega
    rw [hindex]
    simp only [RankThree.sineCoefficient]
    rw [inv_mul_eq_div]
    congr 2 <;> push_cast <;> ring
  · rw [quantumBandCoefficient, dif_neg hz,
      RankThree.bandCoefficient, dif_neg hz, mul_zero]

/-- The three-row quantum band matrix is a positive scalar multiple of the
rank-three sine band matrix. -/
theorem quantumBandMatrix_two_eq_smul_sine (d : ℕ) :
    quantumBandMatrix 2 d =
      (Real.sin (RankThree.sineAngle d))⁻¹ •
        RankThree.bandedMatrix (RankThree.sineCoefficient d) := by
  ext i j
  rw [quantumBandMatrix_apply]
  change quantumBandCoefficient 2 d ((j : ℤ) - (i : ℤ)) =
    (Real.sin (RankThree.sineAngle d))⁻¹ *
      RankThree.bandCoefficient (RankThree.sineCoefficient d)
        ((j : ℤ) - (i : ℤ))
  exact quantumBandCoefficient_two_eq_normalizedSine _

/-- Theorem 5.2(ii) for `m=3` and `d≥2`, inherited from the checked
rank-three sine base point. -/
theorem quantumBandMatrix_two_totallyNonnegative
    {d : ℕ} (hd : 2 ≤ d) :
    TotallyNonnegative (quantumBandMatrix 2 d) := by
  rw [quantumBandMatrix_two_eq_smul_sine d]
  apply totallyNonnegative_smul_of_nonneg
  · exact (inv_pos.mpr (Real.sin_pos_of_pos_of_lt_pi
      (RankThree.sineAngle_pos d) (RankThree.sineAngle_lt_pi d))).le
  · exact RankThree.sineBandedMatrix_totallyNonnegative hd

/-- Theorem 5.2(i) for `m=3`: every minor of order two is positive exactly
when its ordered row/column pair is band-feasible. -/
theorem quantumBandMatrix_two_minor_pos_iff_bandFeasible
    {d : ℕ} (hd : 2 ≤ d)
    (rows : Fin 2 ↪o Fin 3) (cols : Fin 2 ↪o Fin (d + 3)) :
    0 < orderedMinor (quantumBandMatrix 2 d) rows cols ↔
      BandFeasible rows cols := by
  have hTN := quantumBandMatrix_two_totallyNonnegative hd
  have hmatrix := quantumBandMatrix_two_eq_smul_sine d
  let c : ℝ := (Real.sin (RankThree.sineAngle d))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sin_pos_of_pos_of_lt_pi
    (RankThree.sineAngle_pos d) (RankThree.sineAngle_lt_pi d))
  constructor
  · intro hminor
    by_contra hfeasible
    have hzero := quantumBandMatrix_orderedMinor_eq_zero_of_not_bandFeasible
      rows cols hfeasible
    exact hminor.ne' hzero
  · intro hfeasible
    have hrow : rows 0 < rows 1 := rows.strictMono (by decide)
    have hcol : cols 0 < cols 1 := cols.strictMono (by decide)
    have h₀₀ : 0 < quantumBandMatrix 2 d (rows 0) (cols 0) :=
      (quantumBandMatrix_entry_pos_iff (by omega) (by omega) _ _).2
        (hfeasible 0)
    have h₁₁ : 0 < quantumBandMatrix 2 d (rows 1) (cols 1) :=
      (quantumBandMatrix_entry_pos_iff (by omega) (by omega) _ _).2
        (hfeasible 1)
    have h₀₁nonneg := hTN.entry_nonneg (rows 0) (cols 1)
    have h₁₀nonneg := hTN.entry_nonneg (rows 1) (cols 0)
    by_cases hcross : 0 <
        quantumBandMatrix 2 d (rows 0) (cols 1) *
          quantumBandMatrix 2 d (rows 1) (cols 0)
    · have h₀₁ : 0 < quantumBandMatrix 2 d (rows 0) (cols 1) := by
        rcases mul_pos_iff.mp hcross with hpos | hneg
        · exact hpos.1
        · exact (not_lt_of_ge h₀₁nonneg hneg.1).elim
      have h₁₀ : 0 < quantumBandMatrix 2 d (rows 1) (cols 0) := by
        rcases mul_pos_iff.mp hcross with hpos | hneg
        · exact hpos.2
        · exact (not_lt_of_ge h₁₀nonneg hneg.2).elim
      have sineEntryPos {i : Fin 3} {j : Fin (d + 3)}
          (hpos : 0 < quantumBandMatrix 2 d i j) :
          0 < RankThree.bandedMatrix (RankThree.sineCoefficient d) i j := by
        have heq := congrFun (congrFun hmatrix i) j
        change quantumBandMatrix 2 d i j =
          c * RankThree.bandedMatrix (RankThree.sineCoefficient d) i j at heq
        rw [heq] at hpos
        exact pos_of_mul_pos_right hpos hc.le
      have hs₀₀ := sineEntryPos h₀₀
      have hs₀₁ := sineEntryPos h₀₁
      have hs₁₀ := sineEntryPos h₁₀
      have hs₁₁ := sineEntryPos h₁₁
      let avec := RankThree.bandCoefficientVector (RankThree.sineCoefficient d)
      have hs₀₀' : 0 < avec (finiteToeplitzIndex (rows 0) (cols 0)) := by
        change 0 < rankThreeToeplitz avec (rows 0) (cols 0)
        rw [← RankThree.bandedMatrix_eq_rankThreeToeplitz]
        exact hs₀₀
      have hs₀₁' : 0 < avec (finiteToeplitzIndex (rows 0) (cols 1)) := by
        change 0 < rankThreeToeplitz avec (rows 0) (cols 1)
        rw [← RankThree.bandedMatrix_eq_rankThreeToeplitz]
        exact hs₀₁
      have hs₁₀' : 0 < avec (finiteToeplitzIndex (rows 1) (cols 0)) := by
        change 0 < rankThreeToeplitz avec (rows 1) (cols 0)
        rw [← RankThree.bandedMatrix_eq_rankThreeToeplitz]
        exact hs₁₀
      have hs₁₁' : 0 < avec (finiteToeplitzIndex (rows 1) (cols 1)) := by
        change 0 < rankThreeToeplitz avec (rows 1) (cols 1)
        rw [← RankThree.bandedMatrix_eq_rankThreeToeplitz]
        exact hs₁₁
      have hnonstructural : IsNonstructuralTwoMinor
          (RankThree.bandCoefficientVector (RankThree.sineCoefficient d))
          (rows 0) (rows 1) (cols 0) (cols 1) := by
        exact ⟨hs₀₀', hs₀₁', hs₁₀', hs₁₁'⟩
      have hsine := RankThree.sineBandedMatrix_nonstructural_twoMinor_pos
        hd (rows 0) (rows 1) hrow (cols 0) (cols 1) hcol hnonstructural
      rw [hmatrix, orderedMinor]
      change 0 < (c •
        (RankThree.bandedMatrix (RankThree.sineCoefficient d)).submatrix rows cols).det
      rw [Matrix.det_smul]
      simp only [Fintype.card_fin]
      exact mul_pos (pow_pos hc 2) hsine
    · have hcrossZero :
          quantumBandMatrix 2 d (rows 0) (cols 1) *
            quantumBandMatrix 2 d (rows 1) (cols 0) = 0 :=
        le_antisymm (le_of_not_gt hcross)
          (mul_nonneg h₀₁nonneg h₁₀nonneg)
      rw [orderedMinor_two, hcrossZero, sub_zero]
      exact mul_pos h₀₀ h₁₁

/-- Every ordered pair of columns in the three-row band admits a
band-feasible ordered pair of rows. -/
theorem exists_bandFeasible_rows_two
    {d : ℕ} (hd : 2 ≤ d) (cols : Fin 2 ↪o Fin (d + 3)) :
    ∃ rows : Fin 2 ↪o Fin 3, BandFeasible rows cols := by
  have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
  by_cases hright : (cols 1).val ≤ d + 1
  · let rows : Fin 2 ↪o Fin 3 :=
      twoPointOrderEmbedding 0 1 (by decide)
    refine ⟨rows, ?_⟩
    intro t
    fin_cases t
    · change 0 ≤ (cols 0).val ∧ (cols 0).val ≤ 0 + d
      omega
    · change 1 ≤ (cols 1).val ∧ (cols 1).val ≤ 1 + d
      omega
  · have hlast : (cols 1).val = d + 2 := by
      have hbound := (cols 1).isLt
      omega
    by_cases hzero : (cols 0).val = 0
    · let rows : Fin 2 ↪o Fin 3 :=
        twoPointOrderEmbedding 0 2 (by decide)
      refine ⟨rows, ?_⟩
      intro t
      fin_cases t
      · change 0 ≤ (cols 0).val ∧ (cols 0).val ≤ 0 + d
        omega
      · change 2 ≤ (cols 1).val ∧ (cols 1).val ≤ 2 + d
        omega
    · let rows : Fin 2 ↪o Fin 3 :=
        twoPointOrderEmbedding 1 2 (by decide)
      refine ⟨rows, ?_⟩
      intro t
      fin_cases t
      · change 1 ≤ (cols 0).val ∧ (cols 0).val ≤ 1 + d
        omega
      · change 2 ≤ (cols 1).val ∧ (cols 1).val ≤ 2 + d
        omega

/-- Theorem 5.2(iii) for `m=3`: every pair of columns is independent. -/
theorem quantumBandMatrix_two_pair_independent
    {d : ℕ} (hd : 2 ≤ d) (cols : Fin 2 ↪o Fin (d + 3)) :
    LinearIndependent ℝ
      (fun j : Fin 2 ↦ (quantumBandMatrix 2 d).col (cols j)) := by
  obtain ⟨rows, hfeasible⟩ := exists_bandFeasible_rows_two hd cols
  have hminor : orderedMinor (quantumBandMatrix 2 d) rows cols ≠ 0 :=
    (quantumBandMatrix_two_minor_pos_iff_bandFeasible hd rows cols).2 hfeasible |>.ne'
  let C : Matrix (Fin 2) (Fin (d + 3)) ℝ :=
    (quantumBandMatrix 2 d).submatrix rows id
  have hCminor : orderedMinor C (allRows 2) cols ≠ 0 := by
    change ((quantumBandMatrix 2 d).submatrix rows cols).det ≠ 0
    simpa [C, allRows, Matrix.submatrix_submatrix] using hminor
  have hCind : LinearIndependent ℝ (fun j : Fin 2 ↦ C.col (cols j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns C cols).mp hCminor
  let restrictRows : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi fun i ↦ LinearMap.proj (rows i)
  apply LinearIndependent.of_comp restrictRows
  have hfamily :
      (restrictRows ∘ fun j : Fin 2 ↦ (quantumBandMatrix 2 d).col (cols j)) =
        fun j : Fin 2 ↦ C.col (cols j) := by
    funext j i
    rfl
  rw [hfamily]
  exact hCind

/-! ## Complete rank-two specialization -/

@[simp]
theorem quantumBinomialCoefficient_one (d t : ℕ) :
    quantumBinomialCoefficient 1 d t = 1 := by
  simp [quantumBinomialCoefficient]

theorem quantumBandCoefficient_one (d : ℕ) (z : ℤ) :
    quantumBandCoefficient 1 d z = if 0 ≤ z ∧ z ≤ d then 1 else 0 := by
  unfold quantumBandCoefficient
  split_ifs <;> simp

theorem quantumBandMatrix_one_apply (d : ℕ)
    (row : Fin 2) (col : Fin (d + 2)) :
    quantumBandMatrix 1 d row col =
      if row.val ≤ col.val ∧ col.val ≤ row.val + d then 1 else 0 := by
  rw [quantumBandMatrix_apply, quantumBandCoefficient_one]
  by_cases hz : 0 ≤ (col : ℤ) - (row : ℤ) ∧
      (col : ℤ) - (row : ℤ) ≤ d
  · rw [if_pos hz, if_pos]
    omega
  · rw [if_neg hz, if_neg]
    omega

/-- Theorem 5.2 for `m=2`: the full band matrix is totally nonnegative. -/
theorem quantumBandMatrix_one_totallyNonnegative (d : ℕ) :
    TotallyNonnegative (quantumBandMatrix 1 d) := by
  intro q rows cols
  have hq : q ≤ 2 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  interval_cases q
  · simp
  · rw [orderedMinor_one, quantumBandMatrix_apply,
      quantumBandCoefficient_one]
    split_ifs <;> norm_num
  · rw [orderEmbedding_fin_self_eq_allRows rows, orderedMinor_two]
    simp only [allRows_apply_eq_self, quantumBandMatrix_one_apply]
    have hcols := cols.strictMono (show (0 : Fin 2) < 1 by decide)
    have h00 : (0 : Fin 2).val ≤ (cols 0).val ∧
        (cols 0).val ≤ (0 : Fin 2).val + d := by omega
    have h11 : (1 : Fin 2).val ≤ (cols 1).val ∧
        (cols 1).val ≤ (1 : Fin 2).val + d := by
      have hlast := (cols 1).isLt
      omega
    rw [if_pos h00, if_pos h11]
    split_ifs <;> norm_num

/-- Theorem 5.2(i) for `m=2`: entry positivity is exactly band
feasibility. -/
theorem quantumBandMatrix_one_entry_pos_iff
    (d : ℕ) (row : Fin 2) (col : Fin (d + 2)) :
    0 < quantumBandMatrix 1 d row col ↔
      row.val ≤ col.val ∧ col.val ≤ row.val + d := by
  rw [quantumBandMatrix_one_apply]
  split_ifs with h
  · constructor
    · intro _
      omega
    · intro _
      norm_num
  · constructor
    · norm_num
    · intro hband
      exfalso
      apply h
      omega

/-- The rank-two quantum band matrix has full row rank. -/
theorem quantumBandMatrix_one_fullRowRank (d : ℕ) :
    HasFullRowRank (quantumBandMatrix 1 d) := by
  let cols : Fin 2 ↪o Fin (d + 2) := Fin.castLEOrderEmb (by omega)
  refine ⟨cols, ?_⟩
  rw [orderedMinor_two]
  norm_num [cols, allRows, quantumBandMatrix_apply,
    quantumBandCoefficient_one]

/-! ## The first higher-rank example -/

/-- At `m=4`, `d=3`, the first interior coefficient is `2`. -/
theorem quantumBinomialCoefficient_three_three_one :
    quantumBinomialCoefficient 3 3 1 = 2 := by
  rw [quantumBinomialCoefficient, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, quantumTheta]
  norm_num
  have h₂ : (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 := by ring
  have h₃ : (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 := by ring
  rw [h₂, h₃, Real.sin_pi_div_three,
    Real.sin_pi_div_two]
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- At `m=4`, `d=3`, the second interior coefficient is `2`. -/
theorem quantumBinomialCoefficient_three_three_two :
    quantumBinomialCoefficient 3 3 2 = 2 := by
  rw [quantumBinomialCoefficient, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, quantumTheta]
  norm_num
  have h₂ : (2 : ℝ) * (Real.pi / 6) = Real.pi / 3 := by ring
  have h₃ : (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 := by ring
  have h₄ : (4 : ℝ) * (Real.pi / 6) =
      Real.pi - Real.pi / 3 := by ring
  rw [h₂, h₃, h₄, Real.sin_pi_sub,
    Real.sin_pi_div_three, Real.sin_pi_div_two]
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- The coefficient vector in Example 5.5. -/
theorem quantumBinomialCoefficient_three_three :
    (fun t : Fin 4 ↦ quantumBinomialCoefficient 3 3 t.val) = ![1, 2, 2, 1] := by
  funext t
  fin_cases t
  · exact quantumBinomialCoefficient_zero (by omega) (by omega)
  · exact quantumBinomialCoefficient_three_three_one
  · exact quantumBinomialCoefficient_three_three_two
  · exact quantumBinomialCoefficient_right (by omega) (by omega)

/-- The displayed band matrix in Example 5.5. -/
theorem quantumBandMatrix_three_three :
    quantumBandMatrix 3 3 =
      !![1, 2, 2, 1, 0, 0, 0;
         0, 1, 2, 2, 1, 0, 0;
         0, 0, 1, 2, 2, 1, 0;
         0, 0, 0, 1, 2, 2, 1] := by
  have hto2 : (2 : ℤ).toNat = 2 := by
    exact_mod_cast Int.toNat_of_nonneg (a := (2 : ℤ)) (by omega)
  have hto3 : (3 : ℤ).toNat = 3 := by
    exact_mod_cast Int.toNat_of_nonneg (a := (3 : ℤ)) (by omega)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quantumBandMatrix, toeplitzMatrix, quantumBandCoefficient,
      quantumBinomialCoefficient_three_three_one,
      quantumBinomialCoefficient_three_three_two,
      quantumBinomialCoefficient_zero, quantumBinomialCoefficient_right,
      hto2, hto3]

/-- The four consecutive square blocks in Example 5.5. -/
def firstHigherRankBlock : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![!![1, 2, 2, 1; 0, 1, 2, 2; 0, 0, 1, 2; 0, 0, 0, 1],
    !![2, 2, 1, 0; 1, 2, 2, 1; 0, 1, 2, 2; 0, 0, 1, 2],
    !![2, 1, 0, 0; 2, 2, 1, 0; 1, 2, 2, 1; 0, 1, 2, 2],
    !![1, 0, 0, 0; 2, 1, 0, 0; 2, 2, 1, 0; 1, 2, 2, 1]]

/-- The recurrence vector from Example 5.5. -/
def firstHigherRankRecurrence : Fin 4 → ℝ :=
  ![-1, 2, -2, 1]

theorem firstHigherRankBlock_eq_submatrix (t : Fin 4) :
    (!![1, 2, 2, 1, 0, 0, 0;
        0, 1, 2, 2, 1, 0, 0;
        0, 0, 1, 2, 2, 1, 0;
        0, 0, 0, 1, 2, 2, 1] : Matrix (Fin 4) (Fin 7) ℝ).submatrix
      (allRows 4) (consecutiveColumns (by omega : 3 < 7) t) =
        firstHigherRankBlock t := by
  ext i j
  fin_cases t <;> fin_cases i <;> fin_cases j <;>
    norm_num [firstHigherRankBlock, allRows, consecutiveColumns]

theorem firstHigherRankBlock_det (t : Fin 4) :
    (firstHigherRankBlock t).det = ![1, 0, 0, 1] t := by
  fin_cases t
  · change Matrix.det !![1, 2, 2, 1; 0, 1, 2, 2;
      0, 0, 1, 2; 0, 0, 0, 1] = 1
    have htri :
        (!![1, 2, 2, 1; 0, 1, 2, 2; 0, 0, 1, 2;
          0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℝ).BlockTriangular id := by
      intro i j hji
      fin_cases i <;> fin_cases j
      all_goals simp_all
    rw [Matrix.det_of_upperTriangular htri]
    norm_num [Fin.prod_univ_succ]
  · change Matrix.det !![2, 2, 1, 0; 1, 2, 2, 1;
      0, 1, 2, 2; 0, 0, 1, 2] = 0
    apply (Matrix.exists_mulVec_eq_zero_iff).1
    refine ⟨firstHigherRankRecurrence, ?_, ?_⟩
    · norm_num [firstHigherRankRecurrence]
    · funext i
      fin_cases i <;>
        norm_num [firstHigherRankRecurrence,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · change Matrix.det !![2, 1, 0, 0; 2, 2, 1, 0;
      1, 2, 2, 1; 0, 1, 2, 2] = 0
    apply (Matrix.exists_mulVec_eq_zero_iff).1
    refine ⟨firstHigherRankRecurrence, ?_, ?_⟩
    · norm_num [firstHigherRankRecurrence]
    · funext i
      fin_cases i <;>
        norm_num [firstHigherRankRecurrence,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · change Matrix.det !![1, 0, 0, 0; 2, 1, 0, 0;
      2, 2, 1, 0; 1, 2, 2, 1] = 1
    have htranspose :
        (!![1, 0, 0, 0; 2, 1, 0, 0; 2, 2, 1, 0;
          1, 2, 2, 1] : Matrix (Fin 4) (Fin 4) ℝ) =
        Matrix.transpose
          (!![1, 2, 2, 1; 0, 1, 2, 2; 0, 0, 1, 2;
            0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [htranspose, Matrix.det_transpose]
    have htri :
        (!![1, 2, 2, 1; 0, 1, 2, 2; 0, 0, 1, 2;
          0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℝ).BlockTriangular id := by
      intro i j hji
      fin_cases i <;> fin_cases j
      all_goals simp_all
    rw [Matrix.det_of_upperTriangular htri]
    norm_num [Fin.prod_univ_succ]

/-- The consecutive maximal minors in Example 5.5 are `(1,0,0,1)`. -/
theorem quantumBandMatrix_three_three_consecutiveMinors :
    (fun t : Fin 4 ↦ matrixConsecutiveMinor (by omega : 3 < 7)
      (quantumBandMatrix 3 3) t) = ![1, 0, 0, 1] := by
  funext t
  unfold matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  rw [quantumBandMatrix_three_three,
    firstHigherRankBlock_eq_submatrix, firstHigherRankBlock_det]

/-- The explicit autocorrelation Jacobian in Example 5.5. -/
theorem firstHigherRankAutocorrelation :
    autocorrelationKernel firstHigherRankRecurrence 2 =
      !![10, -8; -8, 10] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [autocorrelationKernel, convolutionMatrix,
      convolutionCoefficient, firstHigherRankRecurrence, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The displayed `2 x 2` Jacobian is positive definite. -/
theorem firstHigherRankAutocorrelation_posDef :
    (!![10, -8; -8, 10] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [← firstHigherRankAutocorrelation]
  apply autocorrelationKernel_posDef
  norm_num [firstHigherRankRecurrence]

end

end FurtherToeplitzPositroids
