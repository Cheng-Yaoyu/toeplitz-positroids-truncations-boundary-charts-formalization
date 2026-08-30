import FurtherToeplitzPositroids.PositiveCompletion
import Mathlib.LinearAlgebra.Pi

/-!
# Strictly positive row compression

This module formalizes Proposition 3.1 and Corollary 3.3.  Since mathlib does
not currently expose matroid truncation as a primitive operation, the final
statement uses the equivalent independence-set characterization.
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- An explicit one-row strictly totally positive compression. -/
def oneRowPositiveCompression (m : ℕ) : Matrix (Fin 1) (Fin m) ℝ :=
  fun _ _ ↦ 1

/-- The all-one one-row compression is strictly totally positive. -/
theorem oneRowPositiveCompression_totallyPositive (m : ℕ) :
    TotallyPositive (oneRowPositiveCompression m) := by
  intro k rows cols
  have hk : k ≤ 1 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  interval_cases k
  · simp
  · rw [orderedMinor_one]
    simp [oneRowPositiveCompression]

/-- An explicit two-row strictly totally positive compression. -/
def twoRowPositiveCompression (m : ℕ) : Matrix (Fin 2) (Fin m) ℝ :=
  fun i j ↦ if i = 0 then 1 else j.val + 1

/-- The explicit two-row compression is strictly totally positive. -/
theorem twoRowPositiveCompression_totallyPositive (m : ℕ) :
    TotallyPositive (twoRowPositiveCompression m) := by
  intro k rows cols
  have hk : k ≤ 2 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  interval_cases k
  · simp
  · rw [orderedMinor_one]
    simp only [twoRowPositiveCompression]
    split_ifs <;> positivity
  · rw [orderEmbedding_fin_self_eq_allRows rows, orderedMinor_two]
    simp only [allRows_apply_eq_self, twoRowPositiveCompression]
    simp

/-- An explicit three-row strictly totally positive compression, obtained
from the first three monomials at the positive increasing nodes `j+1`. -/
def threeRowPositiveCompression (m : ℕ) : Matrix (Fin 3) (Fin m) ℝ :=
  fun i j ↦ if i = 0 then 1 else if i = 1 then j.val + 1 else (j.val + 1) ^ 2

/-- The explicit three-row generalized Vandermonde compression is strictly
totally positive. -/
theorem threeRowPositiveCompression_totallyPositive (m : ℕ) :
    TotallyPositive (threeRowPositiveCompression m) := by
  intro k rows cols
  have hk : k ≤ 3 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  interval_cases k
  · simp
  · rw [orderedMinor_one]
    simp only [threeRowPositiveCompression]
    split_ifs <;> positivity
  · rw [orderedMinor_two]
    have hrow : rows 0 < rows 1 := rows.strictMono (by decide)
    have hcol : cols 0 < cols 1 := cols.strictMono (by decide)
    generalize hr0 : rows 0 = r0 at hrow ⊢
    generalize hr1 : rows 1 = r1 at hrow ⊢
    fin_cases r0 <;> fin_cases r1 <;> simp at hrow
    · simp only [threeRowPositiveCompression]
      norm_num
    · simp only [threeRowPositiveCompression]
      norm_num
      have hx : (0 : ℝ) < (cols 0).val + 1 := by positivity
      have hxy₀ : ((cols 0).val : ℝ) < (cols 1).val := by
        exact_mod_cast hcol
      have hxy : ((cols 0).val : ℝ) + 1 < (cols 1).val + 1 := by linarith
      have hy : (0 : ℝ) < (cols 1).val + 1 := hx.trans hxy
      nlinarith [mul_pos (sub_pos.mpr hxy) (add_pos hy hx)]
    · simp only [threeRowPositiveCompression]
      norm_num
      have hx : (0 : ℝ) < (cols 0).val + 1 := by positivity
      have hxy₀ : ((cols 0).val : ℝ) < (cols 1).val := by
        exact_mod_cast hcol
      have hxy : ((cols 0).val : ℝ) + 1 < (cols 1).val + 1 := by linarith
      have hy : (0 : ℝ) < (cols 1).val + 1 := hx.trans hxy
      nlinarith [mul_pos (mul_pos hx hy) (sub_pos.mpr hxy)]
  · rw [orderEmbedding_fin_self_eq_allRows rows, orderedMinor, Matrix.det_fin_three]
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self]
    simp only [threeRowPositiveCompression, h10, h20, h21, if_pos,
      if_false]
    have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
    have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
    have hx : (0 : ℝ) < (cols 0).val + 1 := by positivity
    have hxy₀ : ((cols 0).val : ℝ) < (cols 1).val := by exact_mod_cast h₀₁
    have hyz₀ : ((cols 1).val : ℝ) < (cols 2).val := by exact_mod_cast h₁₂
    have hxy : ((cols 0).val : ℝ) + 1 < (cols 1).val + 1 := by linarith
    have hyz : ((cols 1).val : ℝ) + 1 < (cols 2).val + 1 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hxy)
      (mul_pos (sub_pos.mpr (hxy.trans hyz)) (sub_pos.mpr hyz))]

/-- Cauchy--Binet preserves total nonnegativity under rectangular matrix
multiplication. -/
theorem totallyNonnegative_mul
    {k m n : ℕ} {P : Matrix (Fin k) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyNonnegative P) (hA : TotallyNonnegative A) :
    TotallyNonnegative (P * A) := by
  intro q rows cols
  have hsub :
      (P * A).submatrix rows cols =
        P.submatrix rows id * A.submatrix id cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [orderedMinor, hsub, Matrix.det_mul_eq_sum_orderedMinor]
  exact Finset.sum_nonneg fun middle _ ↦
    mul_nonneg (hP.orderedMinor_nonneg rows middle)
      (hA.orderedMinor_nonneg middle cols)

/-- A rectangular matrix with independent columns has a nonzero square row
minor. -/
theorem exists_orderedRowMinor_ne_zero_of_linearIndependent_columns_general
    {s m : ℕ} (B : Matrix (Fin m) (Fin s) ℝ)
    (hB : LinearIndependent ℝ B.col) :
    ∃ rows : Fin s ↪o Fin m,
      orderedMinor B rows (allRows s) ≠ 0 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hB
  obtain ⟨g, hg⟩ := B.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : Matrix (Fin s) (Fin m) ℝ := LinearMap.toMatrix' g
  have hCB : C * B = 1 := by
    have hmat := congrArg LinearMap.toMatrix' hg
    have hBmat : LinearMap.toMatrix' B.mulVecLin = B := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [LinearMap.toMatrix'_comp] at hmat
    rw [hBmat] at hmat
    simpa [C] using hmat
  by_contra hminor
  push Not at hminor
  have hdet := Matrix.det_mul_eq_sum_orderedMinor C B
  rw [hCB, Matrix.det_one] at hdet
  simp_rw [hminor] at hdet
  simp at hdet

/-- If at most `k` selected columns are independent before a strictly totally
positive row compression, they remain independent afterwards. -/
theorem positiveCompression_preserves_ordered_independence
    {s k m n : ℕ} (hsk : s ≤ k)
    {P : Matrix (Fin k) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyPositive P) (hA : TotallyNonnegative A)
    (cols : Fin s ↪o Fin n)
    (hind : LinearIndependent ℝ (fun j : Fin s ↦ A.col (cols j))) :
    LinearIndependent ℝ (fun j : Fin s ↦ (P * A).col (cols j)) := by
  let B : Matrix (Fin m) (Fin s) ℝ := A.submatrix id cols
  have hBind : LinearIndependent ℝ B.col := by
    simpa [B, Matrix.col, Matrix.submatrix] using hind
  obtain ⟨middle, hmiddle⟩ :=
    exists_orderedRowMinor_ne_zero_of_linearIndependent_columns_general B hBind
  have hmiddleA : orderedMinor A middle cols ≠ 0 := by
    change (A.submatrix middle cols).det ≠ 0
    simpa [B, allRows, Matrix.submatrix_submatrix] using hmiddle
  have hmiddlePos : 0 < orderedMinor A middle cols :=
    lt_of_le_of_ne (hA.orderedMinor_nonneg middle cols) fun h ↦ hmiddleA h.symm
  let outputRows : Fin s ↪o Fin k := Fin.castLEOrderEmb hsk
  have hminorPos : 0 < orderedMinor (P * A) outputRows cols := by
    have hsub :
        (P * A).submatrix outputRows cols =
          P.submatrix outputRows id * A.submatrix id cols := by
      ext i j
      simp [Matrix.mul_apply]
    rw [orderedMinor, hsub, Matrix.det_mul_eq_sum_orderedMinor]
    apply Finset.sum_pos'
    · intro rows _
      exact mul_nonneg
        (hP.orderedMinor_pos outputRows rows).le
        (hA.orderedMinor_nonneg rows cols)
    · refine ⟨middle, Finset.mem_univ middle, ?_⟩
      exact mul_pos (hP.orderedMinor_pos outputRows middle) hmiddlePos
  let C : Matrix (Fin s) (Fin n) ℝ := (P * A).submatrix outputRows id
  have hCminor : orderedMinor C (allRows s) cols ≠ 0 := by
    change ((P * A).submatrix outputRows cols).det ≠ 0
    simpa [C, allRows, Matrix.submatrix_submatrix] using hminorPos.ne'
  have hCind : LinearIndependent ℝ (fun j : Fin s ↦ C.col (cols j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns C cols).mp hCminor
  let restrictRows : (Fin k → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    LinearMap.pi fun i ↦ LinearMap.proj (outputRows i)
  apply LinearIndependent.of_comp restrictRows
  have hfamily :
      (restrictRows ∘ fun j : Fin s ↦ (P * A).col (cols j)) =
        fun j : Fin s ↦ C.col (cols j) := by
    funext j i
    rfl
  rw [hfamily]
  exact hCind

/-- Linear independence after compression implies linear independence before
compression, without a cardinality assumption. -/
theorem positiveCompression_reflects_ordered_independence
    {s k m n : ℕ} (P : Matrix (Fin k) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (cols : Fin s ↪o Fin n)
    (hind : LinearIndependent ℝ (fun j : Fin s ↦ (P * A).col (cols j))) :
    LinearIndependent ℝ (fun j : Fin s ↦ A.col (cols j)) := by
  apply LinearIndependent.of_comp P.mulVecLin
  have hfamily :
      (P.mulVecLin ∘ fun j : Fin s ↦ A.col (cols j)) =
        fun j : Fin s ↦ (P * A).col (cols j) := by
    funext j i
    simp [dotProduct, Matrix.mul_apply, Matrix.mulVecLin, Matrix.mulVec]
  rw [hfamily]
  exact hind

/-- Up to the number of compressed rows, compression preserves and reflects
ordered column independence. -/
theorem positiveCompression_ordered_independence_iff
    {s k m n : ℕ} (hsk : s ≤ k)
    {P : Matrix (Fin k) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyPositive P) (hA : TotallyNonnegative A)
    (cols : Fin s ↪o Fin n) :
    LinearIndependent ℝ (fun j : Fin s ↦ (P * A).col (cols j)) ↔
      LinearIndependent ℝ (fun j : Fin s ↦ A.col (cols j)) :=
  ⟨positiveCompression_reflects_ordered_independence P A cols,
    positiveCompression_preserves_ordered_independence hsk hP hA cols⟩

/-- An independent family of columns of a `k`-row matrix has cardinality at
most `k`. -/
theorem card_le_rows_of_ordered_independence
    {s k n : ℕ} {A : Matrix (Fin k) (Fin n) ℝ}
    {cols : Fin s ↪o Fin n}
    (hind : LinearIndependent ℝ (fun j : Fin s ↦ A.col (cols j))) :
    s ≤ k := by
  have hcard : Fintype.card (Fin s) ≤ Module.finrank ℝ (Fin k → ℝ) :=
    hind.fintype_card_le_finrank
  simpa using hcard

/-- The independence-set characterization of the rank-`k` truncation. -/
def IsRankTruncationOf {E : Type*} [Finite E]
    (k : ℕ) (N M : Matroid E) : Prop :=
  ∀ I : Set E, N.Indep I ↔ M.Indep I ∧ I.ncard ≤ k

/-- Proposition 3.1: strictly totally positive row compression realizes the
rank-`k` truncation of the represented column matroid. -/
theorem positiveCompression_isRankTruncation
    {k m n : ℕ} {P : Matrix (Fin k) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyPositive P) (hA : TotallyNonnegative A) :
    IsRankTruncationOf k (columnMatroid (P * A)) (columnMatroid A) := by
  intro I
  let hIfin : I.Finite := Set.toFinite I
  let s : Finset (Fin n) := hIfin.toFinset
  let q : ℕ := s.card
  let cols : Fin q ↪o Fin n := s.orderEmbOfFin rfl
  have hrange : Set.range cols = I := by
    rw [Finset.range_orderEmbOfFin]
    exact hIfin.coe_toFinset
  constructor
  · intro hcompressed
    have hcompressed' :
        LinearIndependent ℝ (fun j : Fin q ↦ (P * A).col (cols j)) :=
      (columnMatroid_indep_range_iff (P * A) cols).mp (hrange ▸ hcompressed)
    have horiginal :=
      positiveCompression_reflects_ordered_independence P A cols hcompressed'
    refine ⟨?_, ?_⟩
    · rw [← hrange, columnMatroid_indep_range_iff]
      exact horiginal
    · rw [← hrange, Set.ncard_range_of_injective cols.injective]
      simpa using card_le_rows_of_ordered_independence
        (s := q) (A := P * A) (cols := cols) hcompressed'
  · rintro ⟨horiginal, hcard⟩
    have horiginal' : LinearIndependent ℝ (fun j : Fin q ↦ A.col (cols j)) :=
      (columnMatroid_indep_range_iff A cols).mp (hrange ▸ horiginal)
    have hqk : q ≤ k := by
      have hqcard : q = I.ncard := by
        dsimp [q, s]
        exact (Set.ncard_eq_toFinset_card I hIfin).symm
      rw [hqcard]
      exact hcard
    have hcompressed :=
      positiveCompression_preserves_ordered_independence hqk hP hA cols horiginal'
    rw [← hrange, columnMatroid_indep_range_iff]
    exact hcompressed

/-- Corollary 3.3 in matrix form: the compressed representative is totally
nonnegative and has exactly the truncated independence sets. -/
theorem positiveCompression_realizes_truncation
    {k m n : ℕ} {P : Matrix (Fin k) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyPositive P) (hA : TotallyNonnegative A) :
    TotallyNonnegative (P * A) ∧
      IsRankTruncationOf k (columnMatroid (P * A)) (columnMatroid A) :=
  ⟨totallyNonnegative_mul hP.totallyNonnegative hA,
    positiveCompression_isRankTruncation hP hA⟩

end

end FurtherToeplitzPositroids
