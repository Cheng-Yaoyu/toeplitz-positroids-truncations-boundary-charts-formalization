import FurtherToeplitzPositroids.RectangularTN2
import ToeplitzPositroids.Matrix.Reversal
import ToeplitzPositroids.RankTwo.MatroidClassification
import ToeplitzPositroids.RankThree.Classification
import ToeplitzPositroids.RankThree.EndpointAlgebra
import ToeplitzPositroids.RankThree.MomentMatrix

/-!
# The low skeleton in arbitrary rank

This module develops the arbitrary-rank parallel-class infrastructure used in
Theorem 4.3.
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids ToeplitzPositroids
open ToeplitzPositroids.RankThree

noncomputable section

/-! ## Reversal transport -/

/-- A reversed column is a loop exactly when the corresponding original
column is a loop. -/
theorem isLoop_reverseMatrix_iff
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    IsLoop (reverseMatrix A) j ↔ IsLoop A j.rev := by
  rw [isLoop_iff_entry_eq_zero, isLoop_iff_entry_eq_zero]
  constructor
  · intro h i
    simpa [reverseMatrix] using h i.rev
  · intro h i
    simpa [reverseMatrix] using h i.rev

/-- Positive parallelism is transported by simultaneous row and column
reversal. -/
theorem columnsPositivelyParallel_reverseMatrix_iff
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) :
    ColumnsPositivelyParallel (reverseMatrix A) i j ↔
      ColumnsPositivelyParallel A i.rev j.rev := by
  constructor
  · rintro ⟨c, hc, hcol⟩
    refine ⟨c, hc, ?_⟩
    funext r
    have hr := congrFun hcol r.rev
    simpa [reverseMatrix, Matrix.col_apply] using hr
  · rintro ⟨c, hc, hcol⟩
    refine ⟨c, hc, ?_⟩
    funext r
    have hr := congrFun hcol r.rev
    simpa [reverseMatrix, Matrix.col_apply] using hr

/-! ## Geometric coefficient segments forced by parallel Toeplitz shifts -/

/-- Positive parallelism between two rectangular Toeplitz columns gives the
coefficient equalities obtained by reading the column equality row by row. -/
theorem toeplitzMatrix_columnsPositivelyParallel_entries
    {m n : ℕ} {a : ℤ → ℝ} {i j : Fin n}
    (hij : ColumnsPositivelyParallel (toeplitzMatrix m n a) i j) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ r : Fin m,
        a ((j : ℤ) - (r : ℤ)) = lambda * a ((i : ℤ) - (r : ℤ)) := by
  obtain ⟨lambda, hlambda, hcol⟩ := hij
  refine ⟨lambda, hlambda, ?_⟩
  intro r
  simpa [Matrix.col_apply] using congrFun hcol r

/-- A block of at least two mutually positive-parallel Toeplitz columns forces
the entire overlapping coefficient segment to be geometric.  For a block
`p, ..., p + L - 1` in an `m`-row matrix, the segment starts at
`p - (m - 1)` and contains `m + L - 1` coefficients. -/
theorem toeplitzMatrix_geometricSegment_of_parallelBlock
    {m n p L : ℕ} {a : ℤ → ℝ}
    (hm : 2 ≤ m) (hL : 2 ≤ L) (hbound : p + L ≤ n)
    (hparallel : ∀ t : Fin L,
      ColumnsPositivelyParallel (toeplitzMatrix m n a)
        ⟨p, by omega⟩ ⟨p + t, by omega⟩) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ (t : ℕ), t < m + L - 1 →
        a ((p : ℤ) - ((m : ℤ) - 1) + t) =
          a ((p : ℤ) - ((m : ℤ) - 1)) * lambda ^ t := by
  let first : Fin n := ⟨p, by omega⟩
  let second : Fin n := ⟨p + 1, by omega⟩
  obtain ⟨lambda, hlambda, hsecond⟩ :=
    toeplitzMatrix_columnsPositivelyParallel_entries
      (hparallel ⟨1, by omega⟩)
  have hbaseStep : a (p : ℤ) = lambda * a ((p : ℤ) - 1) := by
    have h := hsecond (⟨1, by omega⟩ : Fin m)
    change a (((second : Fin n) : ℤ) - 1) =
      lambda * a (((first : Fin n) : ℤ) - 1) at h
    simpa [first, second] using h
  have hstep : ∀ (k : ℕ), k < m + L - 2 →
      a ((p : ℤ) - ((m : ℤ) - 1) + (k + 1 : ℕ)) =
        lambda * a ((p : ℤ) - ((m : ℤ) - 1) + k) := by
    intro k hk
    by_cases hkm : k < m
    · let r : Fin m := ⟨m - 1 - k, by omega⟩
      have h := hsecond r
      have hleft : ((second : Fin n) : ℤ) - (r : ℤ) =
          (p : ℤ) - ((m : ℤ) - 1) + (k + 1 : ℕ) := by
        simp only [second, r]
        omega
      have hright : ((first : Fin n) : ℤ) - (r : ℤ) =
          (p : ℤ) - ((m : ℤ) - 1) + k := by
        simp only [first, r]
        omega
      rwa [hleft, hright] at h
    · let s : ℕ := k - m + 2
      have hsTwo : 2 ≤ s := by
        dsimp only [s]
        omega
      have hsL : s < L := by
        dsimp only [s]
        omega
      let current : Fin n := ⟨p + s, by omega⟩
      obtain ⟨mu, hmu, hcurrent⟩ :=
        toeplitzMatrix_columnsPositivelyParallel_entries
          (hparallel ⟨s, hsL⟩)
      have htop := hcurrent (⟨0, by omega⟩ : Fin m)
      have hnext := hcurrent (⟨1, by omega⟩ : Fin m)
      have htop' : a ((p : ℤ) + s) = mu * a (p : ℤ) := by
        change a (((current : Fin n) : ℤ) - 0) =
          mu * a (((first : Fin n) : ℤ) - 0) at htop
        simpa [current, first] using htop
      have hnext' : a ((p : ℤ) + s - 1) =
          mu * a ((p : ℤ) - 1) := by
        change a (((current : Fin n) : ℤ) - 1) =
          mu * a (((first : Fin n) : ℤ) - 1) at hnext
        simpa [current, first] using hnext
      have hsource :
          (p : ℤ) - ((m : ℤ) - 1) + k = (p : ℤ) + s - 1 := by
        dsimp only [s]
        omega
      have htarget :
          (p : ℤ) - ((m : ℤ) - 1) + (k + 1 : ℕ) =
            (p : ℤ) + s := by
        dsimp only [s]
        omega
      rw [hsource, htarget, htop', hnext', hbaseStep]
      ring
  refine ⟨lambda, hlambda, ?_⟩
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
      rw [hstep t (by omega), ih (by omega), pow_succ]
      ring

/-! ## The arbitrary-rank internal parallel trap -/

/-- The normalized three-row trap matrix in arbitrary ambient rank.

Here `u = m-k-1`, `v = k-2`, and hence `m = u+v+3`; `s` is the length of the parallel run.
The parameters `e` and `f` are the two exterior coefficients after division
by the common positive coefficient `c`. -/
def arbitraryParallelTrapCore
  (lambda e f : ℝ) (u v s : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![lambda ^ (u + v + 1), lambda ^ (u + v + 2), f;
    lambda ^ u, lambda ^ (u + 1), lambda ^ (u + s + 1);
    e, 1, lambda ^ s]

/-- Formula (13), with the negative powers absorbed into `e` and `f`. -/
theorem arbitraryParallelTrapCore_det
    (lambda e f : ℝ) (u v s : ℕ) :
    (arbitraryParallelTrapCore lambda e f u v s).det =
      lambda ^ u * (lambda ^ (u + v + s + 2) - f) *
        (e * lambda - 1) := by
  rw [Matrix.det_fin_three]
  simp [arbitraryParallelTrapCore, Matrix.cons_val_two, pow_add]
  ring

/-- The actual trap matrix after restoring the common coefficient factor. -/
def arbitraryParallelTrap
    (c lambda e f : ℝ) (u v s : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  c • arbitraryParallelTrapCore lambda e f u v s

theorem arbitraryParallelTrap_det
    (c lambda e f : ℝ) (u v s : ℕ) :
    (arbitraryParallelTrap c lambda e f u v s).det =
      c ^ 3 * lambda ^ u * (lambda ^ (u + v + s + 2) - f) *
        (e * lambda - 1) := by
  rw [arbitraryParallelTrap, Matrix.det_smul,
    arbitraryParallelTrapCore_det]
  simp only [Fintype.card_fin]
  ring

/-- Log-concavity at both endpoints makes the arbitrary-rank trap
determinant nonpositive. -/
theorem arbitraryParallelTrap_det_nonpos
    {c lambda e f : ℝ} {u v s : ℕ}
    (hc : 0 ≤ c) (hlambda : 0 ≤ lambda)
    (he : e * lambda ≤ 1)
    (hf : f ≤ lambda ^ (u + v + s + 2)) :
    (arbitraryParallelTrap c lambda e f u v s).det ≤ 0 := by
  rw [arbitraryParallelTrap_det]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg
      (mul_nonneg (pow_nonneg hc 3) (pow_nonneg hlambda u))
      (sub_nonneg.mpr hf))
    (sub_nonpos.mpr he)

/-- Once the two endpoint log-concavity inequalities are known, a
nonnegative trap minor contradicts strict maximality at both ends. -/
theorem arbitraryParallelTrap_contradiction
    {c lambda e f : ℝ} {u v s : ℕ}
    (hc : 0 < c) (hlambda : 0 < lambda)
    (he : e * lambda ≤ 1)
    (hf : f ≤ lambda ^ (u + v + s + 2))
    (hminor : 0 ≤ (arbitraryParallelTrap c lambda e f u v s).det)
    (hleftMaximal : e * lambda ≠ 1)
    (hrightMaximal : f ≠ lambda ^ (u + v + s + 2)) : False := by
  have hnonpos : (arbitraryParallelTrap c lambda e f u v s).det ≤ 0 :=
    arbitraryParallelTrap_det_nonpos hc.le hlambda.le he hf
  have hzero : (arbitraryParallelTrap c lambda e f u v s).det = 0 :=
    le_antisymm hnonpos hminor
  rw [arbitraryParallelTrap_det] at hzero
  rcases mul_eq_zero.mp hzero with hproduct | hleft
  · rcases mul_eq_zero.mp hproduct with hprefix | hright
    · have hcne : c ^ 3 ≠ 0 := pow_ne_zero _ hc.ne'
      have hlambdane : lambda ^ u ≠ 0 := pow_ne_zero _ hlambda.ne'
      exact (mul_ne_zero hcne hlambdane) hprefix
    · apply hrightMaximal
      exact (sub_eq_zero.mp hright).symm
  · apply hleftMaximal
    exact sub_eq_zero.mp hleft

/-- A natural-indexed maximal nontrivial parallel block in an arbitrary-row
matrix.  The block consists of columns `p, ..., p + L - 1`. -/
structure IsMaximalToeplitzParallelBlock {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (p L : ℕ) : Prop where
  two_le : 2 ≤ L
  bound : p + L ≤ n
  nonloop (t : Fin L) : ¬IsLoop A ⟨p + t, by omega⟩
  parallel (t : Fin L) :
    ColumnsPositivelyParallel A ⟨p, by omega⟩ ⟨p + t, by omega⟩
  left_maximal (hp : 1 ≤ p) :
    ¬ColumnsPositivelyParallel A ⟨p - 1, by omega⟩ ⟨p, by omega⟩
  right_maximal (hright : p + L < n) :
    ¬ColumnsPositivelyParallel A
      ⟨p + L - 1, by omega⟩ ⟨p + L, hright⟩

/-- Formula (13) excludes a maximal nontrivial parallel block with nonloop
neighbors on both sides in every ambient row rank at least three. -/
theorem toeplitzMatrix_no_internal_maximalParallelBlock
    {m n p L : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hp : 1 ≤ p) (hright : p + L < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hblock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n a) p L) : False := by
  have hL : 2 ≤ L := hblock.two_le
  let first : Fin n := ⟨p, by omega⟩
  let left : Fin n := ⟨p - 1, by omega⟩
  let last : Fin n := ⟨p + L - 1, by omega⟩
  let right : Fin n := ⟨p + L, hright⟩
  let z₀ : ℤ := (p : ℤ) - ((m : ℤ) - 1)
  let u : ℕ := m - 3
  obtain ⟨lambda, hlambda, hgeom⟩ :=
    toeplitzMatrix_geometricSegment_of_parallelBlock
      (a := a) (m := m) (n := n) (p := p) (L := L)
      (by omega) hL hblock.bound hblock.parallel
  let c : ℝ := a z₀
  have hgeomAt : ∀ (t : ℕ), t < m + L - 1 →
      a (z₀ + t) = c * lambda ^ t := by
    intro t ht
    simpa [z₀, c] using hgeom t ht
  have hcne : c ≠ 0 := by
    obtain ⟨r, hr⟩ := exists_entry_pos_of_not_isLoop hA
      (hblock.nonloop ⟨0, by omega⟩)
    rw [toeplitzMatrix_apply] at hr
    let t : ℕ := m - 1 - r.val
    have ht : t < m + L - 1 := by
      dsimp only [t]
      omega
    have hindex : z₀ + t = (p : ℤ) - (r : ℤ) := by
      dsimp only [z₀, t]
      omega
    have h := hgeomAt t ht
    rw [hindex] at h
    intro hc
    rw [hc] at h
    simp only [zero_mul] at h
    exact hr.ne' h
  have hcNonneg : 0 ≤ c := by
    let bottom : Fin m := ⟨m - 1, by omega⟩
    have hentry := hA.entry_nonneg bottom first
    rw [toeplitzMatrix_apply] at hentry
    have hindex : ((first : Fin n) : ℤ) - (bottom : ℤ) = z₀ := by
      simp only [first, bottom, z₀]
      omega
    rwa [hindex] at hentry
  have hc : 0 < c := lt_of_le_of_ne hcNonneg (Ne.symm hcne)
  let e : ℝ := a (z₀ - 1) / c
  let f : ℝ := a ((p : ℤ) + L) / c
  have hec : a (z₀ - 1) = c * e := by
    dsimp only [e]
    field_simp
  have hfc : a ((p : ℤ) + L) = c * f := by
    dsimp only [f]
    field_simp
  have hu : u + 3 = m := by
    dsimp only [u]
    omega
  have hgeomZero : a z₀ = c := by
    simpa using hgeomAt 0 (by omega)
  have hgeomOne : a (z₀ + 1) = c * lambda := by
    simpa using hgeomAt 1 (by omega)
  have hgeomU : a (z₀ + u) = c * lambda ^ u :=
    hgeomAt u (by omega)
  have hgeomUOne : a (z₀ + (u + 1)) = c * lambda ^ (u + 1) :=
    hgeomAt (u + 1) (by omega)
  have hgeomUTwo : a (z₀ + (u + 2)) = c * lambda ^ (u + 2) :=
    hgeomAt (u + 2) (by omega)
  have hgeomL : a (z₀ + L) = c * lambda ^ L :=
    hgeomAt L (by omega)
  have hgeomUL : a (z₀ + (u + L)) = c * lambda ^ (u + L) :=
    hgeomAt (u + L) (by omega)
  have hgeomULOne : a (z₀ + (u + L + 1)) =
      c * lambda ^ (u + L + 1) :=
    hgeomAt (u + L + 1) (by omega)
  have hleftTop : a ((p : ℤ) - 1) = c * lambda ^ (u + 1) := by
    rw [← hgeomUOne]
    congr 1
    dsimp only [z₀, u]
    omega
  have hleftMiddle : a ((p : ℤ) - 2) = c * lambda ^ u := by
    rw [← hgeomU]
    congr 1
    dsimp only [z₀, u]
    omega
  have hfirstTop : a (p : ℤ) = c * lambda ^ (u + 2) := by
    rw [← hgeomUTwo]
    congr 1
    dsimp only [z₀, u]
    omega
  have hrightMiddle : a ((p : ℤ) + L - 1) =
      c * lambda ^ (u + L + 1) := by
    rw [← hgeomULOne]
    congr 1
    dsimp only [z₀, u]
    omega
  have hrightBottom : a ((p : ℤ) + L - ((m : ℤ) - 1)) =
      c * lambda ^ L := by
    rw [← hgeomL]
    congr 1
    dsimp only [z₀]
    omega
  have hleftExterior : a ((p : ℤ) - m) = c * e := by
    rw [← hec]
    congr 1
    dsimp only [z₀]
    omega
  have hpPredCast : (((p - 1 : ℕ) : ℤ)) = (p : ℤ) - 1 := by omega
  have hmPredCast : (((m - 1 : ℕ) : ℤ)) = (m : ℤ) - 1 := by omega
  have hpLPredCast : (((p + L - 1 : ℕ) : ℤ)) =
      (p : ℤ) + L - 1 := by omega
  have hpLCast : (((p + L : ℕ) : ℤ)) = (p : ℤ) + L := by omega
  have hmLPredPredCast : (((m + L - 2 : ℕ) : ℤ)) =
      (m : ℤ) + L - 2 := by omega
  have hleftTopNat : a ((p - 1 : ℕ) : ℤ) = c * lambda ^ (u + 1) := by
    rw [hpPredCast]
    exact hleftTop
  have hleftMiddleNat : a (((p - 1 : ℕ) : ℤ) - 1) = c * lambda ^ u := by
    rw [hpPredCast]
    have hindex : (p : ℤ) - 1 - 1 = (p : ℤ) - 2 := by ring
    rw [hindex]
    exact hleftMiddle
  have hleftExteriorNat :
      a (((p - 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ)) = c * e := by
    rw [hpPredCast, hmPredCast]
    have hindex : (p : ℤ) - 1 - ((m : ℤ) - 1) = (p : ℤ) - m := by ring
    rw [hindex]
    exact hleftExterior
  have hfirstBottomNat :
      a ((p : ℤ) - ((m - 1 : ℕ) : ℤ)) = c := by
    rw [hmPredCast]
  have hrightBottomNat :
      a (((p + L : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ)) =
        c * lambda ^ L := by
    rw [hpLCast, hmPredCast]
    exact hrightBottom
  have hrightBottomTarget :
      a ((p : ℤ) + L - ((m - 1 : ℕ) : ℤ)) = c * lambda ^ L := by
    rw [hmPredCast]
    exact hrightBottom
  have hlog := toeplitzMatrix_displayedLogConcave
    (by omega : 2 ≤ m) (by omega : 2 ≤ n) (hA.tnUpTo 2)
  have hlogLeft := hlog z₀ (by
    simp only [displayedLower, z₀]
    omega) (by
    simp only [displayedUpper, z₀]
    omega)
  have heLambda : e * lambda ≤ 1 := by
    apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hc)
    calc
      c ^ 2 * (e * lambda) = (c * e) * (c * lambda) := by ring
      _ = a (z₀ - 1) * a (z₀ + 1) := by rw [hec, hgeomOne]
      _ ≤ a z₀ * a z₀ := hlogLeft
      _ = c ^ 2 * 1 := by rw [hgeomZero]; ring
  have hrightIndex : z₀ + (u + L + 1) = (p : ℤ) + L - 1 := by
    dsimp only [z₀, u]
    omega
  have hlogRight := hlog ((p : ℤ) + L - 1) (by
    simp only [displayedLower]
    omega) (by
    simp only [displayedUpper]
    omega)
  have hrightPredIndex : ((p : ℤ) + L - 1) - 1 =
      (p : ℤ) + L - 2 := by ring
  have hrightSuccIndex : ((p : ℤ) + L - 1) + 1 =
      (p : ℤ) + L := by ring
  rw [hrightPredIndex, hrightSuccIndex] at hlogRight
  have hfactorPos : 0 < c ^ 2 * lambda ^ (u + L) :=
    mul_pos (sq_pos_of_pos hc) (pow_pos hlambda _)
  have hfLambda : f ≤ lambda ^ (u + L + 2) := by
    apply le_of_mul_le_mul_left ?_ hfactorPos
    calc
      (c ^ 2 * lambda ^ (u + L)) * f =
          a (z₀ + (u + L)) * a ((p : ℤ) + L) := by
        rw [hgeomUL, hfc]
        ring
      _ ≤ a ((p : ℤ) + L - 1) * a ((p : ℤ) + L - 1) := by
        have hpred : z₀ + (u + L) = (p : ℤ) + L - 2 := by
          dsimp only [z₀, u]
          omega
        rw [hpred]
        exact hlogRight
      _ = (c ^ 2 * lambda ^ (u + L)) * lambda ^ (u + L + 2) := by
        rw [hrightMiddle]
        simp only [pow_add]
        ring
  let row₀ : Fin m := ⟨0, by omega⟩
  let row₁ : Fin m := ⟨1, by omega⟩
  let rowLast : Fin m := ⟨m - 1, by omega⟩
  have hrow₀₁ : row₀ < row₁ := by simp [row₀, row₁]
  have hrow₁Last : row₁ < rowLast := by simp [row₁, rowLast]; omega
  let rows : Fin 3 ↪o Fin m :=
    selectedTripleEmbedding row₀ row₁ rowLast hrow₀₁ hrow₁Last
  have hleftFirst : left < first := by
    apply Fin.mk_lt_mk.mpr
    change p - 1 < p
    omega
  have hfirstRight : first < right := by
    apply Fin.mk_lt_mk.mpr
    change p < p + L
    omega
  let cols : Fin 3 ↪o Fin n :=
    selectedTripleEmbedding left first right hleftFirst hfirstRight
  have htrapMatrix :
      (toeplitzMatrix m n a).submatrix rows cols =
        arbitraryParallelTrap c lambda e f u 0 L := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rows, cols, row₀, row₁, rowLast, left, first, right,
        arbitraryParallelTrap, arbitraryParallelTrapCore, toeplitzMatrix_apply,
        hleftTop, hleftTopNat, hleftMiddleNat, hleftExteriorNat, hfirstTop,
        hfirstBottomNat, hrightMiddle, hrightBottomTarget, hfc]
  have hminor : 0 ≤ (arbitraryParallelTrap c lambda e f u 0 L).det := by
    have h := hA.orderedMinor_nonneg rows cols
    rw [orderedMinor, htrapMatrix] at h
    exact h
  have hleftFactor : e * lambda ≠ 1 := by
    intro heq
    apply hblock.left_maximal hp
    refine ⟨lambda, hlambda, ?_⟩
    funext r
    simp only [Matrix.col_apply, toeplitzMatrix_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r.val = m - 1
    · have hfirstIndex : (p : ℤ) - (r : ℤ) = z₀ := by
        dsimp only [z₀]
        omega
      have hleftIndex : ((p - 1 : ℕ) : ℤ) - (r : ℤ) = z₀ - 1 := by
        dsimp only [z₀]
        omega
      rw [hfirstIndex, hleftIndex, hgeomZero, hec]
      calc
        c = 1 * c := by ring
        _ = (e * lambda) * c := by rw [heq]
        _ = lambda * (c * e) := by ring
    · let t : ℕ := m - 1 - r.val
      have htPos : 1 ≤ t := by dsimp only [t]; omega
      have ht : t < m + L - 1 := by dsimp only [t]; omega
      have htPred : t - 1 < m + L - 1 := by omega
      have hfirstIndex : (p : ℤ) - (r : ℤ) = z₀ + t := by
        dsimp only [z₀, t]
        omega
      have hleftIndex : ((p - 1 : ℕ) : ℤ) - (r : ℤ) =
          z₀ + (t - 1) := by
        dsimp only [z₀, t]
        omega
      have htPredCast : (t : ℤ) - 1 = ((t - 1 : ℕ) : ℤ) := by omega
      rw [hfirstIndex, hleftIndex, htPredCast, hgeomAt t ht,
        hgeomAt (t - 1) htPred]
      have htpow : lambda ^ t = lambda * lambda ^ (t - 1) := by
        calc
          lambda ^ t = lambda ^ ((t - 1) + 1) := by congr 1; omega
          _ = lambda ^ (t - 1) * lambda := by rw [pow_succ]
          _ = lambda * lambda ^ (t - 1) := by ring
      rw [htpow]
      ring
  have hrightFactor : f ≠ lambda ^ (u + L + 2) := by
    intro hfeq
    apply hblock.right_maximal hright
    refine ⟨lambda, hlambda, ?_⟩
    funext r
    simp only [Matrix.col_apply, toeplitzMatrix_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r.val = 0
    · have hrFin : r = ⟨0, by omega⟩ := Fin.ext hr
      rw [hrFin]
      change a ((p + L : ℕ) : ℤ) =
        lambda * a ((p + L - 1 : ℕ) : ℤ)
      rw [hpLCast, hpLPredCast, hfc, hrightMiddle, hfeq, pow_succ]
      ring
    · let t : ℕ := m + L - 2 - r.val
      have hrPos : 1 ≤ r.val := by omega
      have hrLe : r.val ≤ m - 1 := by omega
      have htEq : t + r.val = m + L - 2 := by
        dsimp only [t]
        omega
      have htEqInt := congrArg (fun q : ℕ ↦ (q : ℤ)) htEq
      push_cast at htEqInt
      rw [hmLPredPredCast] at htEqInt
      have ht : t < m + L - 1 := by dsimp only [t]; omega
      have htSucc : t + 1 < m + L - 1 := by dsimp only [t]; omega
      have hlastIndex : (((p + L - 1 : ℕ) : ℤ) - (r : ℤ)) =
          z₀ + t := by
        rw [hpLPredCast]
        dsimp only [z₀]
        omega
      have hrightIndex' : (((p + L : ℕ) : ℤ) - (r : ℤ)) =
          z₀ + (t + 1) := by
        rw [hpLCast]
        dsimp only [z₀]
        omega
      have htSuccCast : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by omega
      rw [hrightIndex', hlastIndex, ← htSuccCast,
        hgeomAt (t + 1) htSucc, hgeomAt t ht,
        pow_succ]
      ring
  exact arbitraryParallelTrap_contradiction hc hlambda heLambda hfLambda hminor
    hleftFactor hrightFactor

/-- Theorem 4.3, internal-class part: every maximal nontrivial parallel block
of a totally nonnegative Toeplitz matrix with at least three rows is initial
or terminal. -/
theorem toeplitzMatrix_endpointParallel
    {m n p L : ℕ} {a : ℤ → ℝ} (hm : 3 ≤ m)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hblock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n a) p L) :
    p = 0 ∨ p + L = n := by
  by_contra hinterior
  have hpNe : p ≠ 0 := fun hp ↦ hinterior (Or.inl hp)
  have hrightNe : p + L ≠ n := fun hright ↦ hinterior (Or.inr hright)
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hpNe
  have hright : p + L < n := lt_of_le_of_ne hblock.bound hrightNe
  exact toeplitzMatrix_no_internal_maximalParallelBlock hm hp hright hA hblock

/-! ## Loop-adjacent endpoint classes -/

/-- Immediately after a loop, a nonloop Toeplitz column cannot be parallel to
its successor.  Thus a nonempty loop prefix forces the initial nonloop class
in Theorem 4.3 to be a singleton. -/
theorem toeplitzMatrix_not_parallel_after_loop
    {m n p : ℕ} {a : ℤ → ℝ}
    (hm : 2 ≤ m) (hp : 1 ≤ p) (hbound : p + 1 < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hloop : IsLoop (toeplitzMatrix m n a) ⟨p - 1, by omega⟩)
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨p, by omega⟩) :
    ¬ColumnsPositivelyParallel (toeplitzMatrix m n a)
      ⟨p, by omega⟩ ⟨p + 1, by omega⟩ := by
  obtain ⟨r, hrpos⟩ := exists_entry_pos_of_not_isLoop hA hnonloop
  rw [toeplitzMatrix_apply] at hrpos
  have hrZero : r.val = 0 := by
    by_contra hr
    let rpred : Fin m := ⟨r.val - 1, by omega⟩
    have hzero := isLoop_iff_entry_eq_zero.mp hloop rpred
    rw [toeplitzMatrix_apply] at hzero
    have hindex : (((p - 1 : ℕ) : ℤ) - (rpred : ℤ)) =
        (p : ℤ) - (r : ℤ) := by
      dsimp only [rpred]
      omega
    rw [hindex] at hzero
    exact hrpos.ne' hzero
  have hrFin : r = ⟨0, by omega⟩ := Fin.ext hrZero
  have hap : 0 < a (p : ℤ) := by
    rw [hrFin] at hrpos
    simpa using hrpos
  have hzeroPred := isLoop_iff_entry_eq_zero.mp hloop (⟨0, by omega⟩ : Fin m)
  rw [toeplitzMatrix_apply] at hzeroPred
  have hpredIndex : (((p - 1 : ℕ) : ℤ) - (0 : ℤ)) =
      (p : ℤ) - 1 := by omega
  have hzeroPred' : a ((p : ℤ) - 1) = 0 := by
    change a (((p - 1 : ℕ) : ℤ) - 0) = 0 at hzeroPred
    rwa [hpredIndex] at hzeroPred
  rintro ⟨lambda, hlambda, hcols⟩
  have hrow := congrFun hcols (⟨1, by omega⟩ : Fin m)
  simp only [Matrix.col_apply, toeplitzMatrix_apply, Pi.smul_apply, smul_eq_mul] at hrow
  have hrow' : a (p : ℤ) = lambda * a ((p : ℤ) - 1) := by
    change a (((p + 1 : ℕ) : ℤ) - 1) =
      lambda * a ((p : ℤ) - 1) at hrow
    have hindex : ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ) := by omega
    rwa [hindex] at hrow
  rw [hzeroPred'] at hrow'
  exact hap.ne' (by simpa using hrow')

/-- Immediately before a loop, a nonloop Toeplitz column cannot be parallel
to its predecessor.  This is the right-hand loop-boundary assertion of
Theorem 4.3. -/
theorem toeplitzMatrix_not_parallel_before_loop
    {m n q : ℕ} {a : ℤ → ℝ}
    (hm : 2 ≤ m) (hq : 1 ≤ q) (hbound : q + 1 < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨q, by omega⟩)
    (hloop : IsLoop (toeplitzMatrix m n a) ⟨q + 1, hbound⟩) :
    ¬ColumnsPositivelyParallel (toeplitzMatrix m n a)
      ⟨q - 1, by omega⟩ ⟨q, by omega⟩ := by
  obtain ⟨r, hrpos⟩ := exists_entry_pos_of_not_isLoop hA hnonloop
  rw [toeplitzMatrix_apply] at hrpos
  have hrLast : r.val = m - 1 := by
    by_contra hr
    let rsucc : Fin m := ⟨r.val + 1, by omega⟩
    have hzero := isLoop_iff_entry_eq_zero.mp hloop rsucc
    rw [toeplitzMatrix_apply] at hzero
    have hindex : (((q + 1 : ℕ) : ℤ) - (rsucc : ℤ)) =
        (q : ℤ) - (r : ℤ) := by
      dsimp only [rsucc]
      omega
    rw [hindex] at hzero
    exact hrpos.ne' hzero
  let rowPred : Fin m := ⟨m - 2, by omega⟩
  have hzeroSucc := isLoop_iff_entry_eq_zero.mp hloop
    (⟨m - 1, by omega⟩ : Fin m)
  rw [toeplitzMatrix_apply] at hzeroSucc
  rintro ⟨lambda, hlambda, hcols⟩
  have hrow := congrFun hcols rowPred
  simp only [Matrix.col_apply, toeplitzMatrix_apply, Pi.smul_apply, smul_eq_mul] at hrow
  have hrightIndex : (q : ℤ) - (rowPred : ℤ) =
      ((q + 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) := by
    dsimp only [rowPred]
    omega
  have hleftIndex : (((q - 1 : ℕ) : ℤ) - (rowPred : ℤ)) =
      (q : ℤ) - (r : ℤ) := by
    dsimp only [rowPred]
    omega
  rw [hrightIndex, hleftIndex, hzeroSucc] at hrow
  have hzero : a ((q : ℤ) - (r : ℤ)) = 0 :=
    (mul_eq_zero.mp hrow.symm).resolve_left hlambda.ne'
  exact hrpos.ne' hzero

/-! ## The loop-boundary case of endpoint protection -/

/-- Full row rank and at least three rows leave at least three columns at or
after the first nonloop column.  Otherwise every maximal minor contains a
loop column. -/
theorem two_successors_of_fullRowRank_of_initial_loops
    {m n p : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hm : 3 ≤ m) (hpBound : p < n) (hfull : HasFullRowRank A)
    (hloops : ∀ j : Fin n, j.val < p → IsLoop A j) :
    p + 2 < n := by
  by_contra hbound
  obtain ⟨cols, hcols⟩ := hfull
  have h₀₁ : cols ⟨0, by omega⟩ < cols ⟨1, by omega⟩ :=
    cols.strictMono (Fin.mk_lt_mk.mpr (by omega))
  have h₁₂ : cols ⟨1, by omega⟩ < cols ⟨2, by omega⟩ :=
    cols.strictMono (Fin.mk_lt_mk.mpr (by omega))
  have hfirst : (cols ⟨0, by omega⟩).val < p := by
    by_contra hfirst
    have hpFirst : p ≤ (cols ⟨0, by omega⟩).val := by omega
    have hlastBound := (cols ⟨2, by omega⟩).isLt
    omega
  have hloop := hloops (cols ⟨0, by omega⟩) hfirst
  have hzeroEntries := isLoop_iff_entry_eq_zero.mp hloop
  apply hcols
  rw [orderedMinor]
  apply Matrix.det_eq_zero_of_column_eq_zero ⟨0, by omega⟩
  intro i
  exact hzeroEntries (allRows m i)

/-- The increasing embedding selecting the first three rows of an arbitrary
matrix with at least three rows. -/
def topThreeRows (m : ℕ) (hm : 3 ≤ m) : Fin 3 ↪o Fin m :=
  selectedTripleEmbedding ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- The increasing embedding selecting columns `p`, `p+1`, and `p+2`. -/
def consecutiveThreeColumns {n : ℕ} (p : ℕ) (hbound : p + 2 < n) :
    Fin 3 ↪o Fin n :=
  selectedTripleEmbedding ⟨p, by omega⟩ ⟨p + 1, by omega⟩ ⟨p + 2, hbound⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- If column `p-1` is a loop and column `p` is a nonloop, then the top
coefficient of column `p` is positive. -/
theorem toeplitzMatrix_top_coefficient_pos_after_loop
    {m n p : ℕ} {a : ℤ → ℝ}
    (hm : 2 ≤ m) (hp : 1 ≤ p) (hpBound : p < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hloop : IsLoop (toeplitzMatrix m n a) ⟨p - 1, by omega⟩)
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨p, hpBound⟩) :
    0 < a (p : ℤ) := by
  obtain ⟨r, hrpos⟩ := exists_entry_pos_of_not_isLoop hA hnonloop
  rw [toeplitzMatrix_apply] at hrpos
  have hrZero : r.val = 0 := by
    by_contra hr
    let rpred : Fin m := ⟨r.val - 1, by omega⟩
    have hzero := isLoop_iff_entry_eq_zero.mp hloop rpred
    rw [toeplitzMatrix_apply] at hzero
    have hindex : (((p - 1 : ℕ) : ℤ) - (rpred : ℤ)) =
        (p : ℤ) - (r : ℤ) := by
      dsimp only [rpred]
      omega
    rw [hindex] at hzero
    exact hrpos.ne' hzero
  have hrFin : r = ⟨0, by omega⟩ := Fin.ext hrZero
  rw [hrFin] at hrpos
  simpa using hrpos

/-- In the loop-boundary case of Lemma 4.4, the first three nonloop Toeplitz
columns have a positive triangular three-by-three minor. -/
theorem toeplitzMatrix_loopBoundary_threeMinor_pos
    {m n p : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hp : 1 ≤ p) (hbound : p + 2 < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hloop : IsLoop (toeplitzMatrix m n a) ⟨p - 1, by omega⟩)
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨p, by omega⟩) :
    0 < orderedMinor (toeplitzMatrix m n a) (topThreeRows m hm)
      (consecutiveThreeColumns p hbound) := by
  have hap := toeplitzMatrix_top_coefficient_pos_after_loop
    (by omega : 2 ≤ m) hp (by omega) hA hloop hnonloop
  have hzero₁ := isLoop_iff_entry_eq_zero.mp hloop (⟨0, by omega⟩ : Fin m)
  have hzero₂ := isLoop_iff_entry_eq_zero.mp hloop (⟨1, by omega⟩ : Fin m)
  rw [toeplitzMatrix_apply] at hzero₁ hzero₂
  have hzero₁' : a ((p : ℤ) - 1) = 0 := by
    change a (((p - 1 : ℕ) : ℤ) - 0) = 0 at hzero₁
    have hindex : ((p - 1 : ℕ) : ℤ) - 0 = (p : ℤ) - 1 := by omega
    rwa [hindex] at hzero₁
  have hzero₂' : a ((p : ℤ) - 2) = 0 := by
    change a (((p - 1 : ℕ) : ℤ) - 1) = 0 at hzero₂
    have hindex : ((p - 1 : ℕ) : ℤ) - 1 = (p : ℤ) - 2 := by omega
    rwa [hindex] at hzero₂
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    leftBoundaryTriple (a (p : ℤ))
      (a ((p : ℤ) + 1)) (a ((p : ℤ) + 2))
  have htwoOne : (p : ℤ) + 2 - 1 = (p : ℤ) + 1 := by ring
  have honeTwo : (p : ℤ) + 1 - 2 = (p : ℤ) - 1 := by ring
  have hmatrix :
      (toeplitzMatrix m n a).submatrix (topThreeRows m hm)
          (consecutiveThreeColumns p hbound) = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, leftBoundaryTriple, topThreeRows, consecutiveThreeColumns,
        toeplitzMatrix_apply,
        hzero₁', hzero₂', htwoOne, honeTwo]
  rw [orderedMinor, hmatrix]
  exact leftBoundaryTriple_det_pos hap

/-- Full-row-rank loop-boundary endpoint protection, without a separate
column-count hypothesis. -/
theorem toeplitzMatrix_initialLoops_endpointProtection
    {m n p : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hp : 1 ≤ p) (hpBound : p < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hloops : ∀ j : Fin n, j.val < p → IsLoop (toeplitzMatrix m n a) j)
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨p, hpBound⟩) :
    ∃ hbound : p + 2 < n,
      0 < orderedMinor (toeplitzMatrix m n a) (topThreeRows m hm)
        (consecutiveThreeColumns p hbound) := by
  have hbound := two_successors_of_fullRowRank_of_initial_loops
    hm hpBound hfull hloops
  refine ⟨hbound, ?_⟩
  have hpredLoop : IsLoop (toeplitzMatrix m n a) ⟨p - 1, by omega⟩ := by
    apply hloops
    change p - 1 < p
    omega
  exact toeplitzMatrix_loopBoundary_threeMinor_pos hm hp hbound hA hpredLoop hnonloop

/-! ## The nontrivial-initial-class case of endpoint protection -/

/-- A square matrix with one column equal to a scalar multiple of another
distinct column has zero determinant. -/
theorem Matrix.det_eq_zero_of_column_eq_smul
    {d : ℕ} {B : Matrix (Fin d) (Fin d) ℝ} {i j : Fin d}
    (hij : i ≠ j) {lambda : ℝ} (hcol : B.col j = lambda • B.col i) :
    B.det = 0 := by
  have hupdate : B.updateCol j (lambda • B.col i) = B := by
    ext r k
    by_cases hkj : k = j
    · subst k
      simpa [Matrix.updateCol, Matrix.col_apply] using (congrFun hcol r).symm
    · simp [Matrix.updateCol, hkj]
  rw [← hupdate, Matrix.det_updateCol_smul]
  have hzero : (B.updateCol j (B.col i)).det = 0 :=
    Matrix.det_updateCol_eq_zero (M := B) hij
  rw [hzero, mul_zero]

/-- Full row rank supplies two columns after a nontrivial initial parallel
block.  Otherwise a maximal minor would contain two parallel columns. -/
theorem two_successors_of_fullRowRank_of_initial_parallelBlock
    {m n L : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hm : 3 ≤ m) (hfull : HasFullRowRank A)
    (hblock : IsMaximalToeplitzParallelBlock A 0 L) :
    L + 1 < n := by
  by_contra hbound
  obtain ⟨cols, hcols⟩ := hfull
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let i₂ : Fin m := ⟨2, by omega⟩
  have h₀₁ : cols i₀ < cols i₁ :=
    cols.strictMono (Fin.mk_lt_mk.mpr (by omega))
  have h₁₂ : cols i₁ < cols i₂ :=
    cols.strictMono (Fin.mk_lt_mk.mpr (by omega))
  have hcolOne : (cols i₁).val < L := by
    by_contra hone
    have hlastBound := (cols i₂).isLt
    omega
  have hcolZero : (cols i₀).val < L := by omega
  let t₀ : Fin L := ⟨(cols i₀).val, hcolZero⟩
  let t₁ : Fin L := ⟨(cols i₁).val, hcolOne⟩
  have hfirst₀ := hblock.parallel t₀
  have hfirst₁ := hblock.parallel t₁
  have hparallel : ColumnsPositivelyParallel A
      (cols i₀) (cols i₁) := by
    have h₀bound : 0 + t₀.val < n := by
      simp [t₀, (cols i₀).isLt]
    have h₁bound : 0 + t₁.val < n := by
      simp [t₁, (cols i₁).isLt]
    have h₀ : (⟨0 + t₀, h₀bound⟩ : Fin n) = cols i₀ := by
      apply Fin.ext
      change 0 + (cols i₀).val = (cols i₀).val
      omega
    have h₁ : (⟨0 + t₁, h₁bound⟩ : Fin n) = cols i₁ := by
      apply Fin.ext
      change 0 + (cols i₁).val = (cols i₁).val
      omega
    rw [h₀] at hfirst₀
    rw [h₁] at hfirst₁
    exact columnsPositivelyParallel_trans
      (columnsPositivelyParallel_symm hfirst₀) hfirst₁
  obtain ⟨lambda, hlambda, hparallel⟩ := hparallel
  let B : Matrix (Fin m) (Fin m) ℝ := A.submatrix (allRows m) cols
  have hBcols : B.col i₁ = lambda • B.col i₀ := by
    funext r
    simpa [B, Matrix.col_apply] using congrFun hparallel (allRows m r)
  apply hcols
  change B.det = 0
  exact Matrix.det_eq_zero_of_column_eq_smul
    (by
      intro h
      have hv := congrArg Fin.val h
      change (0 : ℕ) = 1 at hv
      omega) hBcols

/-- In the second case of Lemma 4.4, the last column of a nontrivial initial
parallel class and the next two columns have a positive top-three-row minor.
This is formula (14) in arbitrary ambient row rank. -/
theorem toeplitzMatrix_initialParallel_threeMinor_pos
    {m n L : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hL : 2 ≤ L) (hbound : L + 1 < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hblock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n a) 0 L) :
    0 < orderedMinor (toeplitzMatrix m n a) (topThreeRows m hm)
      (consecutiveThreeColumns (L - 1) (by omega)) := by
  let z₀ : ℤ := -((m : ℤ) - 1)
  obtain ⟨lambda, hlambda, hgeom⟩ :=
    toeplitzMatrix_geometricSegment_of_parallelBlock
      (a := a) (m := m) (n := n) (p := 0) (L := L)
      (by omega) hL hblock.bound hblock.parallel
  let c : ℝ := a z₀
  have hgeomAt : ∀ (s : ℕ), s < m + L - 1 →
      a (z₀ + s) = c * lambda ^ s := by
    intro s hs
    simpa [z₀, c] using hgeom s hs
  have hcne : c ≠ 0 := by
    obtain ⟨r, hrpos⟩ := exists_entry_pos_of_not_isLoop hA
      (hblock.nonloop ⟨0, by omega⟩)
    rw [toeplitzMatrix_apply] at hrpos
    let s : ℕ := m - 1 - r.val
    have hs : s < m + L - 1 := by dsimp only [s]; omega
    have hindex : z₀ + s = -(r : ℤ) := by
      dsimp only [z₀, s]
      omega
    have h := hgeomAt s hs
    rw [hindex] at h
    intro hc
    rw [hc] at h
    simp only [zero_mul] at h
    exact hrpos.ne' (by simpa using h)
  have hcNonneg : 0 ≤ c := by
    let bottom : Fin m := ⟨m - 1, by omega⟩
    have hentry := hA.entry_nonneg bottom (⟨0, by omega⟩ : Fin n)
    rw [toeplitzMatrix_apply] at hentry
    have hindex : (0 : ℤ) - (bottom : ℤ) = z₀ := by
      dsimp only [bottom, z₀]
      omega
    change 0 ≤ a ((0 : ℤ) - (bottom : ℤ)) at hentry
    rwa [hindex] at hentry
  have hc : 0 < c := lt_of_le_of_ne hcNonneg (Ne.symm hcne)
  let E : ℕ := m + L - 2
  have hE : E < m + L - 1 := by dsimp only [E]; omega
  have hEOne : E - 1 < m + L - 1 := by omega
  have hETwo : E - 2 < m + L - 1 := by omega
  have hgeomE := hgeomAt E hE
  have hgeomEOne := hgeomAt (E - 1) hEOne
  have hgeomETwo := hgeomAt (E - 2) hETwo
  have hindexE : z₀ + E = (L : ℤ) - 1 := by
    dsimp only [z₀, E]
    omega
  have hindexEOne : z₀ + (E - 1) = (L : ℤ) - 2 := by
    dsimp only [z₀, E]
    omega
  have hindexETwo : z₀ + (E - 2) = (L : ℤ) - 3 := by
    dsimp only [z₀, E]
    omega
  have hcastEOne : ((E - 1 : ℕ) : ℤ) = (E : ℤ) - 1 := by
    dsimp only [E]
    omega
  have hcastETwo : ((E - 2 : ℕ) : ℤ) = (E : ℤ) - 2 := by
    dsimp only [E]
    omega
  rw [hindexE] at hgeomE
  rw [hcastEOne, hindexEOne] at hgeomEOne
  rw [hcastETwo, hindexETwo] at hgeomETwo
  let A0 : ℝ := a ((L : ℤ) - 1)
  have hA0eq : A0 = c * lambda ^ E := by simpa [A0] using hgeomE
  have hA0 : 0 < A0 := by rw [hA0eq]; exact mul_pos hc (pow_pos hlambda _)
  have hprev : 0 < a ((L : ℤ) - 2) := by
    rw [hgeomEOne]
    exact mul_pos hc (pow_pos hlambda _)
  let radius : ℝ := a ((L : ℤ) - 2) / A0
  let t : ℝ := a (L : ℤ) / A0
  let w : ℝ := a ((L : ℤ) + 1) / A0
  have hradius : a ((L : ℤ) - 2) = A0 * radius := by
    dsimp only [radius]
    field_simp
  have ht : a (L : ℤ) = A0 * t := by
    dsimp only [t]
    field_simp
  have hw : a ((L : ℤ) + 1) = A0 * w := by
    dsimp only [w]
    field_simp
  have hgeometricRelation :
      a ((L : ℤ) - 3) * A0 =
        a ((L : ℤ) - 2) * a ((L : ℤ) - 2) := by
    rw [hgeomETwo, hgeomEOne, hA0eq]
    have hEeq : E = (E - 2) + 2 := by dsimp only [E]; omega
    have hEOneEq : E - 1 = (E - 2) + 1 := by dsimp only [E]; omega
    have hpowE : lambda ^ E = lambda ^ (E - 2) * lambda ^ 2 := by
      calc
        lambda ^ E = lambda ^ ((E - 2) + 2) := congrArg (lambda ^ ·) hEeq
        _ = lambda ^ (E - 2) * lambda ^ 2 := pow_add _ _ _
    have hpowEOne : lambda ^ (E - 1) = lambda ^ (E - 2) * lambda := by
      calc
        lambda ^ (E - 1) = lambda ^ ((E - 2) + 1) :=
          congrArg (lambda ^ ·) hEOneEq
        _ = lambda ^ (E - 2) * lambda := by rw [pow_succ]
    rw [hpowE, hpowEOne]
    ring
  have hradiusTwo : a ((L : ℤ) - 3) = A0 * radius ^ 2 := by
    have hA0ne := hA0.ne'
    dsimp only [radius]
    field_simp
    nlinarith [hgeometricRelation]
  have hlog := toeplitzMatrix_displayedLogConcave
    (by omega : 2 ≤ m) (by omega : 2 ≤ n) (hA.tnUpTo 2)
  have hlogEnd := hlog ((L : ℤ) - 1) (by
    simp only [displayedLower]
    omega) (by
    simp only [displayedUpper]
    omega)
  have hlogEnd' :
      a ((L : ℤ) - 1) * a ((L : ℤ) - 1) ≥
        a ((L : ℤ) - 2) * a (L : ℤ) := by
    have hpred : (L : ℤ) - 1 - 1 = (L : ℤ) - 2 := by ring
    have hsucc : (L : ℤ) - 1 + 1 = (L : ℤ) := by ring
    rwa [hpred, hsucc] at hlogEnd
  have hrtLe : radius * t ≤ 1 := by
    apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hA0)
    calc
      A0 ^ 2 * (radius * t) = (A0 * radius) * (A0 * t) := by ring
      _ = a ((L : ℤ) - 2) * a (L : ℤ) := by rw [hradius, ht]
      _ ≤ a ((L : ℤ) - 1) * a ((L : ℤ) - 1) := hlogEnd'
      _ = A0 ^ 2 * 1 := by simp [A0, pow_two]
  have hA0Step : A0 = lambda * a ((L : ℤ) - 2) := by
    rw [hA0eq, hgeomEOne]
    have hEeq : E = (E - 1) + 1 := by dsimp only [E]; omega
    have hpowE : lambda ^ E = lambda ^ (E - 1) * lambda := by
      calc
        lambda ^ E = lambda ^ ((E - 1) + 1) := congrArg (lambda ^ ·) hEeq
        _ = lambda ^ (E - 1) * lambda := by rw [pow_succ]
    rw [hpowE]
    ring
  have hrtNe : radius * t ≠ 1 := by
    intro hrt
    have hproduct : a ((L : ℤ) - 2) * a (L : ℤ) = A0 ^ 2 := by
      calc
        a ((L : ℤ) - 2) * a (L : ℤ) =
            (A0 * radius) * (A0 * t) := by rw [← hradius, ← ht]
        _ = A0 ^ 2 * (radius * t) := by ring
        _ = A0 ^ 2 * 1 := by rw [hrt]
        _ = A0 ^ 2 := by ring
    have htopExtension : a (L : ℤ) = lambda * A0 := by
      nlinarith [hproduct, hA0Step, hprev]
    apply hblock.right_maximal (by omega)
    refine ⟨lambda, hlambda, ?_⟩
    funext r
    simp only [Matrix.col_apply, toeplitzMatrix_apply, Pi.smul_apply, smul_eq_mul]
    simp only [zero_add]
    change a ((L : ℤ) - (r : ℤ)) =
      lambda * a (((L - 1 : ℕ) : ℤ) - (r : ℤ))
    by_cases hr : r.val = 0
    · have hrFin : r = ⟨0, by omega⟩ := Fin.ext hr
      rw [hrFin]
      have hLPredCast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
      simpa [hLPredCast, A0] using htopExtension
    · let s : ℕ := E - r.val
      have hs : s < m + L - 1 := by dsimp only [s, E]; omega
      have hsSucc : s + 1 < m + L - 1 := by dsimp only [s, E]; omega
      have hsEq : s + r.val = E := by dsimp only [s, E]; omega
      have hsEqInt := congrArg (fun q : ℕ ↦ (q : ℤ)) hsEq
      push_cast at hsEqInt
      have hEcast : (E : ℤ) = (m : ℤ) + L - 2 := by
        dsimp only [E]
        omega
      rw [hEcast] at hsEqInt
      have hlastIndex : (((L - 1 : ℕ) : ℤ) - (r : ℤ)) = z₀ + s := by
        have hLPredCast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
        rw [hLPredCast]
        dsimp only [z₀]
        omega
      have hrightIndex : (L : ℤ) - (r : ℤ) = z₀ + (s + 1) := by
        dsimp only [z₀]
        omega
      have hsSuccCast : ((s + 1 : ℕ) : ℤ) = (s : ℤ) + 1 := by omega
      rw [hlastIndex, hrightIndex, ← hsSuccCast,
        hgeomAt s hs, hgeomAt (s + 1) hsSucc, pow_succ]
      ring
  have hrt : radius * t < 1 := lt_of_le_of_ne hrtLe hrtNe
  have hmatrix :
      (toeplitzMatrix m n a).submatrix (topThreeRows m hm)
          (consecutiveThreeColumns (L - 1) (by omega)) =
        endpointProtectionMatrix A0 radius t w := by
    have hLPredCast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
    have hLMinusTwo : (L : ℤ) - 1 - 1 = (L : ℤ) - 2 := by ring
    have hLMinusThree : (L : ℤ) - 1 - 2 = (L : ℤ) - 3 := by ring
    have hstartPlusTwo : (L : ℤ) - 1 + 2 = (L : ℤ) + 1 := by ring
    have hLPlusOneTwo : (L : ℤ) + 1 - 2 = (L : ℤ) - 1 := by ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [topThreeRows, consecutiveThreeColumns, endpointProtectionMatrix,
        toeplitzMatrix_apply, A0, hLPredCast, hLMinusTwo, hLMinusThree,
        hstartPlusTwo, hLPlusOneTwo,
        hradius, hradiusTwo, ht, hw]
  rw [orderedMinor, hmatrix]
  exact endpointProtectionMatrix_det_pos hA0 hrt

/-- Full-row-rank form of the nontrivial-initial-class endpoint protection
calculation. -/
theorem toeplitzMatrix_initialParallel_endpointProtection
    {m n L : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hblock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n a) 0 L) :
    ∃ htripleBound : (L - 1) + 2 < n,
      0 < orderedMinor (toeplitzMatrix m n a) (topThreeRows m hm)
        (consecutiveThreeColumns (L - 1) htripleBound) := by
  have hbound := two_successors_of_fullRowRank_of_initial_parallelBlock
    hm hfull hblock
  have htripleBound : (L - 1) + 2 < n := by
    have hL := hblock.two_le
    omega
  refine ⟨htripleBound, ?_⟩
  simpa only using toeplitzMatrix_initialParallel_threeMinor_pos
    hm hblock.two_le hbound hA hblock

/-- Right-hand coefficient calculation in Lemma 4.4, obtained by reversing
both axes and applying the checked initial-parallel calculation.  The reversed
row and column embeddings are the bottom three rows and the final three
simplified representatives in the original order. -/
theorem toeplitzMatrix_terminalParallel_endpointProtection
    {m n p L : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hend : p + L = n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hblock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n a) p L) :
    ∃ htripleBound : (L - 1) + 2 < n,
      0 < orderedMinor (toeplitzMatrix m n a)
        (reverseOrderEmbedding (topThreeRows m hm))
        (reverseOrderEmbedding
          (consecutiveThreeColumns (L - 1) htripleBound)) := by
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let arev : ℤ → ℝ := reverseCoefficients m n a
  have hmatrix : reverseMatrix A = toeplitzMatrix m n arev := by
    simpa [A, arev, reverseMatrix] using toeplitzMatrix_submatrix_rev
      (r := m) (n := n) a
  have hrevTN : TotallyNonnegative (toeplitzMatrix m n arev) := by
    rw [← hmatrix]
    exact hA.reverseMatrix
  have hrevFull : HasFullRowRank (toeplitzMatrix m n arev) := by
    rw [← hmatrix]
    exact (hasFullRowRank_reverseMatrix_iff A).2 hfull
  have hrevBlockMatrix : IsMaximalToeplitzParallelBlock (reverseMatrix A) 0 L := by
    have hL : 2 ≤ L := hblock.two_le
    refine ⟨hL, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · intro t
      let s : Fin L := ⟨L - 1 - t.val, by omega⟩
      let jt : Fin n := ⟨0 + t.val, by omega⟩
      change ¬IsLoop (reverseMatrix A) jt
      have hindex : jt.rev = (⟨p + s.val, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_rev]
        dsimp only [jt, s]
        omega
      rw [isLoop_reverseMatrix_iff, hindex]
      exact hblock.nonloop s
    · intro t
      let s : Fin L := ⟨L - 1 - t.val, by omega⟩
      let lastIndex : Fin L := ⟨L - 1, by omega⟩
      let jfirst : Fin n := ⟨0, by omega⟩
      let jt : Fin n := ⟨0 + t.val, by omega⟩
      change ColumnsPositivelyParallel (reverseMatrix A) jfirst jt
      have hfirstRev : jfirst.rev =
          ⟨p + lastIndex.val, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_rev]
        dsimp only [jfirst, lastIndex]
        omega
      have htRev : jt.rev = (⟨p + s.val, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_rev]
        dsimp only [jt, s]
        omega
      apply (columnsPositivelyParallel_reverseMatrix_iff A jfirst jt).2
      rw [hfirstRev, htRev]
      exact columnsPositivelyParallel_trans
        (columnsPositivelyParallel_symm (hblock.parallel lastIndex))
        (hblock.parallel s)
    · intro hp
      omega
    · intro hright hparallel
      have hp : 1 ≤ p := by omega
      let jlast : Fin n := ⟨0 + L - 1, by omega⟩
      let jright : Fin n := ⟨0 + L, hright⟩
      change ColumnsPositivelyParallel (reverseMatrix A) jlast jright at hparallel
      have horiginal :=
        (columnsPositivelyParallel_reverseMatrix_iff A jlast jright).1 hparallel
      have hlastRev : jlast.rev =
          (⟨p, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_rev]
        dsimp only [jlast]
        omega
      have hrightRev : jright.rev =
          (⟨p - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        simp only [Fin.val_rev]
        dsimp only [jright]
        omega
      rw [hlastRev, hrightRev] at horiginal
      exact hblock.left_maximal hp
        (columnsPositivelyParallel_symm horiginal)
  have hrevBlock : IsMaximalToeplitzParallelBlock
      (toeplitzMatrix m n arev) 0 L := by
    rwa [← hmatrix]
  obtain ⟨htripleBound, hminor⟩ :=
    toeplitzMatrix_initialParallel_endpointProtection
      hm hrevTN hrevFull hrevBlock
  refine ⟨htripleBound, ?_⟩
  rw [← hmatrix] at hminor
  rw [orderedMinor_reverseMatrix] at hminor
  exact hminor

/-- Right loop-boundary case of Lemma 4.4, obtained from the checked left
loop-boundary calculation by simultaneous reversal. -/
theorem toeplitzMatrix_terminalLoops_endpointProtection
    {m n q : ℕ} {a : ℤ → ℝ}
    (hm : 3 ≤ m) (hq : q + 1 < n)
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hloops : ∀ j : Fin n, q < j.val → IsLoop (toeplitzMatrix m n a) j)
    (hnonloop : ¬IsLoop (toeplitzMatrix m n a) ⟨q, by omega⟩) :
    let pRev := n - 1 - q
    ∃ hbound : pRev + 2 < n,
      0 < orderedMinor (toeplitzMatrix m n a)
        (reverseOrderEmbedding (topThreeRows m hm))
        (reverseOrderEmbedding (consecutiveThreeColumns pRev hbound)) := by
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let arev : ℤ → ℝ := reverseCoefficients m n a
  let pRev : ℕ := n - 1 - q
  have hpRev : 1 ≤ pRev := by dsimp only [pRev]; omega
  have hpRevBound : pRev < n := by dsimp only [pRev]; omega
  have hmatrix : reverseMatrix A = toeplitzMatrix m n arev := by
    simpa [A, arev, reverseMatrix] using toeplitzMatrix_submatrix_rev
      (r := m) (n := n) a
  have hrevTN : TotallyNonnegative (toeplitzMatrix m n arev) := by
    rw [← hmatrix]
    exact hA.reverseMatrix
  have hrevFull : HasFullRowRank (toeplitzMatrix m n arev) := by
    rw [← hmatrix]
    exact (hasFullRowRank_reverseMatrix_iff A).2 hfull
  have hrevLoops : ∀ j : Fin n, j.val < pRev →
      IsLoop (toeplitzMatrix m n arev) j := by
    intro j hj
    rw [← hmatrix, isLoop_reverseMatrix_iff]
    apply hloops
    have hjrevRaw := Fin.val_rev j
    have hjrev : j.rev.val = n - 1 - j.val := by omega
    omega
  let jp : Fin n := ⟨pRev, hpRevBound⟩
  have hjpRev : jp.rev = (⟨q, by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp only [jp, pRev]
    omega
  have hrevNonloop : ¬IsLoop (toeplitzMatrix m n arev) jp := by
    rw [← hmatrix, isLoop_reverseMatrix_iff, hjpRev]
    exact hnonloop
  obtain ⟨hbound, hminor⟩ := toeplitzMatrix_initialLoops_endpointProtection
    hm hpRev hpRevBound hrevTN hrevFull hrevLoops hrevNonloop
  refine ⟨hbound, ?_⟩
  rw [← hmatrix] at hminor
  rw [orderedMinor_reverseMatrix] at hminor
  exact hminor

/-! ## Matroid-level endpoint protection -/

/-- A nonzero square minor on selected rows proves independence of the
corresponding columns in the original ambient row space. -/
theorem linearIndependent_columns_of_orderedMinor_ne_zero
    {s m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (rows : Fin s ↪o Fin m) (cols : Fin s ↪o Fin n)
    (hminor : orderedMinor A rows cols ≠ 0) :
    LinearIndependent ℝ (fun j : Fin s ↦ A.col (cols j)) := by
  let C : Matrix (Fin s) (Fin n) ℝ := A.submatrix rows id
  have hCminor : orderedMinor C (allRows s) cols ≠ 0 := by
    change (A.submatrix rows cols).det ≠ 0
    simpa [C, allRows, Matrix.submatrix_submatrix] using hminor
  have hCind : LinearIndependent ℝ (fun j : Fin s ↦ C.col (cols j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns C cols).mp hCminor
  let restrictRows : (Fin m → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    LinearMap.pi fun i ↦ LinearMap.proj (rows i)
  apply LinearIndependent.of_comp restrictRows
  have hfamily :
      (restrictRows ∘ fun j : Fin s ↦ A.col (cols j)) =
        fun j : Fin s ↦ C.col (cols j) := by
    funext j i
    rfl
  rw [hfamily]
  exact hCind

/-- The matroid statement underlying Lemma 4.4: in a totally nonnegative
configuration with no dependent pair, independence of the first three
columns prevents the first element from lying in a rank-two flat containing
at least three elements. -/
theorem first_not_mem_large_rankTwo_flat
    {m n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hpairs : ∀ cols : Fin 2 ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin 2 ↦ A.col (cols j)))
    (hfirst : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (consecutiveThreeColumns 0 (by omega) j)))
    {F : Set (Fin n)}
    (hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid A) F) :
    (⟨0, by omega⟩ : Fin n) ∉ F := by
  let P : Matrix (Fin 3) (Fin m) ℝ := threeRowPositiveCompression m
  have hP : TotallyPositive P := threeRowPositiveCompression_totallyPositive m
  let J : Fin 3 ↪o Fin n := consecutiveThreeColumns 0 (by omega)
  have hJind : LinearIndependent ℝ (fun j : Fin 3 ↦ A.col (J j)) := by
    simpa [J] using hfirst
  have hrank : ∃ K : Fin 3 ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin 3 ↦ A.col (K j)) := ⟨J, hJind⟩
  obtain ⟨D⟩ := exists_firstCircuitIntervalData
    (p := 1) (by omega : 2 < n) hA hP hpairs hrank
  obtain ⟨run, hFrun⟩ :=
    (isLargeFirstCircuitFlat_iff_runHyperplane hpairs D F).1 hF
  rw [hFrun]
  rintro hzero
  have hleftZero : (D.runs.left run).val = 0 := by
    change (⟨0, by omega⟩ : Fin n) ∈
      Finset.Icc (runLeftColumn D.runs run)
        (runRightColumn (by omega : 2 < n) D.runs run) at hzero
    have hleft := (Finset.mem_Icc.mp hzero).1
    change (D.runs.left run).val ≤ 0 at hleft
    omega
  have hrightTwo : 2 ≤ (D.runs.right run).val + 2 := by
    omega
  have hJrun : ∀ i, J i ∈ runHyperplane (by omega : 2 < n) D.runs run := by
    intro i
    change J i ∈ Finset.Icc (runLeftColumn D.runs run)
      (runRightColumn (by omega : 2 < n) D.runs run)
    apply Finset.mem_Icc.mpr
    have hJval : (J i).val = i.val := by
      fin_cases i <;> rfl
    constructor
    · apply Fin.mk_le_mk.mpr
      change (D.runs.left run).val ≤ (J i).val
      omega
    · apply Fin.mk_le_mk.mpr
      change (J i).val ≤ (D.runs.right run).val + 2
      have hi := i.isLt
      omega
  have hJdep : ¬(columnMatroid A).Indep (Set.range J) :=
    (D.dependent_iff_interval J).2 ⟨run, hJrun⟩
  apply hJdep
  rw [columnMatroid_indep_range_iff]
  exact hJind

/-- Endpoint protection for an explicitly supplied simplification embedding.
The hypothesis on pairs says exactly that one representative was retained
from each nonloop parallel class. -/
theorem first_simplified_not_mem_large_rankTwo_flat
    {m n s : ℕ} (hs : 3 ≤ s) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (sigma : Fin s ↪o Fin n)
    (hsimple : ∀ cols : Fin 2 ↪o Fin s,
      LinearIndependent ℝ
        (fun j : Fin 2 ↦ (A.submatrix (allRows m) sigma).col (cols j)))
    (rows : Fin 3 ↪o Fin m)
    (hminor : orderedMinor A rows
      ((consecutiveThreeColumns 0 (by omega)).trans sigma) ≠ 0)
    {F : Set (Fin s)}
    (hF : IsLargeFirstCircuitFlat (p := 1)
      (columnMatroid (A.submatrix (allRows m) sigma)) F) :
    (⟨0, by omega⟩ : Fin s) ∉ F := by
  let B : Matrix (Fin m) (Fin s) ℝ := A.submatrix (allRows m) sigma
  have hB : TotallyNonnegative B := hA.submatrix (allRows m) sigma
  have hfirstA : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (((consecutiveThreeColumns 0 (by omega)).trans sigma) j)) :=
    linearIndependent_columns_of_orderedMinor_ne_zero
      rows ((consecutiveThreeColumns 0 (by omega)).trans sigma) hminor
  have hfirstB : LinearIndependent ℝ
      (fun j : Fin 3 ↦ B.col (consecutiveThreeColumns 0 (by omega) j)) := by
    simpa [B, Matrix.col_apply, allRows] using hfirstA
  exact first_not_mem_large_rankTwo_flat hs hB (by simpa [B] using hsimple)
    hfirstB hF

/-- The increasing embedding selecting the final three columns. -/
def lastThreeColumns (n : ℕ) (hn : 3 ≤ n) : Fin 3 ↪o Fin n :=
  selectedTripleEmbedding ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩
    ⟨n - 1, by omega⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- Right-hand matroid form of Lemma 4.4.  Independence of the final three
columns excludes the last element from every large rank-two flat. -/
theorem last_not_mem_large_rankTwo_flat
    {m n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hpairs : ∀ cols : Fin 2 ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin 2 ↦ A.col (cols j)))
    (hlast : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (lastThreeColumns n hn j)))
    {F : Set (Fin n)}
    (hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid A) F) :
    (⟨n - 1, by omega⟩ : Fin n) ∉ F := by
  let P : Matrix (Fin 3) (Fin m) ℝ := threeRowPositiveCompression m
  have hP : TotallyPositive P := threeRowPositiveCompression_totallyPositive m
  let J : Fin 3 ↪o Fin n := lastThreeColumns n hn
  have hJind : LinearIndependent ℝ (fun j : Fin 3 ↦ A.col (J j)) := by
    simpa [J] using hlast
  have hrank : ∃ K : Fin 3 ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin 3 ↦ A.col (K j)) := ⟨J, hJind⟩
  obtain ⟨D⟩ := exists_firstCircuitIntervalData
    (p := 1) (by omega : 2 < n) hA hP hpairs hrank
  obtain ⟨run, hFrun⟩ :=
    (isLargeFirstCircuitFlat_iff_runHyperplane hpairs D F).1 hF
  rw [hFrun]
  rintro hlastMem
  have hrightLast : (D.runs.right run).val + 2 = n - 1 := by
    change (⟨n - 1, by omega⟩ : Fin n) ∈
      Finset.Icc (runLeftColumn D.runs run)
        (runRightColumn (by omega : 2 < n) D.runs run) at hlastMem
    have hright := (Finset.mem_Icc.mp hlastMem).2
    change n - 1 ≤ (D.runs.right run).val + 2 at hright
    have hbound := (D.runs.right run).isLt
    omega
  have hleftBound : (D.runs.left run).val ≤ n - 3 := by
    have hlr := Fin.le_iff_val_le_val.mp (D.runs.left_le_right run)
    omega
  have hJrun : ∀ i, J i ∈ runHyperplane (by omega : 2 < n) D.runs run := by
    intro i
    change J i ∈ Finset.Icc (runLeftColumn D.runs run)
      (runRightColumn (by omega : 2 < n) D.runs run)
    apply Finset.mem_Icc.mpr
    have hJval : (J i).val = n - 3 + i.val := by
      fin_cases i <;> simp [J, lastThreeColumns] <;> omega
    constructor
    · apply Fin.mk_le_mk.mpr
      change (D.runs.left run).val ≤ (J i).val
      omega
    · apply Fin.mk_le_mk.mpr
      change (J i).val ≤ (D.runs.right run).val + 2
      have hi := i.isLt
      omega
  have hJdep : ¬(columnMatroid A).Indep (Set.range J) :=
    (D.dependent_iff_interval J).2 ⟨run, hJrun⟩
  apply hJdep
  rw [columnMatroid_indep_range_iff]
  exact hJind

/-- Right endpoint protection for an explicitly supplied simplification
embedding. -/
theorem last_simplified_not_mem_large_rankTwo_flat
    {m n s : ℕ} (hs : 3 ≤ s) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (sigma : Fin s ↪o Fin n)
    (hsimple : ∀ cols : Fin 2 ↪o Fin s,
      LinearIndependent ℝ
        (fun j : Fin 2 ↦ (A.submatrix (allRows m) sigma).col (cols j)))
    (rows : Fin 3 ↪o Fin m)
    (hminor : orderedMinor A rows ((lastThreeColumns s hs).trans sigma) ≠ 0)
    {F : Set (Fin s)}
    (hF : IsLargeFirstCircuitFlat (p := 1)
      (columnMatroid (A.submatrix (allRows m) sigma)) F) :
    (⟨s - 1, by omega⟩ : Fin s) ∉ F := by
  let B : Matrix (Fin m) (Fin s) ℝ := A.submatrix (allRows m) sigma
  have hB : TotallyNonnegative B := hA.submatrix (allRows m) sigma
  have hlastA : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (((lastThreeColumns s hs).trans sigma) j)) :=
    linearIndependent_columns_of_orderedMinor_ne_zero
      rows ((lastThreeColumns s hs).trans sigma) hminor
  have hlastB : LinearIndependent ℝ
      (fun j : Fin 3 ↦ B.col (lastThreeColumns s hs j)) := by
    simpa [B, Matrix.col_apply, allRows] using hlastA
  exact last_not_mem_large_rankTwo_flat hs hB (by simpa [B] using hsimple)
    hlastB hF

/-! ## Rank-three realization assembly -/

/-! ### Generic projective coordinates for two-row compressions -/

/-- The projective coordinate `lower / upper`, with a zero upper entry
represented by `∞`, for an arbitrary two-row matrix. -/
def twoRowProjectiveParameterWithTop
    {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℝ) (j : Fin n) : WithTop ℝ :=
  if B 0 j = 0 then ⊤ else (B 1 j / B 0 j : ℝ)

/-- On nonloop columns of a totally nonnegative two-row matrix, the extended
projective coordinate is weakly increasing. -/
theorem twoRowProjectiveParameterWithTop_mono
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ}
    (hB : TotallyNonnegative B)
    {i j : Fin n} (hij : i ≤ j) (hi : ¬IsLoop B i) (hj : ¬IsLoop B j) :
    twoRowProjectiveParameterWithTop B i ≤
      twoRowProjectiveParameterWithTop B j := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  have hminor := orderedPairMinor_nonneg_of_totallyNonnegative hB hij
  by_cases hiu : B 0 i = 0
  · have hilne : B 1 i ≠ 0 := by
      intro hil
      apply hi
      rw [isLoop_iff_entry_eq_zero]
      intro r
      fin_cases r
      · exact hiu
      · exact hil
    have hilpos : 0 < B 1 i :=
      lt_of_le_of_ne (hB.entry_nonneg 1 i) (Ne.symm hilne)
    have hju : B 0 j = 0 := by
      unfold orderedPairMinor at hminor
      rw [hiu, zero_mul, zero_sub] at hminor
      have hprodNonneg : 0 ≤ B 0 j * B 1 i :=
        mul_nonneg (hB.entry_nonneg 0 j) hilpos.le
      have hprod : B 0 j * B 1 i = 0 := by linarith
      exact (mul_eq_zero.mp hprod).resolve_right hilpos.ne'
    simp [twoRowProjectiveParameterWithTop, hiu, hju]
  · by_cases hju : B 0 j = 0
    · simp [twoRowProjectiveParameterWithTop, hiu, hju]
    · have hiupos : 0 < B 0 i :=
        lt_of_le_of_ne (hB.entry_nonneg 0 i) (Ne.symm hiu)
      have hjupos : 0 < B 0 j :=
        lt_of_le_of_ne (hB.entry_nonneg 0 j) (Ne.symm hju)
      have hquot : B 1 i / B 0 i ≤ B 1 j / B 0 j := by
        apply (div_le_div_iff₀ hiupos hjupos).2
        unfold orderedPairMinor at hminor
        linarith
      simpa [twoRowProjectiveParameterWithTop, hiu, hju] using hquot

/-- Equality of projective coordinates is equivalent to positive
parallelism on nonloop columns. -/
theorem twoRowProjectiveParameterWithTop_eq_iff_parallel
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ}
    (hB : TotallyNonnegative B) {i j : Fin n}
    (hi : ¬IsLoop B i) (hj : ¬IsLoop B j) :
    twoRowProjectiveParameterWithTop B i =
        twoRowProjectiveParameterWithTop B j ↔
      ColumnsPositivelyParallel B i j := by
  have hentry : ∀ r k, 0 ≤ B r k := fun r k ↦ hB.entry_nonneg r k
  have hparamMinor :
      twoRowProjectiveParameterWithTop B i =
          twoRowProjectiveParameterWithTop B j ↔
        orderedPairMinor B i j = 0 := by
    constructor
    · intro hq
      by_cases hiu : B 0 i = 0
      · have hju : B 0 j = 0 := by
          by_contra hju
          simp [twoRowProjectiveParameterWithTop, hiu, hju] at hq
        simp [orderedPairMinor, hiu, hju]
      · have hju : B 0 j ≠ 0 := by
          intro hju
          simp [twoRowProjectiveParameterWithTop, hiu, hju] at hq
        have hreal : B 1 i / B 0 i = B 1 j / B 0 j := by
          simpa [twoRowProjectiveParameterWithTop, hiu, hju] using hq
        unfold orderedPairMinor
        rw [sub_eq_zero]
        field_simp [hiu, hju] at hreal
        simpa [mul_comm] using hreal.symm
    · intro hminor
      by_cases hiu : B 0 i = 0
      · have hilne : B 1 i ≠ 0 := by
          intro hil
          apply hi
          rw [isLoop_iff_entry_eq_zero]
          intro r
          fin_cases r
          · exact hiu
          · exact hil
        have hju : B 0 j = 0 := by
          unfold orderedPairMinor at hminor
          rw [hiu, zero_mul, zero_sub, neg_eq_zero] at hminor
          exact (mul_eq_zero.mp hminor).resolve_right hilne
        simp [twoRowProjectiveParameterWithTop, hiu, hju]
      · have hju : B 0 j ≠ 0 := by
          intro hju
          have hjlne : B 1 j ≠ 0 := by
            intro hjl
            apply hj
            rw [isLoop_iff_entry_eq_zero]
            intro r
            fin_cases r
            · exact hju
            · exact hjl
          unfold orderedPairMinor at hminor
          rw [hju, zero_mul, sub_zero] at hminor
          exact hjlne ((mul_eq_zero.mp hminor).resolve_left hiu)
        have hreal : B 1 i / B 0 i = B 1 j / B 0 j := by
          unfold orderedPairMinor at hminor
          rw [sub_eq_zero] at hminor
          field_simp [hiu, hju]
          simpa [mul_comm] using hminor.symm
        simpa [twoRowProjectiveParameterWithTop, hiu, hju] using hreal
  rw [hparamMinor]
  constructor
  · exact columnsPositivelyParallel_of_orderedPairMinor_eq_zero hentry hi hj
  · rintro ⟨c, hc, hcol⟩
    exact orderedPairMinor_eq_zero_of_column_eq_smul _ _ _ c hcol

/-- Canonical rank-two datum extracted from a two-row TNN matrix once its
nonloop interval endpoints are supplied. -/
noncomputable def rankTwoMatroidDatumOfMatrix
    {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℝ)
    (hB : TotallyNonnegative B) (first last : Fin n) (hfl : first ≤ last)
    (hactive : ∀ j, ¬IsLoop B j ↔ first ≤ j ∧ j ≤ last) :
    RankTwoMatroidDatum n where
  first := first
  last := last
  first_le_last := hfl
  parameter j := twoRowProjectiveParameterWithTop B j
  parameter_mono := by
    intro i j hij
    apply twoRowProjectiveParameterWithTop_mono hB
    · exact hij
    · exact (hactive i).2 i.property
    · exact (hactive j).2 j.property

/-- Intrinsic compatible rank-two support follows from a nonloop interval,
monotone TNN projective coordinates, and the two loop-boundary singleton
conditions. -/
theorem hasCompatibleRankTwoSupport_of_interval_certificate
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ}
    (hB : TotallyNonnegative B) (hfull : HasFullRowRank B)
    (first last : Fin n) (hfl : first ≤ last)
    (hactive : ∀ j, ¬IsLoop B j ↔ first ≤ j ∧ j ≤ last)
    (hleft : 0 < first.val → ∀ j,
      first ≤ j → j ≤ last →
      ColumnsPositivelyParallel B first j → j = first)
    (hright : last.val + 1 < n → ∀ j,
      first ≤ j → j ≤ last →
      ColumnsPositivelyParallel B last j → j = last) :
    HasCompatibleRankTwoSupport (columnMatroid B) := by
  let D : RankTwoMatroidDatum n :=
    rankTwoMatroidDatumOfMatrix B hB first last hfl hactive
  have hD : D.Compatible := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨i, j, hij, hi, hj, hnonparallel⟩ :=
        hasFullRowRank_exists_nonparallel_columns hfull
      let ii : D.Active := ⟨i, (hactive i).1 hi⟩
      let jj : D.Active := ⟨j, (hactive j).1 hj⟩
      refine ⟨ii, jj, ?_⟩
      intro heq
      apply hnonparallel
      exact (twoRowProjectiveParameterWithTop_eq_iff_parallel hB hi hj).1 heq
    · intro hfirst j hparam
      apply Subtype.ext
      apply hleft hfirst j.val j.property.1 j.property.2
      exact (twoRowProjectiveParameterWithTop_eq_iff_parallel hB
        ((hactive first).2 ⟨le_rfl, hfl⟩)
        ((hactive j).2 j.property)).1 hparam.symm
    · intro hlast j hparam
      apply Subtype.ext
      apply hright hlast j.val j.property.1 j.property.2
      exact (twoRowProjectiveParameterWithTop_eq_iff_parallel hB
        ((hactive last).2 ⟨hfl, le_rfl⟩)
        ((hactive j).2 j.property)).1 hparam.symm
  refine ⟨D, hD, ?_⟩
  refine ⟨columnMatroid_ground B, ?_⟩
  intro cols
  rw [columnMatroid_isBase_range_iff]
  constructor
  · intro hminor
    have hi : ¬IsLoop B (cols 0) := by
      intro hloop
      apply hminor
      rw [orderedMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro r
      exact isLoop_iff_entry_eq_zero.mp hloop (allRows 2 r)
    have hj : ¬IsLoop B (cols 1) := by
      intro hloop
      apply hminor
      rw [orderedMinor]
      apply Matrix.det_eq_zero_of_column_eq_zero 1
      intro r
      exact isLoop_iff_entry_eq_zero.mp hloop (allRows 2 r)
    refine ⟨(hactive _).1 hi, (hactive _).1 hj, ?_⟩
    intro hparam
    have hparallel := (twoRowProjectiveParameterWithTop_eq_iff_parallel
      hB hi hj).1 hparam
    obtain ⟨c, hc, hcol⟩ := hparallel
    apply hminor
    rw [orderEmbedding_fin_self_eq_allRows (allRows 2), orderedMinor_two]
    exact orderedPairMinor_eq_zero_of_column_eq_smul B (cols 0) (cols 1) c hcol
  · rintro ⟨hiActive, hjActive, hparam⟩
    have hi : ¬IsLoop B (cols 0) := (hactive _).2 hiActive
    have hj : ¬IsLoop B (cols 1) := (hactive _).2 hjActive
    intro hminor
    have hpairZero : orderedPairMinor B (cols 0) (cols 1) = 0 := by
      rw [orderEmbedding_fin_self_eq_allRows (allRows 2), orderedMinor_two] at hminor
      exact hminor
    have hparallel := columnsPositivelyParallel_of_orderedPairMinor_eq_zero
      (fun r j ↦ hB.entry_nonneg r j) hi hj hpairZero
    exact hparam ((twoRowProjectiveParameterWithTop_eq_iff_parallel
      hB hi hj).2 hparallel)

/-- Every one-row matrix is an integer-indexed Toeplitz section. -/
def oneRowToeplitzCoefficient
    {n : ℕ} (B : Matrix (Fin 1) (Fin n) ℝ) (z : ℤ) : ℝ :=
  if h : 0 ≤ z ∧ z < n then B 0 ⟨z.toNat, by omega⟩ else 0

theorem toeplitzMatrix_one_oneRowToeplitzCoefficient
    {n : ℕ} (B : Matrix (Fin 1) (Fin n) ℝ) :
    toeplitzMatrix 1 n (oneRowToeplitzCoefficient B) = B := by
  ext i j
  fin_cases i
  rw [toeplitzMatrix_apply, oneRowToeplitzCoefficient, dif_pos]
  · congr 2
  · omega

/-- The `k=1` case of Theorem 4.5.  Positive compression realizes the
rank-one truncation, and every one-row representative is automatically
Toeplitz. -/
theorem oneSkeleton_toeplitzRealization
    {m n : ℕ} (hm : 0 < m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hfull : HasFullRowRank A) :
    ∃ b : ℤ → ℝ,
      TotallyNonnegative (toeplitzMatrix 1 n b) ∧
        HasFullRowRank (toeplitzMatrix 1 n b) ∧
        IsRankTruncationOf 1 (columnMatroid (toeplitzMatrix 1 n b))
          (columnMatroid A) := by
  let P : Matrix (Fin 1) (Fin m) ℝ := oneRowPositiveCompression m
  let B : Matrix (Fin 1) (Fin n) ℝ := P * A
  let b : ℤ → ℝ := oneRowToeplitzCoefficient B
  have hP : TotallyPositive P := oneRowPositiveCompression_totallyPositive m
  have hB : TotallyNonnegative B := totallyNonnegative_mul hP.totallyNonnegative hA
  have hmatrix : toeplitzMatrix 1 n b = B := by
    exact toeplitzMatrix_one_oneRowToeplitzCoefficient B
  obtain ⟨basis, hbasis⟩ := hfull
  let j : Fin n := basis ⟨0, hm⟩
  have hj : ¬IsLoop A j := by
    intro hj
    apply hbasis
    rw [orderedMinor]
    apply Matrix.det_eq_zero_of_column_eq_zero ⟨0, hm⟩
    intro i
    exact isLoop_iff_entry_eq_zero.mp hj (allRows m i)
  let selected : Fin 1 ↪o Fin n := singletonOrderEmbedding j
  have hAone : LinearIndependent ℝ (fun t : Fin 1 ↦ A.col (selected t)) := by
    rw [linearIndependent_unique_iff]
    exact hj
  have hBone : LinearIndependent ℝ (fun t : Fin 1 ↦ B.col (selected t)) :=
    positiveCompression_preserves_ordered_independence le_rfl hP hA selected hAone
  have hBfull : HasFullRowRank B := by
    refine ⟨selected, ?_⟩
    rw [orderedMinor_one]
    have hcolne : B.col (selected 0) ≠ 0 := by
      simpa [linearIndependent_unique_iff] using hBone
    intro hzero
    apply hcolne
    funext i
    fin_cases i
    simpa using hzero
  refine ⟨b, ?_, ?_, ?_⟩
  · rwa [hmatrix]
  · rwa [hmatrix]
  · rw [hmatrix]
    exact positiveCompression_isRankTruncation hP hA

/-- The realization-theoretic final step for `k=2` in Theorem 4.5. -/
theorem twoSkeleton_toeplitzRealization_of_compatibleSupport
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hcompatible : HasCompatibleRankTwoSupport
      (columnMatroid (twoRowPositiveCompression m * A))) :
    ∃ b : Fin (n + 1) → ℝ,
      TotallyNonnegative (rankTwoToeplitz b) ∧
        HasFullRowRank (rankTwoToeplitz b) ∧
        IsRankTruncationOf 2 (columnMatroid (rankTwoToeplitz b))
          (columnMatroid A) := by
  obtain ⟨b, hTN, hfull, hmatroid⟩ :=
    hasTNNRankTwoToeplitzRepresentation_iff_hasCompatibleRankTwoSupport.mpr
      hcompatible
  refine ⟨b, hTN, hfull, ?_⟩
  rw [hmatroid]
  exact positiveCompression_isRankTruncation
    (twoRowPositiveCompression_totallyPositive m) hA

/-- The realization-theoretic final step of Theorem 4.5.  Once the structural
results above have supplied compatible rank-three support for the positive
three-row compression, Paper A's checked rank-three classification returns a
Toeplitz representation of exactly the rank-three truncation. -/
theorem threeSkeleton_toeplitzRealization_of_compatibleSupport
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hcompatible : HasCompatibleRankThreeSupport
      (columnMatroid (threeRowPositiveCompression m * A))) :
    ∃ b : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz b) ∧
        HasFullRowRank (rankThreeToeplitz b) ∧
        IsRankTruncationOf 3 (columnMatroid (rankThreeToeplitz b))
          (columnMatroid A) := by
  obtain ⟨b, hTN, hfull, hmatroid⟩ :=
    hasTNNRankThreeToeplitzRepresentation_of_hasCompatibleRankThreeSupport
      hcompatible
  refine ⟨b, hTN, hfull, ?_⟩
  rw [hmatroid]
  exact positiveCompression_isRankTruncation
    (threeRowPositiveCompression_totallyPositive m) hA

/-- Two dependent nonzero columns of a totally nonnegative matrix are
positive scalar multiples. -/
theorem columnsPositivelyParallel_of_pair_not_independent
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j)
    (hdep : ¬LinearIndependent ℝ
      (fun t : Fin 2 ↦ A.col (twoPointOrderEmbedding i j hij t))) :
    ColumnsPositivelyParallel A i j := by
  have hiCol : A.col i ≠ 0 := hi
  have hpair :
      (fun t : Fin 2 ↦ A.col (twoPointOrderEmbedding i j hij t)) =
        ![A.col i, A.col j] := by
    funext t
    fin_cases t <;> rfl
  rw [hpair, LinearIndependent.pair_iff' hiCol] at hdep
  push Not at hdep
  obtain ⟨c, hc⟩ := hdep
  have hci : 0 ≤ c := by
    obtain ⟨r, hr⟩ := exists_entry_pos_of_not_isLoop hA hi
    have hjnonneg := hA.entry_nonneg r j
    have hcoord := congrFun hc r
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    change c * A r i = A r j at hcoord
    rw [← hcoord] at hjnonneg
    exact nonneg_of_mul_nonneg_left hjnonneg hr
  have hcne : c ≠ 0 := by
    intro hzero
    apply hj
    rw [IsLoop, ← hc]
    simp [hzero]
  exact ⟨c, lt_of_le_of_ne hci (Ne.symm hcne), hc.symm⟩

/-- Positive parallelism makes a selected pair dependent. -/
theorem pair_not_independent_of_columnsPositivelyParallel
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop A i)
    (hparallel : ColumnsPositivelyParallel A i j) :
    ¬LinearIndependent ℝ
      (fun t : Fin 2 ↦ A.col (twoPointOrderEmbedding i j hij t)) := by
  obtain ⟨c, _, hc⟩ := hparallel
  have hpair :
      (fun t : Fin 2 ↦ A.col (twoPointOrderEmbedding i j hij t)) =
        ![A.col i, A.col j] := by
    funext t
    fin_cases t <;> rfl
  rw [hpair]
  intro hind
  exact (LinearIndependent.pair_iff' hi |>.1 hind c) hc.symm

/-- In a totally nonnegative configuration without loops, positive parallel
classes are ordinary intervals. -/
theorem columnsPositivelyParallel_interval_of_tnn
    {m n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hnonloop : ∀ j, ¬IsLoop A j)
    {i k j : Fin n} (hik : i < k) (hkj : k < j)
    (hijParallel : ColumnsPositivelyParallel A i j) :
    ColumnsPositivelyParallel A i k ∧ ColumnsPositivelyParallel A k j := by
  let P : Matrix (Fin 2) (Fin m) ℝ := twoRowPositiveCompression m
  have hP : TotallyPositive P := twoRowPositiveCompression_totallyPositive m
  have huniform : ∀ cols : Fin 1 ↪o Fin n,
      LinearIndependent ℝ (fun t : Fin 1 ↦ A.col (cols t)) := by
    intro cols
    rw [linearIndependent_unique_iff]
    exact hnonloop (cols default)
  let IJ := twoPointOrderEmbedding i j (hik.trans hkj)
  have hIJdep : ¬(columnMatroid A).Indep (Set.range IJ) := by
    rw [columnMatroid_indep_range_iff]
    exact pair_not_independent_of_columnsPositivelyParallel
      (hik.trans hkj) (hnonloop i) hijParallel
  have hall := (firstCircuit_dependent_iff_all_anchors
    (p := 0) (by omega : 1 < n) hA hP huniform IJ).1 hIJdep
  have pairDep {u v : Fin n} (huv : u < v) (hiu : i ≤ u) (hvj : v ≤ j) :
      ¬(columnMatroid A).Indep
        (Set.range (twoPointOrderEmbedding u v huv)) := by
    apply (firstCircuit_dependent_iff_all_anchors
      (p := 0) (by omega : 1 < n) hA hP huniform _).2
    intro t ht
    apply hall t
    simp only [anchorFinset, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    simp only [IsAnchor] at ht ⊢
    have hzeroPair : twoPointOrderEmbedding u v huv 0 = u := rfl
    have hlastPair :
        twoPointOrderEmbedding u v huv (Fin.last (0 + 1)) = v := rfl
    have hzeroIJ : IJ 0 = i := rfl
    have hlastIJ : IJ (Fin.last (0 + 1)) = j := rfl
    rw [hzeroPair, hlastPair] at ht
    rw [hzeroIJ, hlastIJ]
    constructor <;> omega
  constructor
  · apply columnsPositivelyParallel_of_pair_not_independent hA hik
      (hnonloop i) (hnonloop k)
    rw [← columnMatroid_indep_range_iff]
    exact pairDep hik le_rfl hkj.le
  · apply columnsPositivelyParallel_of_pair_not_independent hA hkj
      (hnonloop k) (hnonloop j)
    rw [← columnMatroid_indep_range_iff]
    exact pairDep hkj hik.le le_rfl

/-! ## Canonical rank-two support extraction -/

/-- Nonloop column indices of an arbitrary finite matrix. -/
def matrixNonloopIndices {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬IsLoop A j

@[simp]
theorem mem_matrixNonloopIndices_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {j : Fin n} :
    j ∈ matrixNonloopIndices A ↔ ¬IsLoop A j := by
  classical
  simp [matrixNonloopIndices]

/-- A full-row-rank two-row matrix has a nonloop column. -/
theorem matrixNonloopIndices_nonempty_of_twoRow_fullRowRank
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ}
    (hfull : HasFullRowRank B) :
    (matrixNonloopIndices B).Nonempty := by
  obtain ⟨cols, hcols⟩ := hfull
  refine ⟨cols 0, (mem_matrixNonloopIndices_iff).2 ?_⟩
  intro hloop
  apply hcols
  rw [orderedMinor]
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  exact isLoop_iff_entry_eq_zero.mp hloop (allRows 2 i)

/-- The first nonloop index of a full-row-rank two-row matrix. -/
def firstMatrixNonloop
    {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℝ) (hfull : HasFullRowRank B) : Fin n :=
  (matrixNonloopIndices B).min'
    (matrixNonloopIndices_nonempty_of_twoRow_fullRowRank hfull)

/-- The last nonloop index of a full-row-rank two-row matrix. -/
def lastMatrixNonloop
    {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℝ) (hfull : HasFullRowRank B) : Fin n :=
  (matrixNonloopIndices B).max'
    (matrixNonloopIndices_nonempty_of_twoRow_fullRowRank hfull)

theorem firstMatrixNonloop_nonloop
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ} (hfull : HasFullRowRank B) :
    ¬IsLoop B (firstMatrixNonloop B hfull) :=
  (mem_matrixNonloopIndices_iff).1
    ((matrixNonloopIndices B).min'_mem
      (matrixNonloopIndices_nonempty_of_twoRow_fullRowRank hfull))

theorem lastMatrixNonloop_nonloop
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ} (hfull : HasFullRowRank B) :
    ¬IsLoop B (lastMatrixNonloop B hfull) :=
  (mem_matrixNonloopIndices_iff).1
    ((matrixNonloopIndices B).max'_mem
      (matrixNonloopIndices_nonempty_of_twoRow_fullRowRank hfull))

theorem firstMatrixNonloop_le_last
    {n : ℕ} {B : Matrix (Fin 2) (Fin n) ℝ} (hfull : HasFullRowRank B) :
    firstMatrixNonloop B hfull ≤ lastMatrixNonloop B hfull :=
  Finset.min'_le _ _ ((matrixNonloopIndices B).max'_mem
    (matrixNonloopIndices_nonempty_of_twoRow_fullRowRank hfull))

/-- Positive two-row compression preserves and reflects loops. -/
theorem isLoop_twoRowPositiveCompression_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (j : Fin n) :
    IsLoop (twoRowPositiveCompression m * A) j ↔ IsLoop A j := by
  let P : Matrix (Fin 2) (Fin m) ℝ := twoRowPositiveCompression m
  let B : Matrix (Fin 2) (Fin n) ℝ := P * A
  constructor
  · intro hBj
    by_contra hAj
    let selected : Fin 1 ↪o Fin n := singletonOrderEmbedding j
    have hAone : LinearIndependent ℝ
        (fun t : Fin 1 ↦ A.col (selected t)) := by
      rw [linearIndependent_unique_iff]
      exact hAj
    have hBone := positiveCompression_preserves_ordered_independence
      (by omega : 1 ≤ 2)
      (twoRowPositiveCompression_totallyPositive m) hA selected hAone
    have hBnonloop : ¬IsLoop B j := by
      rw [linearIndependent_unique_iff] at hBone
      exact hBone
    exact hBnonloop hBj
  · intro hAj
    rw [isLoop_iff_entry_eq_zero] at hAj ⊢
    intro i
    simp [Matrix.mul_apply, hAj]

/-- A full-row-rank matrix of height at least two remains full-row-rank
after the explicit two-row positive compression. -/
theorem twoRowPositiveCompression_fullRowRank
    {m n : ℕ} (hm : 2 ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hfull : HasFullRowRank A) :
    HasFullRowRank (twoRowPositiveCompression m * A) := by
  obtain ⟨basis, hbasis⟩ := hfull
  have hAll : LinearIndependent ℝ
      (fun j : Fin m ↦ A.col (basis j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns A basis).mp hbasis
  let inc : Fin 2 ↪o Fin m := Fin.castLEOrderEmb hm
  let cols : Fin 2 ↪o Fin n := inc.trans basis
  have hAcols : LinearIndependent ℝ
      (fun j : Fin 2 ↦ A.col (cols j)) := by
    exact hAll.comp (fun j : Fin 2 ↦ inc j) inc.injective
  have hBcols := positiveCompression_preserves_ordered_independence le_rfl
    (twoRowPositiveCompression_totallyPositive m) hA cols hAcols
  refine ⟨cols, ?_⟩
  rw [orderedMinor_ne_zero_iff_linearIndependent_columns]
  exact hBcols

/-- The `k=2` case of Theorem 4.5, with the compatible support certificate
extracted canonically from the original Toeplitz matrix. -/
theorem twoSkeleton_toeplitzRealization
    {m n : ℕ} (hm : 2 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) :
    ∃ b : Fin (n + 1) → ℝ,
      TotallyNonnegative (rankTwoToeplitz b) ∧
        HasFullRowRank (rankTwoToeplitz b) ∧
        IsRankTruncationOf 2 (columnMatroid (rankTwoToeplitz b))
          (columnMatroid (toeplitzMatrix m n a)) := by
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let P : Matrix (Fin 2) (Fin m) ℝ := twoRowPositiveCompression m
  let B : Matrix (Fin 2) (Fin n) ℝ := P * A
  have hP : TotallyPositive P := twoRowPositiveCompression_totallyPositive m
  have hB : TotallyNonnegative B := totallyNonnegative_mul hP.totallyNonnegative hA
  have hBfull : HasFullRowRank B :=
    twoRowPositiveCompression_fullRowRank hm hA hfull
  have hBfullCopy := hBfull
  obtain ⟨basisB, hbasisB⟩ := hBfullCopy
  have hn : 2 ≤ n := by
    simpa using Fintype.card_le_of_injective basisB basisB.injective
  let first : Fin n := firstMatrixNonloop B hBfull
  let last : Fin n := lastMatrixNonloop B hBfull
  have hfirstB : ¬IsLoop B first := firstMatrixNonloop_nonloop hBfull
  have hlastB : ¬IsLoop B last := lastMatrixNonloop_nonloop hBfull
  have hfirstA : ¬IsLoop A first := by
    exact (isLoop_twoRowPositiveCompression_iff hA first).not.mp hfirstB
  have hlastA : ¬IsLoop A last := by
    exact (isLoop_twoRowPositiveCompression_iff hA last).not.mp hlastB
  have hfl : first ≤ last := firstMatrixNonloop_le_last hBfull
  have hactive : ∀ j, ¬IsLoop B j ↔ first ≤ j ∧ j ≤ last := by
    intro j
    constructor
    · intro hj
      have hjmem : j ∈ matrixNonloopIndices B :=
        (mem_matrixNonloopIndices_iff).2 hj
      exact ⟨Finset.min'_le _ _ hjmem, Finset.le_max' _ _ hjmem⟩
    · rintro ⟨hfj, hjl⟩
      have hjA : ¬IsLoop A j := by
        exact toeplitzMatrix_nonloop_interval hm hn hA hfj hjl hfirstA hlastA
      exact (isLoop_twoRowPositiveCompression_iff hA j).not.mpr hjA
  have hleft : 0 < first.val → ∀ j,
      first ≤ j → j ≤ last →
      ColumnsPositivelyParallel B first j → j = first := by
    intro hfirstPos j hfj hjl hparallel
    rcases hfj.eq_or_lt with rfl | hfjlt
    · rfl
    have hjB : ¬IsLoop B j := (hactive j).2 ⟨hfjlt.le, hjl⟩
    have hjA : ¬IsLoop A j :=
      (isLoop_twoRowPositiveCompression_iff hA j).not.mp hjB
    let pair : Fin 2 ↪o Fin n := twoPointOrderEmbedding first j hfjlt
    have hBdep : ¬LinearIndependent ℝ
        (fun t : Fin 2 ↦ B.col (pair t)) :=
      pair_not_independent_of_columnsPositivelyParallel
        hfjlt hfirstB hparallel
    have hAdep : ¬LinearIndependent ℝ
        (fun t : Fin 2 ↦ A.col (pair t)) := by
      intro hAind
      apply hBdep
      exact (positiveCompression_ordered_independence_iff le_rfl hP hA pair).2 hAind
    have hAparallel : ColumnsPositivelyParallel A first j :=
      columnsPositivelyParallel_of_pair_not_independent
        hA hfjlt hfirstA hjA hAdep
    let prev : Fin n := ⟨first.val - 1, by omega⟩
    have hprevB : IsLoop B prev := by
      by_contra hprev
      have hprevMem : prev ∈ matrixNonloopIndices B :=
        (mem_matrixNonloopIndices_iff).2 hprev
      have hmin := Finset.min'_le (matrixNonloopIndices B) prev hprevMem
      change first.val ≤ first.val - 1 at hmin
      omega
    have hprevA : IsLoop A prev :=
      (isLoop_twoRowPositiveCompression_iff hA prev).mp hprevB
    have hnextBound : first.val + 1 < n := by omega
    have hnotAdjacent := toeplitzMatrix_not_parallel_after_loop
      hm hfirstPos hnextBound hA hprevA hfirstA
    let width : ℕ := last.val - first.val + 1
    let window : Fin width ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun u ↦ ⟨first.val + u.val, by
        have hu := u.isLt
        have hlastBound := last.isLt
        dsimp only [width] at hu
        omega⟩)
      (by intro x y hxy; apply Fin.mk_lt_mk.mpr; omega)
    let Awin : Matrix (Fin m) (Fin width) ℝ := A.submatrix (allRows m) window
    have hAwin : TotallyNonnegative Awin := hA.submatrix (allRows m) window
    have hwinNonloop : ∀ u, ¬IsLoop Awin u := by
      intro u
      have hbetween : first ≤ window u ∧ window u ≤ last := by
        constructor
        · apply Fin.mk_le_mk.mpr
          change first.val ≤ first.val + u.val
          omega
        · apply Fin.mk_le_mk.mpr
          change first.val + u.val ≤ last.val
          have hu := u.isLt
          dsimp only [width] at hu
          omega
      have hBu : ¬IsLoop B (window u) := (hactive _).2 hbetween
      have hAu : ¬IsLoop A (window u) :=
        (isLoop_twoRowPositiveCompression_iff hA (window u)).not.mp hBu
      intro hloop
      apply hAu
      rw [isLoop_iff_entry_eq_zero] at hloop ⊢
      intro row
      simpa [Awin, Matrix.submatrix_apply, allRows] using hloop row
    have transportParallel {u v : Fin width}
        (hparallel : ColumnsPositivelyParallel Awin u v) :
        ColumnsPositivelyParallel A (window u) (window v) := by
      obtain ⟨c, hc, hcol⟩ := hparallel
      refine ⟨c, hc, ?_⟩
      funext row
      have hrow := congrFun hcol row
      simpa [Awin, Matrix.col_apply, Matrix.submatrix_apply, allRows] using hrow
    let uj : Fin width := ⟨j.val - first.val, by
      dsimp only [width]
      omega⟩
    have hwindowZero : window ⟨0, by
        have hu : 0 < width := by dsimp only [width]; omega
        exact hu⟩ = first := by
      apply Fin.ext
      simp [window]
    have hwindowJ : window uj = j := by
      apply Fin.ext
      simp [window, uj]
      omega
    have hAwinParallel : ColumnsPositivelyParallel Awin
        ⟨0, by dsimp only [width]; omega⟩ uj := by
      rw [ColumnsPositivelyParallel]
      obtain ⟨c, hc, hcol⟩ := hAparallel
      refine ⟨c, hc, ?_⟩
      funext row
      have hrow := congrFun hcol (allRows m row)
      simpa [Awin, Matrix.col_apply, Matrix.submatrix_apply,
        hwindowZero, hwindowJ] using hrow
    have huPos : 0 < uj.val := by dsimp only [uj]; omega
    have hAadjacent : ColumnsPositivelyParallel A first ⟨first.val + 1, hnextBound⟩ := by
      by_cases huOne : uj.val = 1
      · have huEq : uj = ⟨1, by
            dsimp only [width]
            omega⟩ := Fin.ext huOne
        have hlocal := transportParallel hAwinParallel
        rw [hwindowZero, huEq] at hlocal
        have hwindowOne : window ⟨1, by
            dsimp only [width]
            omega⟩ = (⟨first.val + 1, hnextBound⟩ : Fin n) := by
          apply Fin.ext
          simp [window]
        rwa [hwindowOne] at hlocal
      · have huTwo : 1 < uj.val := by omega
        have hwidth : 2 ≤ width := by
          dsimp only [width, uj] at *
          omega
        have hlocal := (columnsPositivelyParallel_interval_of_tnn
          hwidth hAwin hwinNonloop
          (i := (⟨0, by omega⟩ : Fin width))
          (k := (⟨1, by omega⟩ : Fin width)) (j := uj)
          (by apply Fin.mk_lt_mk.mpr; omega)
          (by apply Fin.mk_lt_mk.mpr; omega) hAwinParallel).1
        have htransported := transportParallel hlocal
        have hwindowOne : window ⟨1, by omega⟩ =
            (⟨first.val + 1, hnextBound⟩ : Fin n) := by
          apply Fin.ext
          simp [window]
        rwa [hwindowZero, hwindowOne] at htransported
    exact (hnotAdjacent hAadjacent).elim
  have hright : last.val + 1 < n → ∀ j,
      first ≤ j → j ≤ last →
      ColumnsPositivelyParallel B last j → j = last := by
    intro hlastBound j hfj hjl hparallel
    rcases hjl.eq_or_lt with rfl | hjllt
    · rfl
    have hjB : ¬IsLoop B j := (hactive j).2 ⟨hfj, hjllt.le⟩
    have hjA : ¬IsLoop A j :=
      (isLoop_twoRowPositiveCompression_iff hA j).not.mp hjB
    have hparallel' : ColumnsPositivelyParallel B j last :=
      columnsPositivelyParallel_symm hparallel
    let pair : Fin 2 ↪o Fin n := twoPointOrderEmbedding j last hjllt
    have hBdep : ¬LinearIndependent ℝ
        (fun t : Fin 2 ↦ B.col (pair t)) :=
      pair_not_independent_of_columnsPositivelyParallel hjllt hjB hparallel'
    have hAdep : ¬LinearIndependent ℝ
        (fun t : Fin 2 ↦ A.col (pair t)) := by
      intro hAind
      apply hBdep
      exact (positiveCompression_ordered_independence_iff le_rfl hP hA pair).2 hAind
    have hAparallel : ColumnsPositivelyParallel A j last :=
      columnsPositivelyParallel_of_pair_not_independent
        hA hjllt hjA hlastA hAdep
    let next : Fin n := ⟨last.val + 1, hlastBound⟩
    have hnextB : IsLoop B next := by
      by_contra hnext
      have hnextMem : next ∈ matrixNonloopIndices B :=
        (mem_matrixNonloopIndices_iff).2 hnext
      have hmax := Finset.le_max' (matrixNonloopIndices B) next hnextMem
      change last.val + 1 ≤ last.val at hmax
      omega
    have hnextA : IsLoop A next :=
      (isLoop_twoRowPositiveCompression_iff hA next).mp hnextB
    have hlastPos : 1 ≤ last.val := by omega
    have hnotAdjacent := toeplitzMatrix_not_parallel_before_loop
      hm hlastPos hlastBound hA hlastA hnextA
    let width : ℕ := last.val - first.val + 1
    let window : Fin width ↪o Fin n := OrderEmbedding.ofStrictMono
      (fun u ↦ ⟨first.val + u.val, by
        have hu := u.isLt
        have hlastIsLt := last.isLt
        dsimp only [width] at hu
        omega⟩)
      (by intro x y hxy; apply Fin.mk_lt_mk.mpr; omega)
    let Awin : Matrix (Fin m) (Fin width) ℝ := A.submatrix (allRows m) window
    have hAwin : TotallyNonnegative Awin := hA.submatrix (allRows m) window
    have hwinNonloop : ∀ u, ¬IsLoop Awin u := by
      intro u
      have hbetween : first ≤ window u ∧ window u ≤ last := by
        constructor
        · apply Fin.mk_le_mk.mpr
          change first.val ≤ first.val + u.val
          omega
        · apply Fin.mk_le_mk.mpr
          change first.val + u.val ≤ last.val
          have hu := u.isLt
          dsimp only [width] at hu
          omega
      have hBu : ¬IsLoop B (window u) := (hactive _).2 hbetween
      have hAu : ¬IsLoop A (window u) :=
        (isLoop_twoRowPositiveCompression_iff hA (window u)).not.mp hBu
      intro hloop
      apply hAu
      rw [isLoop_iff_entry_eq_zero] at hloop ⊢
      intro row
      simpa [Awin, Matrix.submatrix_apply, allRows] using hloop row
    have transportParallel {u v : Fin width}
        (hparallel : ColumnsPositivelyParallel Awin u v) :
        ColumnsPositivelyParallel A (window u) (window v) := by
      obtain ⟨c, hc, hcol⟩ := hparallel
      refine ⟨c, hc, ?_⟩
      funext row
      have hrow := congrFun hcol row
      simpa [Awin, Matrix.col_apply, Matrix.submatrix_apply, allRows] using hrow
    let uj : Fin width := ⟨j.val - first.val, by
      dsimp only [width]
      omega⟩
    let ulast : Fin width := ⟨width - 1, by omega⟩
    have hwindowJ : window uj = j := by
      apply Fin.ext
      simp [window, uj]
      omega
    have hwindowLast : window ulast = last := by
      apply Fin.ext
      simp [window, ulast, width]
      omega
    have hAwinParallel : ColumnsPositivelyParallel Awin uj ulast := by
      obtain ⟨c, hc, hcol⟩ := hAparallel
      refine ⟨c, hc, ?_⟩
      funext row
      have hrow := congrFun hcol (allRows m row)
      simpa [Awin, Matrix.col_apply, Matrix.submatrix_apply,
        hwindowJ, hwindowLast] using hrow
    have huLast : uj.val < ulast.val := by
      dsimp only [uj, ulast, width]
      omega
    have hAadjacent : ColumnsPositivelyParallel A
        ⟨last.val - 1, by omega⟩ last := by
      by_cases huPred : uj.val + 1 = ulast.val
      · have huEq : uj = ⟨width - 2, by omega⟩ := by
            apply Fin.ext
            change uj.val = width - 2
            change uj.val + 1 = width - 1 at huPred
            omega
        have htransported := transportParallel hAwinParallel
        rw [huEq] at htransported
        have hwindowPred : window ⟨width - 2, by omega⟩ =
            (⟨last.val - 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          simp [window, width]
          omega
        rwa [hwindowPred, hwindowLast] at htransported
      · let upred : Fin width := ⟨ulast.val - 1, by omega⟩
        have hupred : uj < upred := by
          apply Fin.mk_lt_mk.mpr
          change uj.val < ulast.val - 1
          omega
        have hlocal := (columnsPositivelyParallel_interval_of_tnn
          (by dsimp only [width, ulast] at *; omega) hAwin hwinNonloop
          (i := uj) (k := upred) (j := ulast)
          hupred (by apply Fin.mk_lt_mk.mpr; dsimp only [upred]; omega)
          hAwinParallel).2
        have htransported := transportParallel hlocal
        have hwindowPred : window upred =
            (⟨last.val - 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          simp [window, upred, ulast, width]
          omega
        rwa [hwindowPred, hwindowLast] at htransported
    exact (hnotAdjacent hAadjacent).elim
  have hcompatible : HasCompatibleRankTwoSupport (columnMatroid B) :=
    hasCompatibleRankTwoSupport_of_interval_certificate
      hB hBfull first last hfl hactive hleft hright
  exact twoSkeleton_toeplitzRealization_of_compatibleSupport hA hcompatible

end

end FurtherToeplitzPositroids
