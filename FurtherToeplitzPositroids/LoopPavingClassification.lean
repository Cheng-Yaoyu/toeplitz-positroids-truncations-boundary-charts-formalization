import FurtherToeplitzPositroids.LowSkeleton

/-!
# The loop-paving sector

This module formalizes the support-theoretic necessity part of Theorem 6.2.
The row rank is written as `r + 2`, so the lower paving skeleton has size
`r + 1`.
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-! ## Endpoint protection for arbitrary maximal blocks -/

/-- Full row rank leaves `m` columns at or after the first nonloop column. -/
theorem maximal_successors_of_fullRowRank_of_initial_loops
    {m n p : ℕ} (hm : 0 < m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hfull : HasFullRowRank A)
    (hloops : ∀ j : Fin n, j.val < p → IsLoop A j) :
    p + (m - 1) < n := by
  by_contra hbound
  obtain ⟨cols, hcols⟩ := hfull
  let first : Fin m := ⟨0, hm⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  have hgap : (cols first).val + (m - 1) ≤ (cols last).val := by
    have hchain : ∀ q : ℕ, (hq : q < m) →
        (cols first).val + q ≤ (cols ⟨q, hq⟩).val := by
      intro q hq
      induction q with
      | zero => simp [first]
      | succ q ih =>
          have hq' : q < m := by omega
          have hstep := cols.strictMono
            (show (⟨q, hq'⟩ : Fin m) < ⟨q + 1, hq⟩ by
              apply Fin.mk_lt_mk.mpr
              omega)
          have hprev := ih hq'
          omega
    have hlast := hchain (m - 1) (by omega)
    simpa [last] using hlast
  have hfirst : (cols first).val < p := by
    by_contra hfirst
    have hlastBound := (cols last).isLt
    omega
  have hloop := hloops (cols first) hfirst
  apply hcols
  rw [orderedMinor]
  apply Matrix.det_eq_zero_of_column_eq_zero first
  intro i
  exact isLoop_iff_entry_eq_zero.mp hloop (allRows m i)

/-- A nonempty loop prefix forces the first consecutive maximal minor of the
nonloop block to be positive.  This is the endpoint condition (36) in the
necessity direction of Theorem 6.2. -/
theorem toeplitzMatrix_first_nonloop_maximalMinor_pos
    {r n p : ℕ} {a : ℤ → ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hpBound : p < n)
    (hA : TotallyNonnegative (toeplitzMatrix (r + 1) n a))
    (hfull : HasFullRowRank (toeplitzMatrix (r + 1) n a))
    (hloops : ∀ j : Fin n, j.val < p →
      IsLoop (toeplitzMatrix (r + 1) n a) j)
    (hnonloop : ¬IsLoop (toeplitzMatrix (r + 1) n a) ⟨p, hpBound⟩) :
    ∃ (hrn : r < n) (t : Fin (n - r)), t.val = p ∧
      0 < matrixConsecutiveMinor hrn (toeplitzMatrix (r + 1) n a) t := by
  have hbound := maximal_successors_of_fullRowRank_of_initial_loops
    (by omega : 0 < r + 1) hfull hloops
  have hrn : r < n := by omega
  let t : Fin (n - r) := ⟨p, by omega⟩
  have hap := toeplitzMatrix_top_coefficient_pos_after_loop
    (by omega : 2 ≤ r + 1) hp hpBound hA
      (hloops ⟨p - 1, by omega⟩ (by change p - 1 < p; omega)) hnonloop
  let block : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    (toeplitzMatrix (r + 1) n a).submatrix
      (allRows (r + 1)) (consecutiveColumns hrn t)
  have htri : block.BlockTriangular id := by
    intro i j hji
    have hjiVal : j.val < i.val := by simpa using hji
    let rloop : Fin (r + 1) := ⟨i.val - j.val - 1, by omega⟩
    have hzero := isLoop_iff_entry_eq_zero.mp
      (hloops ⟨p - 1, by omega⟩ (by change p - 1 < p; omega)) rloop
    rw [toeplitzMatrix_apply] at hzero
    change toeplitzMatrix (r + 1) n a (allRows (r + 1) i)
      (consecutiveColumns hrn t j) = 0
    rw [toeplitzMatrix_apply]
    have hoffset : ((consecutiveColumns hrn t j : Fin n) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ) =
          (((p - 1 : ℕ) : ℤ) - (rloop : ℤ)) := by
      simp only [consecutiveColumns_apply_val, allRows_apply_eq_self]
      dsimp only [rloop, t]
      omega
    rwa [hoffset]
  have hdiag : ∀ i : Fin (r + 1), block i i = a (p : ℤ) := by
    intro i
    change toeplitzMatrix (r + 1) n a (allRows (r + 1) i)
      (consecutiveColumns hrn t i) = _
    rw [toeplitzMatrix_apply]
    have hoffset : ((consecutiveColumns hrn t i : Fin n) : ℤ) -
        ((allRows (r + 1) i : Fin (r + 1)) : ℤ) = (p : ℤ) := by
      simp only [consecutiveColumns_apply_val, allRows_apply_eq_self]
      dsimp only [t]
      omega
    rw [hoffset]
  refine ⟨hrn, t, rfl, ?_⟩
  change 0 < block.det
  rw [Matrix.det_of_upperTriangular htri]
  simp_rw [hdiag]
  exact Finset.prod_pos fun _ _ ↦ hap

/-- The symmetric nonempty-loop-suffix endpoint condition in Theorem 6.2. -/
theorem toeplitzMatrix_last_nonloop_maximalMinor_pos
    {r n q : ℕ} {a : ℤ → ℝ}
    (hr : 0 < r) (hq : q + 1 < n)
    (hA : TotallyNonnegative (toeplitzMatrix (r + 1) n a))
    (hfull : HasFullRowRank (toeplitzMatrix (r + 1) n a))
    (hloops : ∀ j : Fin n, q < j.val →
      IsLoop (toeplitzMatrix (r + 1) n a) j)
    (hnonloop : ¬IsLoop (toeplitzMatrix (r + 1) n a) ⟨q, by omega⟩) :
    ∃ (hrn : r < n) (t : Fin (n - r)), t.val + r = q ∧
      0 < matrixConsecutiveMinor hrn (toeplitzMatrix (r + 1) n a) t := by
  let A : Matrix (Fin (r + 1)) (Fin n) ℝ := toeplitzMatrix (r + 1) n a
  let arev : ℤ → ℝ := reverseCoefficients (r + 1) n a
  let pRev : ℕ := n - 1 - q
  have hpRev : 1 ≤ pRev := by dsimp only [pRev]; omega
  have hpRevBound : pRev < n := by dsimp only [pRev]; omega
  have hmatrix : reverseMatrix A = toeplitzMatrix (r + 1) n arev := by
    simpa [A, arev, reverseMatrix] using toeplitzMatrix_submatrix_rev
      (r := r + 1) (n := n) a
  have hrevTN : TotallyNonnegative (toeplitzMatrix (r + 1) n arev) := by
    rw [← hmatrix]
    exact hA.reverseMatrix
  have hrevFull : HasFullRowRank (toeplitzMatrix (r + 1) n arev) := by
    rw [← hmatrix]
    exact (hasFullRowRank_reverseMatrix_iff A).2 hfull
  have hrevLoops : ∀ j : Fin n, j.val < pRev →
      IsLoop (toeplitzMatrix (r + 1) n arev) j := by
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
  have hrevNonloop : ¬IsLoop (toeplitzMatrix (r + 1) n arev) jp := by
    rw [← hmatrix, isLoop_reverseMatrix_iff, hjpRev]
    exact hnonloop
  obtain ⟨hrn, trev, htrev, hminor⟩ :=
    toeplitzMatrix_first_nonloop_maximalMinor_pos
      hr hpRev hpRevBound hrevTN hrevFull hrevLoops hrevNonloop
  have hqr : r ≤ q := by
    have htrevBound := trev.isLt
    dsimp only [pRev] at htrev htrevBound
    omega
  let t : Fin (n - r) := ⟨q - r, by omega⟩
  have hcols : reverseOrderEmbedding (consecutiveColumns hrn trev) =
      consecutiveColumns hrn t := by
    apply RelEmbedding.ext
    intro i
    apply Fin.ext
    simp only [reverseOrderEmbedding_apply, Fin.val_rev,
      consecutiveColumns_apply_val]
    dsimp only [t]
    omega
  refine ⟨hrn, t, by dsimp only [t]; omega, ?_⟩
  rw [← hmatrix] at hminor
  unfold matrixConsecutiveMinor matrixMaximalMinor at hminor ⊢
  rw [orderedMinor_reverseMatrix, reverseOrderEmbedding_allRows, hcols] at hminor
  exact hminor

/-- The consecutive maximal-minor zero set on a loop-free paving block. -/
def loopPavingZeroSet
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ) :
    Finset (Fin (n - (r + 1))) :=
  Finset.univ.filter fun t ↦ matrixConsecutiveMinor hrn A t = 0

@[simp]
theorem mem_loopPavingZeroSet_iff
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (t : Fin (n - (r + 1))) :
    t ∈ loopPavingZeroSet hrn A ↔ matrixConsecutiveMinor hrn A t = 0 := by
  simp [loopPavingZeroSet]

/-- Equation (34), at matrix-support level: a maximal minor is nonzero
exactly when at least one consecutive anchor in its endpoint span lies
outside the zero set. -/
theorem loopPaving_maximalMinor_ne_zero_iff
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (J : Fin (r + 2) ↪o Fin n) :
    matrixMaximalMinor A J ≠ 0 ↔
      ∃ t ∈ anchorFinset J, t ∉ loopPavingZeroSet hrn A := by
  have hzero := positive_completion_maximalMinor_eq_zero_iff
    hrn (hA.tnUpTo (r + 1)) hind
      (fun t ↦ hA.orderedMinor_nonneg (allRows (r + 2)) (consecutiveColumns hrn t)) J
  constructor
  · intro hJ
    by_contra hnone
    push Not at hnone
    apply hJ
    apply hzero.2
    intro t ht
    exact (mem_loopPavingZeroSet_iff hrn A t).1 (hnone t ht)
  · rintro ⟨t, ht, htZ⟩ hJzero
    have hall := hzero.1 hJzero t ht
    exact htZ (mem_loopPavingZeroSet_iff hrn A t |>.2 hall)

/-- Full row rank makes the consecutive zero set proper. -/
theorem loopPavingZeroSet_proper
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (hfull : HasFullRowRank A) :
    loopPavingZeroSet hrn A ≠ Finset.univ := by
  obtain ⟨J, hJ⟩ := hfull
  intro hzero
  have hsupport := (loopPaving_maximalMinor_ne_zero_iff hrn hA hind J).1 hJ
  obtain ⟨t, ht, htZ⟩ := hsupport
  apply htZ
  rw [hzero]
  exact Finset.mem_univ t

/-- The support predicate depends only on the proper zero set. -/
def LoopPavingBasisPredicate
    {r n : ℕ}
    (Z : Finset (Fin (n - (r + 1))))
    (J : Fin (r + 2) ↪o Fin n) : Prop :=
  ∃ t ∈ anchorFinset J, t ∉ Z

/-- Theorem 6.2(ii), loop-free block necessity in a reusable packaged form. -/
theorem loopPaving_basisPredicate_exact
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (J : Fin (r + 2) ↪o Fin n) :
    matrixMaximalMinor A J ≠ 0 ↔
      LoopPavingBasisPredicate (loopPavingZeroSet hrn A) J :=
  loopPaving_maximalMinor_ne_zero_iff hrn hA hind J

/-! ## Zero runs and interval hyperplanes -/

/-- Avoiding the first consecutive coordinate is exactly the condition that
no enlarged zero-run interval contains the first nonloop element. -/
theorem zero_not_mem_iff_first_not_mem_runHyperplane
    {k n runCount : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z runCount) :
    (⟨0, by omega⟩ : Fin (n - k)) ∉ Z ↔
      ∀ a, (⟨0, by omega⟩ : Fin n) ∉ runHyperplane hk D a := by
  constructor
  · intro hzero a hmem
    have hbounds := Finset.mem_Icc.mp hmem
    have hleft : (D.left a).val = 0 := by
      have hleftBound := Fin.le_iff_val_le_val.mp hbounds.1
      change (D.left a).val ≤ 0 at hleftBound
      omega
    apply hzero
    apply (D.mem_iff _).2
    refine ⟨a, ?_, ?_⟩
    · apply Fin.mk_le_mk.mpr
      change (D.left a).val ≤ 0
      omega
    · have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
      apply Fin.mk_le_mk.mpr
      change 0 ≤ (D.right a).val
      omega
  · intro hrun hzero
    obtain ⟨a, hleft, hright⟩ := (D.mem_iff _).1 hzero
    apply hrun a
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftVal := Fin.le_iff_val_le_val.mp hleft
      exact hleftVal
    · apply Fin.mk_le_mk.mpr
      change 0 ≤ (D.right a).val + k
      omega

/-- Avoiding the final consecutive coordinate is exactly the right endpoint
protection condition on all enlarged zero-run intervals. -/
theorem last_not_mem_iff_last_not_mem_runHyperplane
    {k n runCount : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z runCount) :
    (⟨n - k - 1, by omega⟩ : Fin (n - k)) ∉ Z ↔
      ∀ a, (⟨n - 1, by omega⟩ : Fin n) ∉ runHyperplane hk D a := by
  constructor
  · intro hlast a hmem
    have hbounds := Finset.mem_Icc.mp hmem
    have hright : (D.right a).val = n - k - 1 := by
      have hrightBound := (D.right a).isLt
      have hrightMem := Fin.le_iff_val_le_val.mp hbounds.2
      change n - 1 ≤ (D.right a).val + k at hrightMem
      omega
    apply hlast
    apply (D.mem_iff _).2
    refine ⟨a, ?_, ?_⟩
    · have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
      apply Fin.mk_le_mk.mpr
      change (D.left a).val ≤ n - k - 1
      omega
    · apply Fin.mk_le_mk.mpr
      change n - k - 1 ≤ (D.right a).val
      omega
  · intro hrun hlast
    obtain ⟨a, hleft, hright⟩ := (D.mem_iff _).1 hlast
    apply hrun a
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftBound := (D.left a).isLt
      change (D.left a).val ≤ n - 1
      omega
    · apply Fin.mk_le_mk.mpr
      change n - 1 ≤ (D.right a).val + k
      have hrightVal := Fin.le_iff_val_le_val.mp hright
      change n - k - 1 ≤ (D.right a).val at hrightVal
      have hrightBound := (D.right a).isLt
      omega

/-- Equation (37): distinct enlarged zero-run intervals meet in at most
`k-1` elements. -/
theorem loopPaving_runHyperplane_intersection_bound
    {k n runCount : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z runCount)
    {a b : Fin runCount} (hab : a ≠ b) :
    ((runHyperplane hk D a) ∩ (runHyperplane hk D b)).card ≤ k - 1 :=
  card_runHyperplane_inter_le hk D hab

/-- Every enlarged nonempty zero run contains at least `k+1` columns, the
rank-sized lower bound in Theorem 6.2(iii). -/
theorem loopPaving_runHyperplane_card_lower_bound
    {k n runCount : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z runCount)
    (a : Fin runCount) :
    k + 1 ≤ (runHyperplane hk D a).card := by
  let core : Finset (Fin n) :=
    Finset.univ.image (runFullColumns hk D a)
  have hsubset : core ⊆ runHyperplane hk D a := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact runFullColumns_mem_runHyperplane hk D a i
  have hcard := Finset.card_le_card hsubset
  have hcoreCard : core.card = k + 1 := by
    dsimp only [core]
    rw [Finset.card_image_of_injective _ (runFullColumns hk D a).injective,
      Finset.card_univ, Fintype.card_fin]
  rwa [hcoreCard] at hcard

end

end FurtherToeplitzPositroids
