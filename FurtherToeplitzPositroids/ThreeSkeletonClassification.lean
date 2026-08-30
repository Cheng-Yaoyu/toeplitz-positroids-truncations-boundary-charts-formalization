import FurtherToeplitzPositroids.LoopPavingClassification

/-!
# Compatible rank-three data from first-circuit intervals

This module constructs the simple compatible rank-three datum associated to
the zero-run intervals of a loop-free, pairwise independent three-row TNN
configuration. It is the core combinatorial assembly used in Theorem 4.5.
-/

namespace FurtherToeplitzPositroids

open PavingToeplitzPositroids ToeplitzPositroids
open ToeplitzPositroids.RankThree

noncomputable section

/-! ## Three-row compression transport -/

/-- A positive multiple of a nonloop column is a nonloop in any row
dimension. -/
theorem not_isLoop_right_of_columnsPositivelyParallel
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {i j : Fin n}
    (hparallel : ColumnsPositivelyParallel A i j) (hi : ¬IsLoop A i) :
    ¬IsLoop A j := by
  obtain ⟨c, hc, hcol⟩ := hparallel
  intro hj
  apply hi
  rw [isLoop_iff_entry_eq_zero]
  intro r
  have hcoord := congrFun hcol r
  have hjzero := isLoop_iff_entry_eq_zero.mp hj r
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  rw [hjzero] at hcoord
  exact (mul_eq_zero.mp hcoord.symm).resolve_left hc.ne'

/-- Positive three-row compression preserves and reflects loops. -/
theorem isLoop_threeRowPositiveCompression_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (j : Fin n) :
    IsLoop (threeRowPositiveCompression m * A) j ↔ IsLoop A j := by
  let P : Matrix (Fin 3) (Fin m) ℝ := threeRowPositiveCompression m
  let C : Matrix (Fin 3) (Fin n) ℝ := P * A
  constructor
  · intro hCj
    by_contra hAj
    let selected : Fin 1 ↪o Fin n := singletonOrderEmbedding j
    have hAone : LinearIndependent ℝ
        (fun t : Fin 1 ↦ A.col (selected t)) := by
      rw [linearIndependent_unique_iff]
      exact hAj
    have hCone := positiveCompression_preserves_ordered_independence
      (by omega : 1 ≤ 3)
      (threeRowPositiveCompression_totallyPositive m) hA selected hAone
    have hCnonloop : ¬IsLoop C j := by
      rw [linearIndependent_unique_iff] at hCone
      exact hCone
    exact hCnonloop hCj
  · intro hAj
    rw [isLoop_iff_entry_eq_zero] at hAj ⊢
    intro i
    simp [Matrix.mul_apply, hAj]

/-- Positive parallel classes are unchanged by the three-row compression. -/
theorem columnsPositivelyParallel_threeRowCompression_iff
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) :
    ColumnsPositivelyParallel (threeRowPositiveCompression m * A) i j ↔
      ColumnsPositivelyParallel A i j := by
  let P : Matrix (Fin 3) (Fin m) ℝ := threeRowPositiveCompression m
  let C : Matrix (Fin 3) (Fin n) ℝ := P * A
  have hP : TotallyPositive P := threeRowPositiveCompression_totallyPositive m
  have hC : TotallyNonnegative C := totallyNonnegative_mul hP.totallyNonnegative hA
  have hiC : ¬IsLoop C i := (isLoop_threeRowPositiveCompression_iff hA i).not.mpr hi
  have hjC : ¬IsLoop C j := (isLoop_threeRowPositiveCompression_iff hA j).not.mpr hj
  constructor
  · intro hparallel
    let pair : Fin 2 ↪o Fin n := twoPointOrderEmbedding i j hij
    have hCdep := pair_not_independent_of_columnsPositivelyParallel
      hij hiC hparallel
    have hAdep : ¬LinearIndependent ℝ
        (fun t : Fin 2 ↦ A.col (pair t)) := by
      intro hAind
      apply hCdep
      exact positiveCompression_preserves_ordered_independence
        (by omega : 2 ≤ 3) hP hA pair hAind
    exact columnsPositivelyParallel_of_pair_not_independent hA hij hi hj hAdep
  · rintro ⟨c, hc, hcol⟩
    refine ⟨c, hc, ?_⟩
    funext row
    simp only [Matrix.col_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqcol := congrFun hcol q
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hqcol
    rw [hqcol]
    ring

/-- Full row rank at least three survives the explicit three-row compression. -/
theorem threeRowPositiveCompression_fullRowRank
    {m n : ℕ} (hm : 3 ≤ m) {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hfull : HasFullRowRank A) :
    HasFullRowRank (threeRowPositiveCompression m * A) := by
  obtain ⟨basis, hbasis⟩ := hfull
  have hAll : LinearIndependent ℝ
      (fun j : Fin m ↦ A.col (basis j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns A basis).mp hbasis
  let inc : Fin 3 ↪o Fin m := Fin.castLEOrderEmb hm
  let cols : Fin 3 ↪o Fin n := inc.trans basis
  have hAcols : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (cols j)) :=
    hAll.comp (fun j : Fin 3 ↦ inc j) inc.injective
  have hCcols := positiveCompression_preserves_ordered_independence le_rfl
    (threeRowPositiveCompression_totallyPositive m) hA cols hAcols
  refine ⟨cols, ?_⟩
  rw [orderedMinor_ne_zero_iff_linearIndependent_columns]
  exact hCcols

/-- The explicit three-row compression of an arbitrary-row Toeplitz matrix. -/
def compressedThreeRowToeplitzMatrix
    (m n : ℕ) (a : ℤ → ℝ) : Matrix (Fin 3) (Fin n) ℝ :=
  threeRowPositiveCompression m * toeplitzMatrix m n a

/-- From the second simplified class onward, consecutive simplification
representatives of the three-row compression are consecutive raw columns.
This is Theorem 4.3 in the form needed for the rank-three block counts. -/
theorem threeRowCompression_internal_representatives_consecutive
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    {q : Fin (simplificationSize
      (compressedThreeRowToeplitzMatrix m n a))}
    (hqPos : 0 < q.val)
    (hqNext : q.val + 1 < simplificationSize
      (compressedThreeRowToeplitzMatrix m n a)) :
    let C := compressedThreeRowToeplitzMatrix m n a
    (simplificationEmbedding C ⟨q.val + 1, hqNext⟩).val =
      (simplificationEmbedding C q).val + 1 := by
  dsimp only
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let qnext : Fin (simplificationSize C) := ⟨q.val + 1, hqNext⟩
  let first : Fin n := simplificationEmbedding C q
  let next : Fin n := simplificationEmbedding C qnext
  let p : ℕ := first.val
  let L : ℕ := next.val - first.val
  have hpEq : p = first.val := rfl
  have hqnext : q < qnext := Fin.mk_lt_mk.mpr (by omega)
  have hfirstNext : first < next := (simplificationEmbedding C).strictMono hqnext
  have hpLEq : p + L = next.val := by
    dsimp only [p, L]
    have hvals : first.val < next.val := hfirstNext
    omega
  by_contra hgap
  change next.val ≠ first.val + 1 at hgap
  have hL : 2 ≤ L := by
    dsimp only [L]
    omega
  have hp : 1 ≤ p := by
    let qzero : Fin (simplificationSize C) := ⟨0, Nat.zero_lt_of_lt q.isLt⟩
    have hzeroq : qzero < q := Fin.mk_lt_mk.mpr hqPos
    have hemb := (simplificationEmbedding C).strictMono hzeroq
    change (simplificationEmbedding C qzero).val < first.val at hemb
    rw [hpEq]
    omega
  have hbound : p + L < n := by
    have hnextBound := next.isLt
    rw [hpLEq]
    exact next.isLt
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hTwo : TNUpTo C 2 := hC.tnUpTo 2
  have hfirstC : ¬IsLoop C first := simplificationEmbedding_not_isLoop C q
  have hnextC : ¬IsLoop C next := simplificationEmbedding_not_isLoop C qnext
  have hfirstA : ¬IsLoop A first :=
    (isLoop_threeRowPositiveCompression_iff hA first).not.mp hfirstC
  have hnextA : ¬IsLoop A next :=
    (isLoop_threeRowPositiveCompression_iff hA next).not.mp hnextC
  have hblockC : ∀ t : Fin L,
      ColumnsPositivelyParallel C first ⟨p + t.val, by omega⟩ := by
    intro t
    let x : Fin n := ⟨p + t.val, by omega⟩
    have hfirstx : first ≤ x := by
      apply Fin.mk_le_mk.mpr
      change first.val ≤ p + t.val
      rw [hpEq]
      exact Nat.le_add_right _ _
    have hxnext : x < next := by
      apply Fin.mk_lt_mk.mpr
      change p + t.val < next.val
      rw [← hpLEq]
      exact Nat.add_lt_add_left t.isLt p
    have hxC : ¬IsLoop C x := by
      have hxA : ¬IsLoop A x :=
        toeplitzMatrix_nonloop_interval (by omega : 2 ≤ m) (by omega) hA
          hfirstx hxnext.le hfirstA hnextA
      exact (isLoop_threeRowPositiveCompression_iff hA x).not.mpr hxA
    let c := simplificationClassIndex C x hxC
    have hclassFirst : simplificationClassIndex C first hfirstC = q := by
      apply (simplificationClassIndex_eq_iff C first hfirstC q).2
      exact columnsPositivelyParallel_refl C first
    have hqle : q ≤ c := by
      have hmono := simplificationClassIndex_mono_of_tnUpTo_two
        hTwo hfirstx hfirstC hxC
      rwa [hclassFirst] at hmono
    have hclt : c < qnext := by
      by_contra hc
      have hnextc : qnext ≤ c := le_of_not_gt hc
      have hemb := (simplificationEmbedding C).monotone hnextc
      have hrep := simplificationEmbedding_classIndex_eq_parallelRepresentative C x hxC
      have hreple : parallelRepresentative C x ≤ x :=
        parallelRepresentative_le (columnsPositivelyParallel_refl C x)
      rw [← hrep] at hreple
      exact (not_le_of_gt hxnext) (hemb.trans hreple)
    have hcq : c = q := by
      apply Fin.ext
      have hqv := Fin.mk_le_mk.mp hqle
      have hcv := Fin.mk_lt_mk.mp hclt
      change c.val < q.val + 1 at hcv
      omega
    have hpar := simplificationClassIndex_parallel C x hxC
    simpa [c, hcq, first, x] using hpar
  have hblockA : ∀ t : Fin L,
      ColumnsPositivelyParallel A ⟨p, by omega⟩ ⟨p + t.val, by omega⟩ := by
    intro t
    by_cases ht : t.val = 0
    · have hindex : (⟨p + t.val, by omega⟩ : Fin n) = ⟨p, by omega⟩ :=
        Fin.ext (by change p + t.val = p; omega)
      rw [hindex]
      exact columnsPositivelyParallel_refl A _
    · have hlt : (⟨p, by omega⟩ : Fin n) < ⟨p + t.val, by omega⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      have hrightA : ¬IsLoop A ⟨p + t.val, by omega⟩ := by
        have hrightC : ¬IsLoop C ⟨p + t.val, by omega⟩ :=
          (isLoop_iff_of_columnsPositivelyParallel (hblockC t)).not.mp hfirstC
        exact (isLoop_threeRowPositiveCompression_iff hA _).not.mp hrightC
      apply (columnsPositivelyParallel_threeRowCompression_iff
        hA hlt (by simpa [p, first] using hfirstA) hrightA).1
      simpa [p, first] using hblockC t
  have hnonloopA : ∀ t : Fin L, ¬IsLoop A ⟨p + t.val, by omega⟩ := by
    intro t
    have hfirstEq : (⟨p, by omega⟩ : Fin n) = first := by rfl
    have hfirstNonloop : ¬IsLoop A ⟨p, by omega⟩ := by
      rwa [hfirstEq]
    exact not_isLoop_right_of_columnsPositivelyParallel (hblockA t) hfirstNonloop
  have hleftMax : ¬ColumnsPositivelyParallel A
      ⟨p - 1, by omega⟩ ⟨p, by omega⟩ := by
    intro hparA
    have hfirstEq : (⟨p, by omega⟩ : Fin n) = first := by rfl
    have hfirstNonloop : ¬IsLoop A ⟨p, by omega⟩ := by rwa [hfirstEq]
    have hleftA : ¬IsLoop A ⟨p - 1, by omega⟩ :=
      not_isLoop_right_of_columnsPositivelyParallel
        (columnsPositivelyParallel_symm hparA) hfirstNonloop
    have hparC := (columnsPositivelyParallel_threeRowCompression_iff hA
      (Fin.mk_lt_mk.mpr (by omega)) hleftA
      (by simpa [p, first] using hfirstA)).2 hparA
    change ColumnsPositivelyParallel C
      ⟨p - 1, by omega⟩ ⟨p, by omega⟩ at hparC
    have hrepEq := parallelRepresentative_eq_iff.2 hparC
    have hpFixed : parallelRepresentative C ⟨p, by omega⟩ = ⟨p, by omega⟩ := by
      simpa [p, first] using parallelRepresentative_simplificationEmbedding C q
    rw [hpFixed] at hrepEq
    have hreple : parallelRepresentative C ⟨p - 1, by omega⟩ ≤ ⟨p - 1, by omega⟩ :=
      parallelRepresentative_le (columnsPositivelyParallel_refl C _)
    rw [hrepEq] at hreple
    exact (not_le_of_gt (Fin.mk_lt_mk.mpr (by omega))) hreple
  have hrightMax : ¬ColumnsPositivelyParallel A
      ⟨p + L - 1, by omega⟩ ⟨p + L, by omega⟩ := by
    intro hparA
    have hlastAraw := hblockA ⟨L - 1, by omega⟩
    have hlastA : ColumnsPositivelyParallel A
        ⟨p, by omega⟩ ⟨p + L - 1, by omega⟩ := by
      convert hlastAraw using 1
      apply Fin.ext
      simp
      omega
    have hfirstRight := columnsPositivelyParallel_trans hlastA hparA
    have hpLEq : (⟨p + L, by omega⟩ : Fin n) = next := by
      apply Fin.ext
      dsimp only [p, L]
      omega
    rw [hpLEq] at hfirstRight
    have hfirstEq : (⟨p, by omega⟩ : Fin n) = first := by rfl
    rw [hfirstEq] at hfirstRight
    have hparC := (columnsPositivelyParallel_threeRowCompression_iff hA
      hfirstNext hfirstA hnextA).2 hfirstRight
    change ColumnsPositivelyParallel C first next at hparC
    exact (ne_of_lt hqnext) ((simplificationEmbedding_parallel_iff C).1
      (by simpa [first, next] using hparC))
  let block : IsMaximalToeplitzParallelBlock A p L :=
    { two_le := hL
      bound := hbound.le
      nonloop := hnonloopA
      parallel := hblockA
      left_maximal := fun _ ↦ hleftMax
      right_maximal := fun _ ↦ hrightMax }
  rcases toeplitzMatrix_endpointParallel hm hA block with hpzero | hterminal
  · omega
  · omega

/-- Closed formula for every internal simplification representative. -/
theorem threeRowCompression_internal_simplificationEmbedding_val
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    {k : ℕ} (hk1 : 1 ≤ k)
    (hks : k < simplificationSize (compressedThreeRowToeplitzMatrix m n a)) :
    (simplificationEmbedding (compressedThreeRowToeplitzMatrix m n a) ⟨k, hks⟩).val =
      (simplificationEmbedding (compressedThreeRowToeplitzMatrix m n a)
        ⟨1, by omega⟩).val + (k - 1) := by
  induction k, hk1 using Nat.le_induction with
  | base => simp
  | succ k hk1 ih =>
      have hks' : k < simplificationSize (compressedThreeRowToeplitzMatrix m n a) := by
        omega
      have hstep := threeRowCompression_internal_representatives_consecutive
        hm hA (q := (⟨k, hks'⟩ :
          Fin (simplificationSize (compressedThreeRowToeplitzMatrix m n a))))
        hk1 hks
      have ih' := ih hks'
      rw [hstep, ih']
      omega

/-- A zero run enlarged by two columns, viewed as a simplified rank-two
interval. -/
def firstCircuitRunInterval
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (a : Fin D.runCount) :
    SimplifiedInterval n where
  left := runLeftColumn D.runs a
  right := runRightColumn h D.runs a
  left_le_right := by
    apply Fin.mk_le_mk.mpr
    have hlr := Fin.le_iff_val_le_val.mp (D.runs.left_le_right a)
    omega

/-- The finite family of enlarged zero-run intervals. -/
def firstCircuitRunIntervals
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) :
    Finset (SimplifiedInterval n) :=
  Finset.univ.image (firstCircuitRunInterval D)

/-- The simple compatible rank-three datum: no loops, singleton endpoint
parallel classes, and rank-two intervals supplied by the first-circuit runs. -/
def simpleCompatibleRankThreeData
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) :
    CompatibleRankThreeData n where
  leftLoopCount := 0
  rightLoopCount := 0
  initialParallelSize := 1
  terminalParallelSize := 1
  simplifiedSize := n
  initialParallelSize_pos := by omega
  terminalParallelSize_pos := by omega
  simplifiedSize_ge_three := by omega
  groundSize_eq := by omega
  initialParallel_singleton_of_leftLoops := by omega
  terminalParallel_singleton_of_rightLoops := by omega
  intervals := firstCircuitRunIntervals D
  interval_large := by
    intro H hH
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    simp only [firstCircuitRunInterval, runLeftColumn, runRightColumn]
    have hlr := Fin.le_iff_val_le_val.mp (D.runs.left_le_right a)
    omega
  intervals_separated := by
    intro H hH K hK hHK
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hK
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hHK rfl
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · have hsep := D.runs.separated hablt
      have hle : (D.runs.right a).val + 2 ≤ (D.runs.left b).val := by omega
      rcases hle.eq_or_lt with heq | hlt
      · refine Or.inr (Or.inr (Or.inl ?_))
        apply Fin.ext
        change (D.runs.right a).val + 2 = (D.runs.left b).val
        exact heq
      · exact Or.inl (Fin.mk_lt_mk.mpr hlt)
    · have hsep := D.runs.separated hbalt
      have hle : (D.runs.right b).val + 2 ≤ (D.runs.left a).val := by omega
      rcases hle.eq_or_lt with heq | hlt
      · refine Or.inr (Or.inr (Or.inr ?_))
        apply Fin.ext
        change (D.runs.right b).val + 2 = (D.runs.left a).val
        exact heq
      · exact Or.inr (Or.inl (Fin.mk_lt_mk.mpr hlt))
  initial_endpoint_protected := by simp
  terminal_endpoint_protected := by simp
  interval_not_whole := by
    intro H hH
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    by_contra hwhole
    push Not at hwhole
    rcases hwhole with ⟨hleft, hright⟩
    apply D.zeroSet_proper
    apply Finset.eq_univ_of_forall
    intro t
    apply (D.runs.mem_iff t).2
    refine ⟨a, ?_, ?_⟩
    · apply Fin.mk_le_mk.mpr
      change (D.runs.left a).val ≤ t.val
      have hleftVal : (D.runs.left a).val = 0 := by
        simpa [firstCircuitRunInterval, runLeftColumn] using hleft
      omega
    · apply Fin.mk_le_mk.mpr
      change t.val ≤ (D.runs.right a).val
      have hrightVal : (D.runs.right a).val + 2 + 1 = n := by
        simpa [firstCircuitRunInterval, runRightColumn] using hright
      have ht := t.isLt
      omega

/-! ## Simplification formulas for the simple datum -/

@[simp]
theorem simpleCompatibleRankThreeData_isLoop_false
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (j : Fin n) :
    ¬(simpleCompatibleRankThreeData D).IsLoop j := by
  simp [CompatibleRankThreeData.IsLoop,
    CompatibleRankThreeData.IsLeftLoop, CompatibleRankThreeData.IsRightLoop,
    simpleCompatibleRankThreeData, CompatibleRankThreeData.rightLoopStart,
    CompatibleRankThreeData.terminalStart, CompatibleRankThreeData.middleStart]
  omega

@[simp]
theorem simpleCompatibleRankThreeData_simplifiedIndex
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (j : Fin n) :
    (simpleCompatibleRankThreeData D).simplifiedIndex j = j := by
  apply Fin.ext
  unfold CompatibleRankThreeData.simplifiedIndex
    CompatibleRankThreeData.simplifiedIndexNat
  simp only [simpleCompatibleRankThreeData,
    CompatibleRankThreeData.middleStart, CompatibleRankThreeData.terminalStart]
  split_ifs <;> omega

@[simp]
theorem simpleCompatibleRankThreeData_simplifiedIndex?_eq_some
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (j : Fin n) :
    (simpleCompatibleRankThreeData D).simplifiedIndex? j = some j := by
  rw [CompatibleRankThreeData.simplifiedIndex?]
  simp only [CompatibleRankThreeData.isNonloop_iff_not_isLoop,
    simpleCompatibleRankThreeData_isLoop_false, not_false_eq_true, if_true,
    simpleCompatibleRankThreeData_simplifiedIndex]
  rfl

@[simp]
theorem simpleCompatibleRankThreeData_simplifiedImages
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (J : Finset (Fin n)) :
    (simpleCompatibleRankThreeData D).simplifiedImages J = J := by
  unfold CompatibleRankThreeData.simplifiedImages
  simp_rw [simpleCompatibleRankThreeData_simplifiedIndex?_eq_some]
  change (J.biUnion fun j : Fin n ↦ (some j).toFinset) = J
  ext x
  simp

theorem simpleCompatibleRankThreeData_initialParallel_iff
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (j : Fin n) :
    (simpleCompatibleRankThreeData D).IsInitialParallel j ↔ j.val = 0 := by
  simp [CompatibleRankThreeData.IsInitialParallel,
    CompatibleRankThreeData.middleStart, simpleCompatibleRankThreeData]

theorem simpleCompatibleRankThreeData_terminalParallel_iff
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (j : Fin n) :
    (simpleCompatibleRankThreeData D).IsTerminalParallel j ↔ j.val = n - 1 := by
  simp [CompatibleRankThreeData.IsTerminalParallel,
    CompatibleRankThreeData.terminalStart,
    CompatibleRankThreeData.rightLoopStart,
    CompatibleRankThreeData.middleStart, simpleCompatibleRankThreeData]
  omega

theorem simpleCompatibleRankThreeData_not_containsInitialParallelPair
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (J : Finset (Fin n)) :
    ¬(simpleCompatibleRankThreeData D).ContainsInitialParallelPair J := by
  unfold CompatibleRankThreeData.ContainsInitialParallelPair
  have hsubset : J.filter (simpleCompatibleRankThreeData D).IsInitialParallel ⊆
      {⟨0, by omega⟩} := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have hxzero := (simpleCompatibleRankThreeData_initialParallel_iff D x).1 hx.2
    have hxEq : x = (⟨0, by omega⟩ : Fin n) := by
      apply Fin.ext
      exact hxzero
    simp [hxEq]
  have hcard := Finset.card_le_card hsubset
  simp at hcard
  omega

theorem simpleCompatibleRankThreeData_not_containsTerminalParallelPair
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (J : Finset (Fin n)) :
    ¬(simpleCompatibleRankThreeData D).ContainsTerminalParallelPair J := by
  unfold CompatibleRankThreeData.ContainsTerminalParallelPair
  have hsubset : J.filter (simpleCompatibleRankThreeData D).IsTerminalParallel ⊆
      {⟨n - 1, by omega⟩} := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have hxlast := (simpleCompatibleRankThreeData_terminalParallel_iff D x).1 hx.2
    have hxEq : x = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      exact hxlast
    simp [hxEq]
  have hcard := Finset.card_le_card hsubset
  simp at hcard
  omega

/-- In the simple datum, collinearity means containment in one enlarged
zero-run interval. -/
theorem simpleCompatibleRankThreeData_simplifiedCollinear_iff
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (J : Finset (Fin n)) :
    (simpleCompatibleRankThreeData D).SimplifiedCollinear J ↔
      ∃ a, J ⊆ (firstCircuitRunInterval D a).points := by
  unfold CompatibleRankThreeData.SimplifiedCollinear
  constructor
  · rintro ⟨H, hH, hJH⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    exact ⟨a, hJH⟩
  · rintro ⟨a, hJa⟩
    exact ⟨firstCircuitRunInterval D a,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩, hJa⟩

/-- Triple nonbases of the simple datum are exactly triples contained in one
enlarged zero run. -/
theorem simpleCompatibleRankThreeData_tripleNonbasis_iff
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (J : Finset (Fin n)) :
    (simpleCompatibleRankThreeData D).TripleNonbasis J ↔
      J.card = 3 ∧ ∃ a, J ⊆ (firstCircuitRunInterval D a).points := by
  unfold CompatibleRankThreeData.TripleNonbasis
  rw [simpleCompatibleRankThreeData_simplifiedImages]
  have hmeet : ¬(simpleCompatibleRankThreeData D).MeetsLoops J := by
    rintro ⟨j, hj, hloop⟩
    exact simpleCompatibleRankThreeData_isLoop_false D j hloop
  rw [show (simpleCompatibleRankThreeData D).MeetsLoops J = False by
      exact propext (iff_false_intro hmeet),
    show (simpleCompatibleRankThreeData D).ContainsInitialParallelPair J = False by
      exact propext (iff_false_intro
        (simpleCompatibleRankThreeData_not_containsInitialParallelPair D J)),
    show (simpleCompatibleRankThreeData D).ContainsTerminalParallelPair J = False by
      exact propext (iff_false_intro
        (simpleCompatibleRankThreeData_not_containsTerminalParallelPair D J))]
  simp only [false_or]
  constructor
  · rintro ⟨hcard, hcard', hcoll⟩
    exact ⟨hcard, (simpleCompatibleRankThreeData_simplifiedCollinear_iff D J).1 hcoll⟩
  · rintro ⟨hcard, hcoll⟩
    exact ⟨hcard, ⟨hcard,
      (simpleCompatibleRankThreeData_simplifiedCollinear_iff D J).2 hcoll⟩⟩

@[simp]
theorem firstCircuitRunInterval_points
    {m n : ℕ} {h : 2 < n} {A : Matrix (Fin m) (Fin n) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A) (a : Fin D.runCount) :
    (firstCircuitRunInterval D a).points = runHyperplane h D.runs a := by
  rfl

/-- The simple compatible datum exactly represents the column matroid of its
three-row first-circuit configuration. -/
theorem simpleCompatibleRankThreeData_supportRealization
    {n : ℕ} {h : 2 < n} {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A)
    (D : FirstCircuitIntervalData (p := 1) h A) :
    CompatibleTripleSupportRealization
      (simpleCompatibleRankThreeData D) (columnMatroid A) := by
  refine ⟨columnMatroid_ground A, ?_, ?_⟩
  · obtain ⟨cols, hcols⟩ := hfull
    refine ⟨Set.range cols, ?_, ?_⟩
    · exact (columnMatroid_isBase_range_iff A cols).2 hcols
    · rw [Set.ncard_range_of_injective cols.injective]
      simp
  · intro J hJ
    let cols : Fin 3 ↪o Fin n := J.orderEmbOfFin hJ
    have hrange : Set.range cols = (J : Set (Fin n)) := by
      rw [Finset.range_orderEmbOfFin]
    rw [← hrange, columnMatroid_isBase_range_iff]
    have hcontained : ∀ a,
        J ⊆ (firstCircuitRunInterval D a).points ↔
          ∀ i, cols i ∈ runHyperplane h D.runs a := by
      intro a
      constructor
      · intro hsubset i
        rw [← firstCircuitRunInterval_points]
        apply hsubset
        exact Finset.orderEmbOfFin_mem J hJ i
      · intro hall x hx
        rw [firstCircuitRunInterval_points]
        have hxSet : x ∈ (J : Set (Fin n)) := by simpa using hx
        rw [← hrange] at hxSet
        obtain ⟨i, rfl⟩ := hxSet
        exact hall i
    rw [simpleCompatibleRankThreeData_tripleNonbasis_iff, hJ]
    norm_num only
    constructor
    · intro hminor hnonbasis
      obtain ⟨htrue, a, hJa⟩ := hnonbasis
      have hdep : ¬(columnMatroid A).Indep (Set.range cols) :=
        (D.dependent_iff_interval cols).2 ⟨a, (hcontained a).1 hJa⟩
      apply hdep
      rw [columnMatroid_indep_range_iff,
        ← orderedMinor_ne_zero_iff_linearIndependent_columns]
      exact hminor
    · intro hnonbasis
      by_contra hminor
      have hdep : ¬(columnMatroid A).Indep (Set.range cols) := by
        rw [columnMatroid_indep_range_iff,
          ← orderedMinor_ne_zero_iff_linearIndependent_columns]
        exact fun hne ↦ hne hminor
      obtain ⟨a, hall⟩ := (D.dependent_iff_interval cols).1 hdep
      exact hnonbasis ⟨True.intro, a, (hcontained a).2 hall⟩

/-- The simple first-circuit configuration therefore has compatible
rank-three support in the sense required by Paper A's realization theorem. -/
theorem simple_hasCompatibleRankThreeSupport
    {n : ℕ} {h : 2 < n} {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A)
    (D : FirstCircuitIntervalData (p := 1) h A) :
    HasCompatibleRankThreeSupport (columnMatroid A) :=
  ⟨simpleCompatibleRankThreeData D,
    simpleCompatibleRankThreeData_supportRealization hfull D⟩

/-- A full-rank, pairwise independent, three-row TNN configuration has a
Toeplitz realization with exactly the same column matroid. -/
theorem simpleThreeRow_exists_toeplitzRealization
    {n : ℕ} (hn : 3 ≤ n) {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (huniform : ∀ cols : Fin 2 ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin 2 ↦ A.col (cols j)))
    (hfull : HasFullRowRank A) :
    HasTNNRankThreeToeplitzRepresentation (columnMatroid A) := by
  have hpn : 2 < n := by omega
  let P : Matrix (Fin 3) (Fin 3) ℝ := threeRowPositiveCompression 3
  have hP : TotallyPositive P := threeRowPositiveCompression_totallyPositive 3
  have hfullCopy := hfull
  obtain ⟨basis, hbasis⟩ := hfullCopy
  have hbasisInd : LinearIndependent ℝ
      (fun j : Fin 3 ↦ A.col (basis j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns A basis).mp hbasis
  obtain ⟨D⟩ := exists_firstCircuitIntervalData hpn hA hP huniform
    ⟨basis, hbasisInd⟩
  apply hasTNNRankThreeToeplitzRepresentation_of_hasCompatibleRankThreeSupport
  exact simple_hasCompatibleRankThreeSupport hfull D

/-! ## Inflation by loops and endpoint parallel classes -/

/-- Numerical block counts for inflating a simple rank-three core. -/
structure RankThreeInflationCounts (n s : ℕ) where
  leftLoops : ℕ
  rightLoops : ℕ
  initialClass : ℕ
  terminalClass : ℕ
  initialClass_pos : 0 < initialClass
  terminalClass_pos : 0 < terminalClass
  simplified_ge_three : 3 ≤ s
  ground_eq : leftLoops + initialClass + (s - 2) + terminalClass + rightLoops = n
  initial_singleton_of_loops : 0 < leftLoops → initialClass = 1
  terminal_singleton_of_loops : 0 < rightLoops → terminalClass = 1

/-- Inflate a simple compatible datum by loop blocks and endpoint parallel
classes, assuming precisely the two endpoint-protection facts. -/
def inflateSimpleCompatibleRankThreeData
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (C : RankThreeInflationCounts n s)
    (hleft : 0 < C.leftLoops ∨ 1 < C.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < C.rightLoops ∨ 1 < C.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s) :
    CompatibleRankThreeData n where
  leftLoopCount := C.leftLoops
  rightLoopCount := C.rightLoops
  initialParallelSize := C.initialClass
  terminalParallelSize := C.terminalClass
  simplifiedSize := s
  initialParallelSize_pos := C.initialClass_pos
  terminalParallelSize_pos := C.terminalClass_pos
  simplifiedSize_ge_three := C.simplified_ge_three
  groundSize_eq := C.ground_eq
  initialParallel_singleton_of_leftLoops := C.initial_singleton_of_loops
  terminalParallel_singleton_of_rightLoops := C.terminal_singleton_of_loops
  intervals := firstCircuitRunIntervals D
  interval_large := (simpleCompatibleRankThreeData D).interval_large
  intervals_separated := (simpleCompatibleRankThreeData D).intervals_separated
  initial_endpoint_protected := hleft
  terminal_endpoint_protected := hright
  interval_not_whole := (simpleCompatibleRankThreeData D).interval_not_whole

/-- Endpoint independence of the first and last three simplified columns
supplies exactly the protection hypotheses required for inflation. -/
def inflateSimpleCompatibleRankThreeDataOfEndpointIndependence
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (hA : TotallyNonnegative A)
    (hpair : ∀ cols : Fin 2 ↪o Fin s,
      LinearIndependent ℝ (fun j : Fin 2 ↦ A.col (cols j)))
    (D : FirstCircuitIntervalData (p := 1) h A)
    (C : RankThreeInflationCounts n s)
    (hfirst : 0 < C.leftLoops ∨ 1 < C.initialClass →
      LinearIndependent ℝ
        (fun j : Fin 3 ↦ A.col (consecutiveThreeColumns 0 (by omega) j)))
    (hlast : 0 < C.rightLoops ∨ 1 < C.terminalClass →
      LinearIndependent ℝ
        (fun j : Fin 3 ↦ A.col (lastThreeColumns s (by omega) j))) :
    CompatibleRankThreeData n := by
  apply inflateSimpleCompatibleRankThreeData D C
  · intro hprotected H hH hleft
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    let F : Set (Fin s) := runHyperplane h D.runs a
    have hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid A) F :=
      (isLargeFirstCircuitFlat_iff_runHyperplane hpair D F).2 ⟨a, rfl⟩
    have hnot := first_not_mem_large_rankTwo_flat (by omega) hA hpair
      (hfirst hprotected) hF
    apply hnot
    change (⟨0, by omega⟩ : Fin s) ∈ runHyperplane h D.runs a
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftVal : (D.runs.left a).val = 0 := by
        simpa [firstCircuitRunInterval, runLeftColumn] using hleft
      omega
    · apply Fin.mk_le_mk.mpr
      change 0 ≤ (D.runs.right a).val + 2
      omega
  · intro hprotected H hH hright
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hH
    let F : Set (Fin s) := runHyperplane h D.runs a
    have hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid A) F :=
      (isLargeFirstCircuitFlat_iff_runHyperplane hpair D F).2 ⟨a, rfl⟩
    have hnot := last_not_mem_large_rankTwo_flat (by omega) hA hpair
      (hlast hprotected) hF
    apply hnot
    change (⟨s - 1, by omega⟩ : Fin s) ∈ runHyperplane h D.runs a
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftBound := (D.runs.left a).isLt
      omega
    · apply Fin.mk_le_mk.mpr
      have hrightVal : (D.runs.right a).val + 2 + 1 = s := by
        simpa [firstCircuitRunInterval, runRightColumn] using hright
      omega

/-! ### Elementary formulas for inflated data -/

/-- The nonloops of an inflated datum are exactly the raw indices between
the two loop blocks. -/
theorem inflateSimpleCompatibleRankThreeData_isNonloop_iff
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (K : RankThreeInflationCounts n s)
    (hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s)
    (j : Fin n) :
    (inflateSimpleCompatibleRankThreeData D K hleft hright).IsNonloop j ↔
      K.leftLoops ≤ j.val ∧ j.val < n - K.rightLoops := by
  unfold CompatibleRankThreeData.IsNonloop
  change K.leftLoops ≤ j.val ∧
      j.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass ↔ _
  have hground := K.ground_eq
  omega

/-- The numeric simplification map of an inflated datum is the expected
piecewise block-coordinate map. -/
theorem inflateSimpleCompatibleRankThreeData_simplifiedIndexNat
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (K : RankThreeInflationCounts n s)
    (hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s)
    (j : Fin n) :
    (inflateSimpleCompatibleRankThreeData D K hleft hright).simplifiedIndexNat j =
      if j.val < K.leftLoops + K.initialClass then 0
      else if j.val < K.leftLoops + K.initialClass + (s - 2) then
        j.val - (K.leftLoops + K.initialClass) + 1
      else s - 1 := by
  rfl

/-- Two distinct nonloops with the same inflated simplification index must
belong to one of the two endpoint parallel classes.  Every middle class is a
singleton by construction. -/
theorem inflateSimpleCompatibleRankThreeData_equal_index_is_endpoint
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (K : RankThreeInflationCounts n s)
    (hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s)
    {i j : Fin n} (hij : i < j)
    (hi : (inflateSimpleCompatibleRankThreeData D K hleft hright).IsNonloop i)
    (hj : (inflateSimpleCompatibleRankThreeData D K hleft hright).IsNonloop j)
    (heq : (inflateSimpleCompatibleRankThreeData D K hleft hright).simplifiedIndex i =
      (inflateSimpleCompatibleRankThreeData D K hleft hright).simplifiedIndex j) :
    ((inflateSimpleCompatibleRankThreeData D K hleft hright).IsInitialParallel i ∧
        (inflateSimpleCompatibleRankThreeData D K hleft hright).IsInitialParallel j) ∨
      ((inflateSimpleCompatibleRankThreeData D K hleft hright).IsTerminalParallel i ∧
        (inflateSimpleCompatibleRankThreeData D K hleft hright).IsTerminalParallel j) := by
  have heqVal := congrArg Fin.val heq
  change K.leftLoops ≤ i.val ∧
      i.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass at hi
  change K.leftLoops ≤ j.val ∧
      j.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass at hj
  change (if i.val < K.leftLoops + K.initialClass then 0
      else if i.val < K.leftLoops + K.initialClass + (s - 2) then
        i.val - (K.leftLoops + K.initialClass) + 1
      else s - 1) =
    (if j.val < K.leftLoops + K.initialClass then 0
      else if j.val < K.leftLoops + K.initialClass + (s - 2) then
        j.val - (K.leftLoops + K.initialClass) + 1
      else s - 1) at heqVal
  change
    ((K.leftLoops ≤ i.val ∧ i.val < K.leftLoops + K.initialClass) ∧
      (K.leftLoops ≤ j.val ∧ j.val < K.leftLoops + K.initialClass)) ∨
    ((K.leftLoops + K.initialClass + (s - 2) ≤ i.val ∧
        i.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass) ∧
      (K.leftLoops + K.initialClass + (s - 2) ≤ j.val ∧
        j.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass))
  split_ifs at heqVal <;> omega

/-- Every element of the initial endpoint block maps to simplified index
zero. -/
theorem inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_zero
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (K : RankThreeInflationCounts n s)
    (hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s)
    {j : Fin n}
    (hj : (inflateSimpleCompatibleRankThreeData D K hleft hright).IsInitialParallel j) :
    (inflateSimpleCompatibleRankThreeData D K hleft hright).simplifiedIndex j =
      (⟨0, by omega⟩ : Fin s) := by
  apply Fin.ext
  change (if j.val < K.leftLoops + K.initialClass then 0
      else if j.val < K.leftLoops + K.initialClass + (s - 2) then
        j.val - (K.leftLoops + K.initialClass) + 1
      else s - 1) = 0
  change K.leftLoops ≤ j.val ∧ j.val < K.leftLoops + K.initialClass at hj
  rw [if_pos hj.2]

/-- Every element of the terminal endpoint block maps to the last
simplified index. -/
theorem inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_last
    {m s n : ℕ} {h : 2 < s} {A : Matrix (Fin m) (Fin s) ℝ}
    (D : FirstCircuitIntervalData (p := 1) h A)
    (K : RankThreeInflationCounts n s)
    (hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.right.val + 1 ≠ s)
    {j : Fin n}
    (hj : (inflateSimpleCompatibleRankThreeData D K hleft hright).IsTerminalParallel j) :
    (inflateSimpleCompatibleRankThreeData D K hleft hright).simplifiedIndex j =
      (⟨s - 1, by omega⟩ : Fin s) := by
  apply Fin.ext
  change (if j.val < K.leftLoops + K.initialClass then 0
      else if j.val < K.leftLoops + K.initialClass + (s - 2) then
        j.val - (K.leftLoops + K.initialClass) + 1
      else s - 1) = s - 1
  change K.leftLoops + K.initialClass + (s - 2) ≤ j.val ∧
      j.val < K.leftLoops + K.initialClass + (s - 2) + K.terminalClass at hj
  rw [if_neg (by omega), if_neg (by omega)]

/-- Canonical loop and endpoint-class counts extracted from the three-row
compression of an arbitrary-rank Toeplitz matrix. -/
def threeRowCompressionInflationCounts
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) :
    let C := compressedThreeRowToeplitzMatrix m n a
    RankThreeInflationCounts n (simplificationSize C) := by
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C := threeRowPositiveCompression_fullRowRank hm hA hfull
  let s : ℕ := simplificationSize C
  have hs : 3 ≤ s := three_le_simplificationSize_of_hasFullRowRank
    (hC.tnUpTo 2) hCfull
  let r0 : Fin n := simplificationEmbedding C ⟨0, by omega⟩
  let r1 : Fin n := simplificationEmbedding C ⟨1, by omega⟩
  let rLast : Fin n := simplificationEmbedding C ⟨s - 1, by omega⟩
  let z : Fin n := lastNonloopIndex C hCfull
  let leftLoops := r0.val
  let rightLoops := n - (z.val + 1)
  let initialClass := r1.val - r0.val
  let terminalClass := z.val + 1 - rLast.val
  have hinternal : ∀ k : ℕ, (hks : k < s) → 1 ≤ k →
      (simplificationEmbedding C ⟨k, hks⟩).val = r1.val + (k - 1) := by
    intro k hks hk1
    induction k, hk1 using Nat.le_induction with
    | base => simp [r1]
    | succ k hk1 ih =>
        have hks' : k < s := by omega
        have hstep := threeRowCompression_internal_representatives_consecutive
          hm hA (q := (⟨k, hks'⟩ : Fin s)) hk1 hks
        have ih' := ih hks'
        change (simplificationEmbedding C ⟨k + 1, hks⟩).val =
          (simplificationEmbedding C ⟨k, hks'⟩).val + 1 at hstep
        rw [hstep, ih']
        omega
  have hrLastFormula : rLast.val = r1.val + (s - 2) := by
    have h := hinternal (s - 1) (by omega) (by omega)
    have hindex : (⟨s - 1, by omega⟩ : Fin s) = ⟨s - 1, by omega⟩ := rfl
    simpa [rLast] using h
  have hInitialPos : 0 < initialClass := by
    have h01 := (simplificationEmbedding C).strictMono
      (show (⟨0, by omega⟩ : Fin s) < ⟨1, by omega⟩ by
        apply Fin.mk_lt_mk.mpr
        omega)
    dsimp only [initialClass, r0, r1]
    omega
  have hrLastz : rLast ≤ z := nonloop_le_lastNonloopIndex hCfull
    (simplificationEmbedding_not_isLoop C _)
  have hTerminalPos : 0 < terminalClass := by
    dsimp only [terminalClass]
    omega
  have hGround : leftLoops + initialClass + (s - 2) + terminalClass + rightLoops = n := by
    dsimp only [leftLoops, initialClass, terminalClass, rightLoops]
    rw [hrLastFormula]
    have hzBound := z.isLt
    omega
  have hInitialSingleton : 0 < leftLoops → initialClass = 1 := by
    intro hleft
    by_contra hsize
    have hsizeTwo : 2 ≤ initialClass := by omega
    let prev : Fin n := ⟨r0.val - 1, by omega⟩
    have hprevLt : prev < r0 := by
      apply Fin.mk_lt_mk.mpr
      change r0.val - 1 < r0.val
      dsimp only [leftLoops] at hleft
      omega
    have hprevC : IsLoop C prev := by
      apply isLoop_of_lt_first_simplificationEmbedding (A := C) (by omega)
      have hfirstEq : simplificationEmbedding C ⟨0, by omega⟩ = r0 := rfl
      rwa [hfirstEq]
    have hprevA : IsLoop A prev :=
      (isLoop_threeRowPositiveCompression_iff hA prev).mp hprevC
    let next : Fin n := ⟨r0.val + 1, by
      have hr1Bound := r1.isLt
      dsimp only [initialClass] at hsizeTwo
      omega⟩
    have hnextLt : next < r1 := by
      apply Fin.mk_lt_mk.mpr
      change r0.val + 1 < r1.val
      dsimp only [initialClass] at hsizeTwo
      omega
    have hr0A : ¬IsLoop A r0 :=
      (isLoop_threeRowPositiveCompression_iff hA r0).not.mp
        (by simpa [r0] using simplificationEmbedding_not_isLoop C ⟨0, by omega⟩)
    have hr1A : ¬IsLoop A r1 :=
      (isLoop_threeRowPositiveCompression_iff hA r1).not.mp
        (by simpa [r1] using simplificationEmbedding_not_isLoop C ⟨1, by omega⟩)
    have hnextA : ¬IsLoop A next :=
      toeplitzMatrix_nonloop_interval (by omega : 2 ≤ m)
        (by have hr1Bound := r1.isLt; omega) hA
        (by apply Fin.mk_le_mk.mpr; change r0.val ≤ r0.val + 1; omega)
        hnextLt.le hr0A hr1A
    have hnextC : ¬IsLoop C next :=
      (isLoop_threeRowPositiveCompression_iff hA next).not.mpr hnextA
    have hparC := columnsPositivelyParallel_first_of_lt_secondRepresentative
      (A := C) (by omega) hnextLt hnextC
    change ColumnsPositivelyParallel C r0 next at hparC
    have hr0next : r0 < next := by
      apply Fin.mk_lt_mk.mpr
      change r0.val < r0.val + 1
      omega
    have hparA := (columnsPositivelyParallel_threeRowCompression_iff hA
      hr0next hr0A hnextA).1 hparC
    have hr0Pos : 1 ≤ r0.val := by
      dsimp only [leftLoops] at hleft
      omega
    have hnot := toeplitzMatrix_not_parallel_after_loop
      (by omega : 2 ≤ m) hr0Pos next.isLt hA hprevA hr0A
    change ¬ColumnsPositivelyParallel A r0 next at hnot
    exact hnot hparA
  have hTerminalSingleton : 0 < rightLoops → terminalClass = 1 := by
    intro hright
    by_contra hsize
    have hsizeTwo : 2 ≤ terminalClass := by omega
    let next : Fin n := ⟨z.val + 1, by
      dsimp only [rightLoops] at hright
      have hzBound := z.isLt
      omega⟩
    have hnextC : IsLoop C next := by
      apply isLoop_of_lastNonloopIndex_lt hCfull
      apply Fin.mk_lt_mk.mpr
      change z.val < z.val + 1
      omega
    have hnextA : IsLoop A next :=
      (isLoop_threeRowPositiveCompression_iff hA next).mp hnextC
    let prev : Fin n := ⟨z.val - 1, by
      have hzLast := hrLastz
      dsimp only [terminalClass] at hsizeTwo
      omega⟩
    have hlastC : ¬IsLoop C z := by
      simpa [z] using lastNonloopIndex_nonloop C hCfull
    have hrLastA : ¬IsLoop A rLast :=
      (isLoop_threeRowPositiveCompression_iff hA rLast).not.mp
        (by simpa [rLast, s] using
          simplificationEmbedding_not_isLoop C ⟨s - 1, by omega⟩)
    have hzA : ¬IsLoop A z :=
      (isLoop_threeRowPositiveCompression_iff hA z).not.mp hlastC
    have hrLastPrev : rLast ≤ prev := by
      apply Fin.mk_le_mk.mpr
      change rLast.val ≤ z.val - 1
      dsimp only [terminalClass] at hsizeTwo
      omega
    have hprevZ : prev ≤ z := by
      apply Fin.mk_le_mk.mpr
      change z.val - 1 ≤ z.val
      omega
    have hprevA : ¬IsLoop A prev :=
      toeplitzMatrix_nonloop_interval (by omega : 2 ≤ m)
        (by have hzBound := z.isLt; omega) hA hrLastPrev hprevZ hrLastA hzA
    have hprevC : ¬IsLoop C prev :=
      (isLoop_threeRowPositiveCompression_iff hA prev).not.mpr hprevA
    have hparC := columnsPositivelyParallel_last_of_lastRepresentative_le
      (hC.tnUpTo 2) (by omega) (j := prev) hrLastPrev hprevC
    change ColumnsPositivelyParallel C rLast prev at hparC
    have hparC' : ColumnsPositivelyParallel C prev z := by
      have hlastToZ := columnsPositivelyParallel_last_of_lastRepresentative_le
        (hC.tnUpTo 2) (by omega) (j := z) (by exact hrLastz) hlastC
      change ColumnsPositivelyParallel C rLast z at hlastToZ
      exact columnsPositivelyParallel_trans
        (columnsPositivelyParallel_symm hparC) hlastToZ
    have hprevz : prev < z := by
      apply Fin.mk_lt_mk.mpr
      change z.val - 1 < z.val
      omega
    have hparA := (columnsPositivelyParallel_threeRowCompression_iff hA
      hprevz hprevA hzA).1 hparC'
    have hnot := toeplitzMatrix_not_parallel_before_loop
      (by omega : 2 ≤ m) (by
        have hrLastBound := rLast.isLt
        dsimp only [terminalClass] at hsizeTwo
        omega) next.isLt hA hzA hnextA
    change ¬ColumnsPositivelyParallel A prev z at hnot
    exact hnot hparA
  exact
    { leftLoops := leftLoops
      rightLoops := rightLoops
      initialClass := initialClass
      terminalClass := terminalClass
      initialClass_pos := hInitialPos
      terminalClass_pos := hTerminalPos
      simplified_ge_three := hs
      ground_eq := hGround
      initial_singleton_of_loops := hInitialSingleton
      terminal_singleton_of_loops := hTerminalSingleton }

/-- The simplification of the three-row compression is a full-rank simple
TNN configuration and therefore has first-circuit interval data. -/
theorem exists_threeRowCompression_coreIntervalData
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) :
    let C := compressedThreeRowToeplitzMatrix m n a
    ∃ hsn : 2 < simplificationSize C,
      Nonempty (FirstCircuitIntervalData (p := 1) hsn (simplifiedMatrix C)) := by
  dsimp only
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let S : Matrix (Fin 3) (Fin (simplificationSize C)) ℝ := simplifiedMatrix C
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C := threeRowPositiveCompression_fullRowRank hm hA hfull
  have hs : 3 ≤ simplificationSize C :=
    three_le_simplificationSize_of_hasFullRowRank (hC.tnUpTo 2) hCfull
  have hsn : 2 < simplificationSize C := by omega
  have hS : TotallyNonnegative S := hC.submatrix (allRows 3) (simplificationEmbedding C)
  have hSfull : HasFullRowRank S :=
    (hasFullRowRank_iff_simplifiedMatrix (hC.tnUpTo 2)).1 hCfull
  have hpair : ∀ cols : Fin 2 ↪o Fin (simplificationSize C),
      LinearIndependent ℝ (fun j : Fin 2 ↦ S.col (cols j)) := by
    intro cols
    have hpq : cols 0 < cols 1 := cols.strictMono (by decide)
    by_contra hdep
    have hcolsEq : cols = twoPointOrderEmbedding (cols 0) (cols 1) hpq := by
      apply RelEmbedding.ext
      intro t
      fin_cases t <;> rfl
    rw [hcolsEq] at hdep
    have hparallel := columnsPositivelyParallel_of_pair_not_independent
      hS hpq (simplifiedMatrix_not_isLoop C _) (simplifiedMatrix_not_isLoop C _) hdep
    have heq := (simplifiedMatrix_columnsPositivelyParallel_iff C _ _).1 hparallel
    exact (ne_of_lt hpq) heq
  obtain ⟨basis, hbasis⟩ := hSfull
  have hbasisInd : LinearIndependent ℝ
      (fun j : Fin 3 ↦ S.col (basis j)) :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns S basis).1 hbasis
  refine ⟨hsn, ?_⟩
  exact exists_firstCircuitIntervalData hsn hS
    (threeRowPositiveCompression_totallyPositive 3) hpair ⟨basis, hbasisInd⟩

/-! ## Raw block and simplification-index formulas -/

/-- The canonical inflation counts recover exactly the nonloop interval of
the three-row compression. -/
theorem threeRowCompression_nonloop_iff_inflationCounts
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) (j : Fin n) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    ¬IsLoop C j ↔ K.leftLoops ≤ j.val ∧ j.val < n - K.rightLoops := by
  dsimp only
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let K : RankThreeInflationCounts n (simplificationSize C) :=
    threeRowCompressionInflationCounts hm hA hfull
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C := threeRowPositiveCompression_fullRowRank hm hA hfull
  have hs : 3 ≤ simplificationSize C :=
    three_le_simplificationSize_of_hasFullRowRank (hC.tnUpTo 2) hCfull
  let r0 : Fin n := simplificationEmbedding C ⟨0, by omega⟩
  let z : Fin n := lastNonloopIndex C hCfull
  have hKleft : K.leftLoops = r0.val := by rfl
  have hKright : K.rightLoops = n - (z.val + 1) := by rfl
  rw [hKleft, hKright]
  constructor
  · intro hj
    have hfirstLe : r0 ≤ j := by
      exact first_simplificationEmbedding_le_nonloop (A := C) (by omega) hj
    have hjlast : j ≤ z := nonloop_le_lastNonloopIndex hCfull hj
    constructor
    · exact Fin.mk_le_mk.mp hfirstLe
    · change j.val < n - (n - (z.val + 1))
      have hzBound := z.isLt
      have hjzVal := Fin.mk_le_mk.mp hjlast
      omega
  · rintro ⟨hr0j, hjz⟩
    change r0.val ≤ j.val at hr0j
    change j.val < n - (n - (z.val + 1)) at hjz
    have hr0C : ¬IsLoop C r0 := simplificationEmbedding_not_isLoop C _
    have hzC : ¬IsLoop C z := lastNonloopIndex_nonloop C hCfull
    have hr0A : ¬IsLoop A r0 :=
      (isLoop_threeRowPositiveCompression_iff hA r0).not.mp hr0C
    have hzA : ¬IsLoop A z :=
      (isLoop_threeRowPositiveCompression_iff hA z).not.mp hzC
    have hr0j : r0 ≤ j := Fin.mk_le_mk.mpr hr0j
    have hjz' : j ≤ z := by
      apply Fin.mk_le_mk.mpr
      change j.val ≤ z.val
      dsimp only [z] at hjz ⊢
      have hzBound := (lastNonloopIndex C hCfull).isLt
      omega
    have hjA := toeplitzMatrix_nonloop_interval (by omega : 2 ≤ m)
      (by have hn := three_le_of_hasFullRowRank hCfull; omega) hA hr0j hjz' hr0A hzA
    exact (isLoop_threeRowPositiveCompression_iff hA j).not.mpr hjA

/-- Piecewise formula for the canonical simplification class index, in the
same coordinates used by the inflated compatible datum. -/
theorem threeRowCompression_classIndex_formula
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (j : Fin n) (hj : ¬IsLoop (compressedThreeRowToeplitzMatrix m n a) j) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    (simplificationClassIndex C j hj).val =
      if j.val < K.leftLoops + K.initialClass then 0
      else if j.val < K.leftLoops + K.initialClass +
          (simplificationSize C - 2) then
        j.val - (K.leftLoops + K.initialClass) + 1
      else simplificationSize C - 1 := by
  dsimp only
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let K : RankThreeInflationCounts n (simplificationSize C) :=
    threeRowCompressionInflationCounts hm hA hfull
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C := threeRowPositiveCompression_fullRowRank hm hA hfull
  let s : ℕ := simplificationSize C
  have hs : 3 ≤ s := three_le_simplificationSize_of_hasFullRowRank
    (hC.tnUpTo 2) hCfull
  let q0 : Fin s := ⟨0, by omega⟩
  let q1 : Fin s := ⟨1, by omega⟩
  let qLast : Fin s := ⟨s - 1, by omega⟩
  let r0 : Fin n := simplificationEmbedding C q0
  let r1 : Fin n := simplificationEmbedding C q1
  let rLast : Fin n := simplificationEmbedding C qLast
  have hKleft : K.leftLoops = r0.val := by rfl
  have hKinit : K.initialClass = r1.val - r0.val := by rfl
  have hr0r1 : r0.val < r1.val := by
    have hlt := (simplificationEmbedding C).strictMono
      (show q0 < q1 by apply Fin.mk_lt_mk.mpr; omega)
    exact hlt
  have hmiddle : K.leftLoops + K.initialClass = r1.val := by
    rw [hKleft, hKinit]
    omega
  have hrLastFormula : rLast.val = r1.val + (s - 2) := by
    have hkLastOne : 1 ≤ s - 1 := by omega
    have hkLastBound :
        s - 1 < simplificationSize (compressedThreeRowToeplitzMatrix m n a) := by
      simpa [C, s] using (show s - 1 < s by omega)
    have h := threeRowCompression_internal_simplificationEmbedding_val
      hm hA (k := s - 1) hkLastOne hkLastBound
    simpa [C, s, r1, rLast, q1, qLast] using h
  have hterminal : K.leftLoops + K.initialClass + (s - 2) = rLast.val := by
    rw [hmiddle, hrLastFormula]
  change (simplificationClassIndex C j hj).val = _
  rw [hmiddle]
  change (simplificationClassIndex C j hj).val =
    if j.val < r1.val then 0
    else if j.val < r1.val + (s - 2) then j.val - r1.val + 1
    else s - 1
  split_ifs with hjFirst hjMiddle
  · have hpar := columnsPositivelyParallel_first_of_lt_secondRepresentative
      (A := C) (by omega) (show j < r1 by exact Fin.mk_lt_mk.mpr hjFirst) hj
    change ColumnsPositivelyParallel C r0 j at hpar
    have hclass := (simplificationClassIndex_eq_iff C j hj q0).2 hpar
    exact congrArg Fin.val hclass
  · let kval : ℕ := j.val - r1.val + 1
    have hk1 : 1 ≤ kval := by dsimp only [kval]; omega
    have hks : kval < s := by
      dsimp only [kval]
      omega
    let qk : Fin s := ⟨kval, hks⟩
    have hsigma : simplificationEmbedding C qk = j := by
      apply Fin.ext
      have hformula := threeRowCompression_internal_simplificationEmbedding_val
        hm hA (k := kval) hk1 hks
      change (simplificationEmbedding C qk).val = j.val
      have hformula' : (simplificationEmbedding C qk).val =
          r1.val + (kval - 1) := by
        simpa [C, qk, r1, q1] using hformula
      rw [hformula']
      dsimp only [kval]
      omega
    have hclass : simplificationClassIndex C j hj = qk := by
      apply (simplificationClassIndex_eq_iff C j hj qk).2
      rw [hsigma]
      exact columnsPositivelyParallel_refl C j
    rw [hclass]
  · have hrLastj : rLast ≤ j := by
      have hval : rLast.val ≤ j.val := by
        rw [hrLastFormula]
        omega
      exact Fin.mk_le_mk.mpr hval
    have hpar := columnsPositivelyParallel_last_of_lastRepresentative_le
      (hC.tnUpTo 2) (by omega) hrLastj hj
    change ColumnsPositivelyParallel C rLast j at hpar
    have hclass := (simplificationClassIndex_eq_iff C j hj qLast).2 hpar
    rw [hclass]

/-- For any endpoint-protected inflation of the canonical simple core, the
datum's nonloop predicate is the actual nonloop predicate of the compressed
three-row matrix. -/
theorem threeRowCompression_inflated_isNonloop_iff
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a))
    (j : Fin n) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    let E := inflateSimpleCompatibleRankThreeData D K hleft hright
    E.IsNonloop j ↔ ¬IsLoop C j := by
  dsimp only
  exact (inflateSimpleCompatibleRankThreeData_isNonloop_iff
    D (threeRowCompressionInflationCounts hm hA hfull) hleft hright j).trans
      (threeRowCompression_nonloop_iff_inflationCounts hm hA hfull j).symm

/-- The inflated datum's simplification map is exactly the intrinsic
simplification-class map of the compressed matrix. -/
theorem threeRowCompression_inflated_simplifiedIndex_eq
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a))
    (j : Fin n) (hj : ¬IsLoop (compressedThreeRowToeplitzMatrix m n a) j) :
    let K := threeRowCompressionInflationCounts hm hA hfull
    let E := inflateSimpleCompatibleRankThreeData D K hleft hright
    E.simplifiedIndex j =
      simplificationClassIndex (compressedThreeRowToeplitzMatrix m n a) j hj := by
  dsimp only
  apply Fin.ext
  change (inflateSimpleCompatibleRankThreeData D
    (threeRowCompressionInflationCounts hm hA hfull) hleft hright).simplifiedIndexNat j = _
  rw [inflateSimpleCompatibleRankThreeData_simplifiedIndexNat,
    threeRowCompression_classIndex_formula hm hA hfull j hj]

/-- On a loop-free raw triple, inflated simplified images are exactly the
three intrinsic simplification-class indices. -/
theorem threeRowCompression_inflated_simplifiedImages_triple
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a))
    {i j k : Fin n}
    (hi : ¬IsLoop (compressedThreeRowToeplitzMatrix m n a) i)
    (hj : ¬IsLoop (compressedThreeRowToeplitzMatrix m n a) j)
    (hk : ¬IsLoop (compressedThreeRowToeplitzMatrix m n a) k) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    let E := inflateSimpleCompatibleRankThreeData D K hleft hright
    E.simplifiedImages {i, j, k} =
      {simplificationClassIndex C i hi,
        simplificationClassIndex C j hj,
        simplificationClassIndex C k hk} := by
  classical
  dsimp only
  let C := compressedThreeRowToeplitzMatrix m n a
  let K := threeRowCompressionInflationCounts hm hA hfull
  let E := inflateSimpleCompatibleRankThreeData D K hleft hright
  have hiE : E.IsNonloop i :=
    (threeRowCompression_inflated_isNonloop_iff hm hA hfull
      D hleft hright i).2 hi
  have hjE : E.IsNonloop j :=
    (threeRowCompression_inflated_isNonloop_iff hm hA hfull
      D hleft hright j).2 hj
  have hkE : E.IsNonloop k :=
    (threeRowCompression_inflated_isNonloop_iff hm hA hfull
      D hleft hright k).2 hk
  have hiEq := threeRowCompression_inflated_simplifiedIndex_eq
    hm hA hfull D hleft hright i hi
  have hjEq := threeRowCompression_inflated_simplifiedIndex_eq
    hm hA hfull D hleft hright j hj
  have hkEq := threeRowCompression_inflated_simplifiedIndex_eq
    hm hA hfull D hleft hright k hk
  dsimp only at hiEq hjEq hkEq
  change E.simplifiedIndex i = simplificationClassIndex C i hi at hiEq
  change E.simplifiedIndex j = simplificationClassIndex C j hj at hjEq
  change E.simplifiedIndex k = simplificationClassIndex C k hk at hkEq
  change E.simplifiedImages {i, j, k} = _
  calc
    E.simplifiedImages {i, j, k} =
        {simplificationClassIndex C j hj,
          simplificationClassIndex C i hi,
          simplificationClassIndex C k hk} := by
      unfold CompatibleRankThreeData.simplifiedImages
      simp [CompatibleRankThreeData.simplifiedIndex?, hiE, hjE, hkE,
        hiEq, hjEq, hkEq]
      rfl
    _ = _ := by exact Finset.insert_comm _ _ _

/-- The inflated interval datum detects exactly the zero maximal minors of
the original three-row compression.  This is the raw-support identification
step: loops, repeated endpoint classes, and dependent triples in the simple
core are treated separately. -/
theorem threeRowCompression_inflated_tripleNonbasis_iff
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a))
    (J : Finset (Fin n)) (hJ : J.card = 3) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    let E := inflateSimpleCompatibleRankThreeData D K hleft hright
    E.TripleNonbasis J ↔
      orderedMinor C (allRows 3) (J.orderEmbOfFin hJ) = 0 := by
  classical
  dsimp only
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let S : Matrix (Fin 3) (Fin (simplificationSize C)) ℝ := simplifiedMatrix C
  let K := threeRowCompressionInflationCounts hm hA hfull
  let E := inflateSimpleCompatibleRankThreeData D K hleft hright
  let cols : Fin 3 ↪o Fin n := J.orderEmbOfFin hJ
  let i := cols 0
  let j := cols 1
  let k := cols 2
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have h01 : i < j := cols.strictMono (by decide)
  have h12 : j < k := cols.strictMono (by decide)
  have hiJ : i ∈ J := J.orderEmbOfFin_mem hJ 0
  have hjJ : j ∈ J := J.orderEmbOfFin_mem hJ 1
  have hkJ : k ∈ J := J.orderEmbOfFin_mem hJ 2
  have hJijk : J = {i, j, k} := by
    simpa [i, j, k, cols] using finset_eq_three_orderEmb_values hJ
  have hnonloop_iff : ∀ x : Fin n, E.IsNonloop x ↔ ¬IsLoop C x := by
    intro x
    exact threeRowCompression_inflated_isNonloop_iff hm hA hfull
      D hleft hright x
  have hindex_eq : ∀ (x : Fin n) (hx : ¬IsLoop C x),
      E.simplifiedIndex x = simplificationClassIndex C x hx := by
    intro x hx
    exact threeRowCompression_inflated_simplifiedIndex_eq
      hm hA hfull D hleft hright x hx
  have himages_eq : ∀ {x y z : Fin n}
      (hx : ¬IsLoop C x) (hy : ¬IsLoop C y) (hz : ¬IsLoop C z),
      E.simplifiedImages {x, y, z} =
        {simplificationClassIndex C x hx,
          simplificationClassIndex C y hy,
          simplificationClassIndex C z hz} := by
    intro x y z hx hy hz
    exact threeRowCompression_inflated_simplifiedImages_triple
      hm hA hfull D hleft hright hx hy hz
  have actualLoop_of_dataLoop : ∀ x : Fin n, E.IsLoop x → IsLoop C x := by
    intro x hxE
    by_contra hxC
    have hxNonloop : E.IsNonloop x := (hnonloop_iff x).2 hxC
    exact ((E.isNonloop_iff_not_isLoop x).1 hxNonloop) hxE
  have dataLoop_of_actualLoop : ∀ x : Fin n, IsLoop C x → E.IsLoop x := by
    intro x hxC
    by_contra hxE
    have hxNonloop : E.IsNonloop x := (E.isNonloop_iff_not_isLoop x).2 hxE
    exact ((hnonloop_iff x).1 hxNonloop) hxC
  change E.TripleNonbasis J ↔ _
  constructor
  · intro hE
    by_cases hi : IsLoop C i
    · exact orderedMinor_allRows_eq_zero_of_isLoop C cols 0 hi
    by_cases hj : IsLoop C j
    · exact orderedMinor_allRows_eq_zero_of_isLoop C cols 1 hj
    by_cases hk : IsLoop C k
    · exact orderedMinor_allRows_eq_zero_of_isLoop C cols 2 hk
    rcases hE.2 with hloops | hinitial | hterminal | hcollinear
    · rcases hloops with ⟨e, heJ, heLoop⟩
      have heLoop' := actualLoop_of_dataLoop e heLoop
      rw [hJijk] at heJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at heJ
      rcases heJ with rfl | rfl | rfl
      · exact (hi heLoop').elim
      · exact (hj heLoop').elim
      · exact (hk heLoop').elim
    · change 2 ≤ (J.filter E.IsInitialParallel).card at hinitial
      have hcard : 1 < (J.filter E.IsInitialParallel).card := by omega
      rcases Finset.one_lt_card.mp hcard with ⟨e, he, f, hf, hef⟩
      have heData := (Finset.mem_filter.mp he).2
      have hfData := (Finset.mem_filter.mp hf).2
      have heNonloopData := E.isInitialParallel_isNonloop heData
      have hfNonloopData := E.isInitialParallel_isNonloop hfData
      have heNonloop : ¬IsLoop C e := (hnonloop_iff e).1 heNonloopData
      have hfNonloop : ¬IsLoop C f := (hnonloop_iff f).1 hfNonloopData
      have heZero := inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_zero
        D K hleft hright heData
      have hfZero := inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_zero
        D K hleft hright hfData
      have hclass : simplificationClassIndex C e heNonloop =
          simplificationClassIndex C f hfNonloop := by
        rw [← hindex_eq e heNonloop, ← hindex_eq f hfNonloop, heZero, hfZero]
      have hefPar : ColumnsPositivelyParallel C e f :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel
          C heNonloop hfNonloop).mp hclass
      have heRange : e ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp he).1
      have hfRange : f ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp hf).1
      rw [← Finset.range_orderEmbOfFin J hJ] at heRange hfRange
      rcases heRange with ⟨re, rfl⟩
      rcases hfRange with ⟨rf, rfl⟩
      exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel
        C cols (fun h ↦ hef (congrArg cols h)) hefPar
    · change 2 ≤ (J.filter E.IsTerminalParallel).card at hterminal
      have hcard : 1 < (J.filter E.IsTerminalParallel).card := by omega
      rcases Finset.one_lt_card.mp hcard with ⟨e, he, f, hf, hef⟩
      have heData := (Finset.mem_filter.mp he).2
      have hfData := (Finset.mem_filter.mp hf).2
      have heNonloopData := E.isTerminalParallel_isNonloop heData
      have hfNonloopData := E.isTerminalParallel_isNonloop hfData
      have heNonloop : ¬IsLoop C e := (hnonloop_iff e).1 heNonloopData
      have hfNonloop : ¬IsLoop C f := (hnonloop_iff f).1 hfNonloopData
      have heLast := inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_last
        D K hleft hright heData
      have hfLast := inflateSimpleCompatibleRankThreeData_simplifiedIndex_eq_last
        D K hleft hright hfData
      have hclass : simplificationClassIndex C e heNonloop =
          simplificationClassIndex C f hfNonloop := by
        rw [← hindex_eq e heNonloop, ← hindex_eq f hfNonloop, heLast, hfLast]
      have hefPar : ColumnsPositivelyParallel C e f :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel
          C heNonloop hfNonloop).mp hclass
      have heRange : e ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp he).1
      have hfRange : f ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp hf).1
      rw [← Finset.range_orderEmbOfFin J hJ] at heRange hfRange
      rcases heRange with ⟨re, rfl⟩
      rcases hfRange with ⟨rf, rfl⟩
      exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel
        C cols (fun h ↦ hef (congrArg cols h)) hefPar
    · rcases hcollinear with ⟨himagesCard, H, hHD, himagesH⟩
      rw [hJijk, himages_eq hi hj hk] at himagesCard himagesH
      let p := simplificationClassIndex C i hi
      let q := simplificationClassIndex C j hj
      let r := simplificationClassIndex C k hk
      change ({p, q, r} : Finset (Fin (simplificationSize C))).card = 3 at himagesCard
      have hpq : p ≠ q := by
        intro hpq
        rw [hpq] at himagesCard
        have htwo : ({q, r} : Finset (Fin (simplificationSize C))).card ≤ 2 :=
          Finset.card_le_two
        simp only [Finset.insert_idem] at himagesCard
        omega
      have hqr : q ≠ r := by
        intro hqr
        rw [hqr] at himagesCard
        have htwo : ({p, r} : Finset (Fin (simplificationSize C))).card ≤ 2 :=
          Finset.card_le_two
        have hdup : ({p, r, r} : Finset (Fin (simplificationSize C))) = {p, r} := by
          ext x
          simp
        rw [hdup] at himagesCard
        omega
      rcases exists_ordered_simplificationTriple_and_scaledMinor
          (hC.tnUpTo 2) h01 h12 hi hj hk hpq hqr with
        ⟨p', q', r', hpq', hqr', hp, hq, hr,
          u, v, w, hu, hv, hw, hscale⟩
      obtain ⟨run, hrun, hH⟩ := Finset.mem_image.mp hHD
      subst H
      have hpMem : p' ∈ (firstCircuitRunInterval D run).points := by
        apply himagesH
        rw [hp]
        exact Finset.mem_insert_self _ _
      have hqMem : q' ∈ (firstCircuitRunInterval D run).points := by
        apply himagesH
        rw [hq]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hrMem : r' ∈ (firstCircuitRunInterval D run).points := by
        apply himagesH
        rw [hr]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      let coreCols : Fin 3 ↪o Fin (simplificationSize C) :=
        selectedTripleEmbedding p' q' r' hpq' hqr'
      have hall : ∀ t, coreCols t ∈ runHyperplane hsn D.runs run := by
        intro t
        rw [← firstCircuitRunInterval_points]
        fin_cases t
        · exact hpMem
        · exact hqMem
        · exact hrMem
      have hdep : ¬(columnMatroid S).Indep (Set.range coreCols) :=
        (D.dependent_iff_interval coreCols).2 ⟨run, hall⟩
      have hcoreZero : orderedMinor S (allRows 3) coreCols = 0 := by
        by_contra hne
        apply hdep
        rw [columnMatroid_indep_range_iff,
          ← orderedMinor_ne_zero_iff_linearIndependent_columns]
        exact hne
      rw [selectedTripleEmbedding_eq cols] at hscale
      change orderedMinor C (allRows 3) cols = 0
      rw [hscale]
      change u * v * w * orderedMinor S (allRows 3) coreCols = 0
      rw [hcoreZero, mul_zero]
  · intro hzero
    refine ⟨hJ, ?_⟩
    by_cases hi : IsLoop C i
    · exact Or.inl ⟨i, hiJ, dataLoop_of_actualLoop i hi⟩
    by_cases hj : IsLoop C j
    · exact Or.inl ⟨j, hjJ, dataLoop_of_actualLoop j hj⟩
    by_cases hk : IsLoop C k
    · exact Or.inl ⟨k, hkJ, dataLoop_of_actualLoop k hk⟩
    have hiE : E.IsNonloop i := (hnonloop_iff i).2 hi
    have hjE : E.IsNonloop j := (hnonloop_iff j).2 hj
    have hkE : E.IsNonloop k := (hnonloop_iff k).2 hk
    let p := simplificationClassIndex C i hi
    let q := simplificationClassIndex C j hj
    let r := simplificationClassIndex C k hk
    by_cases hpq : p = q
    · have hindex : E.simplifiedIndex i = E.simplifiedIndex j := by
        rw [hindex_eq i hi, hindex_eq j hj]
        exact hpq
      rcases inflateSimpleCompatibleRankThreeData_equal_index_is_endpoint
          D K hleft hright h01 hiE hjE hindex with hinitial | hterminal
      · apply Or.inr (Or.inl ?_)
        unfold CompatibleRankThreeData.ContainsInitialParallelPair
        have hsub : ({i, j} : Finset (Fin n)) ⊆ J.filter E.IsInitialParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hiJ, hinitial.1⟩
          · exact Finset.mem_filter.mpr ⟨hjJ, hinitial.2⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h01] using hcard
      · apply Or.inr (Or.inr (Or.inl ?_))
        unfold CompatibleRankThreeData.ContainsTerminalParallelPair
        have hsub : ({i, j} : Finset (Fin n)) ⊆ J.filter E.IsTerminalParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hiJ, hterminal.1⟩
          · exact Finset.mem_filter.mpr ⟨hjJ, hterminal.2⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h01] using hcard
    by_cases hqr : q = r
    · have hindex : E.simplifiedIndex j = E.simplifiedIndex k := by
        rw [hindex_eq j hj, hindex_eq k hk]
        exact hqr
      rcases inflateSimpleCompatibleRankThreeData_equal_index_is_endpoint
          D K hleft hright h12 hjE hkE hindex with hinitial | hterminal
      · apply Or.inr (Or.inl ?_)
        unfold CompatibleRankThreeData.ContainsInitialParallelPair
        have hsub : ({j, k} : Finset (Fin n)) ⊆ J.filter E.IsInitialParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hjJ, hinitial.1⟩
          · exact Finset.mem_filter.mpr ⟨hkJ, hinitial.2⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h12] using hcard
      · apply Or.inr (Or.inr (Or.inl ?_))
        unfold CompatibleRankThreeData.ContainsTerminalParallelPair
        have hsub : ({j, k} : Finset (Fin n)) ⊆ J.filter E.IsTerminalParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hjJ, hterminal.1⟩
          · exact Finset.mem_filter.mpr ⟨hkJ, hterminal.2⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h12] using hcard
    apply Or.inr (Or.inr (Or.inr ?_))
    rcases exists_ordered_simplificationTriple_and_scaledMinor
        (hC.tnUpTo 2) h01 h12 hi hj hk hpq hqr with
      ⟨p', q', r', hpq', hqr', hp, hq, hr,
        u, v, w, hu, hv, hw, hscale⟩
    rw [selectedTripleEmbedding_eq cols] at hscale
    have hcoreZero : orderedMinor S (allRows 3)
        (selectedTripleEmbedding p' q' r' hpq' hqr') = 0 := by
      have hprod : u * v * w ≠ 0 := mul_ne_zero (mul_ne_zero hu.ne' hv.ne') hw.ne'
      rw [hzero] at hscale
      exact (mul_eq_zero.mp hscale.symm).resolve_left hprod
    let coreCols : Fin 3 ↪o Fin (simplificationSize C) :=
      selectedTripleEmbedding p' q' r' hpq' hqr'
    have hdep : ¬(columnMatroid S).Indep (Set.range coreCols) := by
      rw [columnMatroid_indep_range_iff,
        ← orderedMinor_ne_zero_iff_linearIndependent_columns]
      exact not_ne_iff.mpr hcoreZero
    obtain ⟨run, hall⟩ := (D.dependent_iff_interval coreCols).1 hdep
    constructor
    · rw [hJijk, himages_eq hi hj hk, ← hp, ← hq, ← hr]
      exact Finset.card_eq_three.mpr
        ⟨p', q', r', ne_of_lt hpq', ne_of_lt (hpq'.trans hqr'),
          ne_of_lt hqr', rfl⟩
    · refine ⟨firstCircuitRunInterval D run, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨run, Finset.mem_univ run, rfl⟩
      · rw [hJijk, himages_eq hi hj hk, ← hp, ← hq, ← hr]
        intro x hx
        rw [firstCircuitRunInterval_points]
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hall 0
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hall 1
          · have hxr := Finset.mem_singleton.mp hx
            subst x
            exact hall 2

/-- Any endpoint-protected inflation of the canonical core realizes the
column-matroid support of the compressed three-row matrix. -/
theorem threeRowCompression_inflated_supportRealization
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a)) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let K := threeRowCompressionInflationCounts hm hA hfull
    CompatibleTripleSupportRealization
      (inflateSimpleCompatibleRankThreeData D K hleft hright)
      (columnMatroid C) := by
  classical
  dsimp only
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let K := threeRowCompressionInflationCounts hm hA hfull
  let E := inflateSimpleCompatibleRankThreeData D K hleft hright
  have hCfull : HasFullRowRank C :=
    threeRowPositiveCompression_fullRowRank hm hA hfull
  refine ⟨columnMatroid_ground C, ?_, ?_⟩
  · obtain ⟨cols, hcols⟩ := hCfull
    refine ⟨Set.range cols, ?_, ?_⟩
    · exact (columnMatroid_isBase_range_iff C cols).2 hcols
    · rw [Set.ncard_range_of_injective cols.injective]
      simp
  · intro J hJ
    let cols : Fin 3 ↪o Fin n := J.orderEmbOfFin hJ
    have hrange : Set.range cols = (J : Set (Fin n)) := by
      rw [Finset.range_orderEmbOfFin]
    rw [← hrange, columnMatroid_isBase_range_iff]
    have hsupport := threeRowCompression_inflated_tripleNonbasis_iff
      hm hA hfull D hleft hright J hJ
    dsimp only at hsupport
    change E.TripleNonbasis J ↔ orderedMinor C (allRows 3) cols = 0 at hsupport
    tauto

/-- Endpoint-protected core data therefore supply compatible support for
the compressed three-row column matroid. -/
theorem threeRowCompression_hasCompatibleSupport_of_endpointProtection
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    {hsn : 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)}
    (D : FirstCircuitIntervalData (p := 1) hsn
      (simplifiedMatrix (compressedThreeRowToeplitzMatrix m n a)))
    (hleft :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass →
        ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0)
    (hright :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass →
        ∀ H ∈ firstCircuitRunIntervals D,
          H.right.val + 1 ≠ simplificationSize
            (compressedThreeRowToeplitzMatrix m n a)) :
    HasCompatibleRankThreeSupport
      (columnMatroid (compressedThreeRowToeplitzMatrix m n a)) := by
  let K := threeRowCompressionInflationCounts hm hA hfull
  refine ⟨inflateSimpleCompatibleRankThreeData D K hleft hright, ?_⟩
  exact threeRowCompression_inflated_supportRealization
    hm hA hfull D hleft hright

/-! ## Endpoint protection for the canonical simple core -/

/-- If the left endpoint is protected by either an initial loop block or a
nontrivial initial parallel class, then the first three columns of the
canonical simplification are independent. -/
theorem threeRowCompression_core_firstThree_independent
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hprotected :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.leftLoops ∨ 1 < K.initialClass) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let S := simplifiedMatrix C
    LinearIndependent ℝ
      (fun j : Fin 3 ↦ S.col (consecutiveThreeColumns 0 (by
        have hC : TotallyNonnegative
            (compressedThreeRowToeplitzMatrix m n a) := totallyNonnegative_mul
          (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
        have hCfull : HasFullRowRank
            (compressedThreeRowToeplitzMatrix m n a) :=
          threeRowPositiveCompression_fullRowRank hm hA hfull
        have hs := three_le_simplificationSize_of_hasFullRowRank
          (hC.tnUpTo 2) hCfull
        change 2 < simplificationSize (compressedThreeRowToeplitzMatrix m n a)
        omega) j)) := by
  dsimp only at hprotected ⊢
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let S : Matrix (Fin 3) (Fin (simplificationSize C)) ℝ := simplifiedMatrix C
  let K : RankThreeInflationCounts n (simplificationSize C) :=
    threeRowCompressionInflationCounts hm hA hfull
  change 0 < K.leftLoops ∨ 1 < K.initialClass at hprotected
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C :=
    threeRowPositiveCompression_fullRowRank hm hA hfull
  have hs : 3 ≤ simplificationSize C :=
    three_le_simplificationSize_of_hasFullRowRank (hC.tnUpTo 2) hCfull
  have finish : ∀ (p : ℕ) (hbound : p + 2 < n),
      p + 1 = K.leftLoops + K.initialClass →
      LinearIndependent ℝ
        (fun t : Fin 3 ↦ C.col (consecutiveThreeColumns p hbound t)) →
      LinearIndependent ℝ
        (fun t : Fin 3 ↦ S.col (consecutiveThreeColumns 0 (by omega) t)) := by
    intro p hbound hpMiddle hraw
    let rawCols : Fin 3 ↪o Fin n := consecutiveThreeColumns p hbound
    have h0 : ¬IsLoop C (rawCols 0) := hraw.ne_zero 0
    have h1 : ¬IsLoop C (rawCols 1) := hraw.ne_zero 1
    have h2 : ¬IsLoop C (rawCols 2) := hraw.ne_zero 2
    have hclass0Val : (simplificationClassIndex C (rawCols 0) h0).val = 0 := by
      have hf : (simplificationClassIndex C (rawCols 0) h0).val =
          if (rawCols 0).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 0).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 0).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 0) h0
      rw [hf]
      have hraw : (rawCols 0).val = p := by rfl
      split_ifs <;> omega
    have hclass1Val : (simplificationClassIndex C (rawCols 1) h1).val = 1 := by
      have hf : (simplificationClassIndex C (rawCols 1) h1).val =
          if (rawCols 1).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 1).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 1).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 1) h1
      rw [hf]
      have hraw : (rawCols 1).val = p + 1 := by rfl
      split_ifs <;> omega
    have hclass2Val : (simplificationClassIndex C (rawCols 2) h2).val = 2 := by
      have hf : (simplificationClassIndex C (rawCols 2) h2).val =
          if (rawCols 2).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 2).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 2).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 2) h2
      rw [hf]
      have hraw : (rawCols 2).val = p + 2 := by rfl
      split_ifs <;> omega
    have h01raw : rawCols 0 < rawCols 1 := rawCols.strictMono (by decide)
    have h12raw : rawCols 1 < rawCols 2 := rawCols.strictMono (by decide)
    have hc01 : simplificationClassIndex C (rawCols 0) h0 ≠
        simplificationClassIndex C (rawCols 1) h1 := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hc12 : simplificationClassIndex C (rawCols 1) h1 ≠
        simplificationClassIndex C (rawCols 2) h2 := by
      intro heq
      have := congrArg Fin.val heq
      omega
    rcases exists_ordered_simplificationTriple_and_scaledMinor
        (hC.tnUpTo 2) h01raw h12raw h0 h1 h2 hc01 hc12 with
      ⟨p', q', r', hpq', hqr', hp', hq', hr',
        u, v, w, hu, hv, hw, hscale⟩
    have hrawMinor : orderedMinor C (allRows 3) rawCols ≠ 0 :=
      (orderedMinor_ne_zero_iff_linearIndependent_columns C rawCols).2 hraw
    rw [selectedTripleEmbedding_eq rawCols] at hscale
    let coreCols : Fin 3 ↪o Fin (simplificationSize C) :=
      selectedTripleEmbedding p' q' r' hpq' hqr'
    have hcoreMinor : orderedMinor S (allRows 3) coreCols ≠ 0 := by
      intro hzero
      apply hrawMinor
      rw [hscale]
      change u * v * w * orderedMinor S (allRows 3) coreCols = 0
      rw [hzero, mul_zero]
    have hcoreCols : coreCols = consecutiveThreeColumns 0 (by omega) := by
      apply RelEmbedding.ext
      intro t
      apply Fin.ext
      fin_cases t
      · have hpVal := congrArg Fin.val hp'
        change p'.val = 0
        omega
      · have hqVal := congrArg Fin.val hq'
        change q'.val = 1
        omega
      · have hrVal := congrArg Fin.val hr'
        change r'.val = 2
        omega
    rw [hcoreCols] at hcoreMinor
    exact (orderedMinor_ne_zero_iff_linearIndependent_columns S _).1 hcoreMinor
  rcases hprotected with hleftLoops | hlargeClass
  · have hinitial : K.initialClass = 1 := K.initial_singleton_of_loops hleftLoops
    let p := K.leftLoops
    have hp : 1 ≤ p := by dsimp only [p]; omega
    have hpBound : p < n := by
      have hground := K.ground_eq
      have hterminal := K.terminalClass_pos
      dsimp only [p]
      omega
    have hloops : ∀ x : Fin n, x.val < p → IsLoop A x := by
      intro x hx
      have hxC : IsLoop C x := by
        by_contra hxNonloop
        have hbounds := (threeRowCompression_nonloop_iff_inflationCounts
          hm hA hfull x).1 hxNonloop
        dsimp only [p] at hx
        exact (not_lt_of_ge hbounds.1) hx
      exact (isLoop_threeRowPositiveCompression_iff hA x).mp hxC
    let jp : Fin n := ⟨p, hpBound⟩
    have hjpC : ¬IsLoop C jp := by
      apply (threeRowCompression_nonloop_iff_inflationCounts
        hm hA hfull jp).2
      have hground := K.ground_eq
      change K.leftLoops ≤ p ∧ p < n - K.rightLoops
      dsimp only [p]
      omega
    have hjpA : ¬IsLoop A jp :=
      (isLoop_threeRowPositiveCompression_iff hA jp).not.mp hjpC
    obtain ⟨hbound, hminor⟩ := toeplitzMatrix_initialLoops_endpointProtection
      hm hp hpBound hA hfull hloops hjpA
    have hrawA : LinearIndependent ℝ
        (fun t : Fin 3 ↦ A.col (consecutiveThreeColumns p hbound t)) :=
      linearIndependent_columns_of_orderedMinor_ne_zero
        (topThreeRows m hm) (consecutiveThreeColumns p hbound) hminor.ne'
    have hrawC := positiveCompression_preserves_ordered_independence le_rfl
      (threeRowPositiveCompression_totallyPositive m) hA
      (consecutiveThreeColumns p hbound) hrawA
    apply finish p hbound
    · dsimp only [p]
      omega
    · simpa [C, A] using hrawC
  · have hleftZero : K.leftLoops = 0 := by
      by_contra hleft
      have hleftPos : 0 < K.leftLoops := Nat.pos_of_ne_zero hleft
      have := K.initial_singleton_of_loops hleftPos
      omega
    let L := K.initialClass
    have hL : 2 ≤ L := by dsimp only [L]; omega
    have hLBound : L < n := by
      have hground := K.ground_eq
      have hterminal := K.terminalClass_pos
      dsimp only [L]
      omega
    have hblock : IsMaximalToeplitzParallelBlock A 0 L := by
      refine ⟨hL, by omega, ?_, ?_, ?_, ?_⟩
      · intro t
        apply (isLoop_threeRowPositiveCompression_iff hA _).not.mp
        apply (threeRowCompression_nonloop_iff_inflationCounts
          hm hA hfull _).2
        have hground := K.ground_eq
        simpa only [Nat.zero_add] using
          (show K.leftLoops ≤ t.val ∧ t.val < n - K.rightLoops by omega)
      · intro t
        by_cases ht : t.val = 0
        · have hindex : (⟨0 + t.val, by omega⟩ : Fin n) = ⟨0, by omega⟩ :=
            by
              apply Fin.ext
              change 0 + t.val = 0
              omega
          rw [hindex]
          exact columnsPositivelyParallel_refl A _
        · let x : Fin n := ⟨t.val, by omega⟩
          let z : Fin n := ⟨0, by omega⟩
          have hzC : ¬IsLoop C z := by
            apply (threeRowCompression_nonloop_iff_inflationCounts
              hm hA hfull z).2
            have hground := K.ground_eq
            change K.leftLoops ≤ 0 ∧ 0 < n - K.rightLoops
            omega
          have hxC : ¬IsLoop C x := by
            apply (threeRowCompression_nonloop_iff_inflationCounts
              hm hA hfull x).2
            have hground := K.ground_eq
            change K.leftLoops ≤ t.val ∧ t.val < n - K.rightLoops
            omega
          have hzFormula : (simplificationClassIndex C z hzC).val =
              if z.val < K.leftLoops + K.initialClass then 0
              else if z.val < K.leftLoops + K.initialClass +
                  (simplificationSize C - 2) then
                z.val - (K.leftLoops + K.initialClass) + 1
              else simplificationSize C - 1 := by
            simpa [C, K] using threeRowCompression_classIndex_formula
              hm hA hfull z hzC
          have hxFormula : (simplificationClassIndex C x hxC).val =
              if x.val < K.leftLoops + K.initialClass then 0
              else if x.val < K.leftLoops + K.initialClass +
                  (simplificationSize C - 2) then
                x.val - (K.leftLoops + K.initialClass) + 1
              else simplificationSize C - 1 := by
            simpa [C, K] using threeRowCompression_classIndex_formula
              hm hA hfull x hxC
          have hclass : simplificationClassIndex C z hzC =
              simplificationClassIndex C x hxC := by
            apply Fin.ext
            change (simplificationClassIndex C z hzC).val =
              (simplificationClassIndex C x hxC).val
            rw [hzFormula, hxFormula]
            split_ifs <;> dsimp only [z, x] at * <;> omega
          have hparC :=
            (simplificationClassIndex_eq_iff_columnsPositivelyParallel
              C hzC hxC).mp hclass
          have hzA : ¬IsLoop A z :=
            (isLoop_threeRowPositiveCompression_iff hA z).not.mp hzC
          have hxA : ¬IsLoop A x :=
            (isLoop_threeRowPositiveCompression_iff hA x).not.mp hxC
          have hparA := (columnsPositivelyParallel_threeRowCompression_iff
            hA (Fin.mk_lt_mk.mpr (by omega)) hzA hxA).1 hparC
          simpa [x, z] using hparA
      · intro hp
        omega
      · intro hright hparA
        let x : Fin n := ⟨L - 1, by omega⟩
        let y : Fin n := ⟨L, by omega⟩
        have hxC : ¬IsLoop C x := by
          apply (threeRowCompression_nonloop_iff_inflationCounts
            hm hA hfull x).2
          have hground := K.ground_eq
          change K.leftLoops ≤ L - 1 ∧ L - 1 < n - K.rightLoops
          omega
        have hyC : ¬IsLoop C y := by
          apply (threeRowCompression_nonloop_iff_inflationCounts
            hm hA hfull y).2
          have hground := K.ground_eq
          change K.leftLoops ≤ L ∧ L < n - K.rightLoops
          omega
        have hxA : ¬IsLoop A x :=
          (isLoop_threeRowPositiveCompression_iff hA x).not.mp hxC
        have hyA : ¬IsLoop A y :=
          (isLoop_threeRowPositiveCompression_iff hA y).not.mp hyC
        have hparC := (columnsPositivelyParallel_threeRowCompression_iff
          hA (Fin.mk_lt_mk.mpr (by omega)) hxA hyA).2
          (by simpa [x, y] using hparA)
        have hclass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel
            C hxC hyC).2 hparC
        have hxFormula : (simplificationClassIndex C x hxC).val =
            if x.val < K.leftLoops + K.initialClass then 0
            else if x.val < K.leftLoops + K.initialClass +
                (simplificationSize C - 2) then
              x.val - (K.leftLoops + K.initialClass) + 1
            else simplificationSize C - 1 := by
          simpa [C, K] using threeRowCompression_classIndex_formula
            hm hA hfull x hxC
        have hyFormula : (simplificationClassIndex C y hyC).val =
            if y.val < K.leftLoops + K.initialClass then 0
            else if y.val < K.leftLoops + K.initialClass +
                (simplificationSize C - 2) then
              y.val - (K.leftLoops + K.initialClass) + 1
            else simplificationSize C - 1 := by
          simpa [C, K] using threeRowCompression_classIndex_formula
            hm hA hfull y hyC
        have hval := congrArg Fin.val hclass
        rw [hxFormula, hyFormula] at hval
        split_ifs at hval <;> dsimp only [x, y] at * <;> omega
    obtain ⟨hbound, hminor⟩ := toeplitzMatrix_initialParallel_endpointProtection
      hm hA hfull hblock
    let p := L - 1
    have hrawA : LinearIndependent ℝ
        (fun t : Fin 3 ↦ A.col (consecutiveThreeColumns p hbound t)) :=
      linearIndependent_columns_of_orderedMinor_ne_zero
        (topThreeRows m hm) (consecutiveThreeColumns p hbound) hminor.ne'
    have hrawC := positiveCompression_preserves_ordered_independence le_rfl
      (threeRowPositiveCompression_totallyPositive m) hA
      (consecutiveThreeColumns p hbound) hrawA
    apply finish p hbound
    · dsimp only [p, L]
      omega
    · simpa [C, A] using hrawC

/-- If the right endpoint is protected by either a terminal loop block or a
nontrivial terminal parallel class, then the last three columns of the
canonical simplification are independent. -/
theorem threeRowCompression_core_lastThree_independent
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a))
    (hprotected :
      let K := threeRowCompressionInflationCounts hm hA hfull
      0 < K.rightLoops ∨ 1 < K.terminalClass) :
    let C := compressedThreeRowToeplitzMatrix m n a
    let S := simplifiedMatrix C
    LinearIndependent ℝ
      (fun j : Fin 3 ↦ S.col (lastThreeColumns (simplificationSize C) (by
        have hC : TotallyNonnegative C := totallyNonnegative_mul
          (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
        have hCfull : HasFullRowRank C :=
          threeRowPositiveCompression_fullRowRank hm hA hfull
        exact three_le_simplificationSize_of_hasFullRowRank
          (hC.tnUpTo 2) hCfull) j)) := by
  dsimp only at hprotected ⊢
  let A : Matrix (Fin m) (Fin n) ℝ := toeplitzMatrix m n a
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let S : Matrix (Fin 3) (Fin (simplificationSize C)) ℝ := simplifiedMatrix C
  let K : RankThreeInflationCounts n (simplificationSize C) :=
    threeRowCompressionInflationCounts hm hA hfull
  change 0 < K.rightLoops ∨ 1 < K.terminalClass at hprotected
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C :=
    threeRowPositiveCompression_fullRowRank hm hA hfull
  have hs : 3 ≤ simplificationSize C :=
    three_le_simplificationSize_of_hasFullRowRank (hC.tnUpTo 2) hCfull
  have finish : ∀ (p : ℕ) (hbound : p + 2 < n),
      p + 2 = K.leftLoops + K.initialClass + (simplificationSize C - 2) →
      LinearIndependent ℝ
        (fun t : Fin 3 ↦ C.col (consecutiveThreeColumns p hbound t)) →
      LinearIndependent ℝ
        (fun t : Fin 3 ↦ S.col
          (lastThreeColumns (simplificationSize C) hs t)) := by
    intro p hbound hpTerminal hraw
    let rawCols : Fin 3 ↪o Fin n := consecutiveThreeColumns p hbound
    have h0 : ¬IsLoop C (rawCols 0) := hraw.ne_zero 0
    have h1 : ¬IsLoop C (rawCols 1) := hraw.ne_zero 1
    have h2 : ¬IsLoop C (rawCols 2) := hraw.ne_zero 2
    have hclass0Val : (simplificationClassIndex C (rawCols 0) h0).val =
        simplificationSize C - 3 := by
      have hf : (simplificationClassIndex C (rawCols 0) h0).val =
          if (rawCols 0).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 0).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 0).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 0) h0
      rw [hf]
      have hraw : (rawCols 0).val = p := by rfl
      split_ifs <;> omega
    have hclass1Val : (simplificationClassIndex C (rawCols 1) h1).val =
        simplificationSize C - 2 := by
      have hf : (simplificationClassIndex C (rawCols 1) h1).val =
          if (rawCols 1).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 1).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 1).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 1) h1
      rw [hf]
      have hraw : (rawCols 1).val = p + 1 := by rfl
      split_ifs <;> omega
    have hclass2Val : (simplificationClassIndex C (rawCols 2) h2).val =
        simplificationSize C - 1 := by
      have hf : (simplificationClassIndex C (rawCols 2) h2).val =
          if (rawCols 2).val < K.leftLoops + K.initialClass then 0
          else if (rawCols 2).val < K.leftLoops + K.initialClass +
              (simplificationSize C - 2) then
            (rawCols 2).val - (K.leftLoops + K.initialClass) + 1
          else simplificationSize C - 1 := by
        simpa [C, K] using threeRowCompression_classIndex_formula
          hm hA hfull (rawCols 2) h2
      rw [hf]
      have hraw : (rawCols 2).val = p + 2 := by rfl
      split_ifs <;> omega
    have h01raw : rawCols 0 < rawCols 1 := rawCols.strictMono (by decide)
    have h12raw : rawCols 1 < rawCols 2 := rawCols.strictMono (by decide)
    have hc01 : simplificationClassIndex C (rawCols 0) h0 ≠
        simplificationClassIndex C (rawCols 1) h1 := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hc12 : simplificationClassIndex C (rawCols 1) h1 ≠
        simplificationClassIndex C (rawCols 2) h2 := by
      intro heq
      have := congrArg Fin.val heq
      omega
    rcases exists_ordered_simplificationTriple_and_scaledMinor
        (hC.tnUpTo 2) h01raw h12raw h0 h1 h2 hc01 hc12 with
      ⟨p', q', r', hpq', hqr', hp', hq', hr',
        u, v, w, hu, hv, hw, hscale⟩
    have hrawMinor : orderedMinor C (allRows 3) rawCols ≠ 0 :=
      (orderedMinor_ne_zero_iff_linearIndependent_columns C rawCols).2 hraw
    rw [selectedTripleEmbedding_eq rawCols] at hscale
    let coreCols : Fin 3 ↪o Fin (simplificationSize C) :=
      selectedTripleEmbedding p' q' r' hpq' hqr'
    have hcoreMinor : orderedMinor S (allRows 3) coreCols ≠ 0 := by
      intro hzero
      apply hrawMinor
      rw [hscale]
      change u * v * w * orderedMinor S (allRows 3) coreCols = 0
      rw [hzero, mul_zero]
    have hcoreCols : coreCols = lastThreeColumns (simplificationSize C) hs := by
      apply RelEmbedding.ext
      intro t
      apply Fin.ext
      fin_cases t
      · have hpVal := congrArg Fin.val hp'
        change p'.val = simplificationSize C - 3
        omega
      · have hqVal := congrArg Fin.val hq'
        change q'.val = simplificationSize C - 2
        omega
      · have hrVal := congrArg Fin.val hr'
        change r'.val = simplificationSize C - 1
        omega
    rw [hcoreCols] at hcoreMinor
    exact (orderedMinor_ne_zero_iff_linearIndependent_columns S _).1 hcoreMinor
  rcases hprotected with hrightLoops | hlargeClass
  · have hterminal : K.terminalClass = 1 :=
      K.terminal_singleton_of_loops hrightLoops
    let q := n - 1 - K.rightLoops
    have hqBound : q < n := by
      have hground := K.ground_eq
      dsimp only [q]
      omega
    have hqSucc : q + 1 < n := by
      have hground := K.ground_eq
      dsimp only [q]
      omega
    have hloops : ∀ x : Fin n, q < x.val → IsLoop A x := by
      intro x hx
      have hxC : IsLoop C x := by
        by_contra hxNonloop
        have hbounds := (threeRowCompression_nonloop_iff_inflationCounts
          hm hA hfull x).1 hxNonloop
        change K.leftLoops ≤ x.val ∧ x.val < n - K.rightLoops at hbounds
        have hground := K.ground_eq
        dsimp only [q] at hx
        omega
      exact (isLoop_threeRowPositiveCompression_iff hA x).mp hxC
    let jq : Fin n := ⟨q, hqBound⟩
    have hjqC : ¬IsLoop C jq := by
      apply (threeRowCompression_nonloop_iff_inflationCounts
        hm hA hfull jq).2
      have hground := K.ground_eq
      change K.leftLoops ≤ q ∧ q < n - K.rightLoops
      dsimp only [q]
      omega
    have hjqA : ¬IsLoop A jq :=
      (isLoop_threeRowPositiveCompression_iff hA jq).not.mp hjqC
    obtain ⟨hbound, hminor⟩ := toeplitzMatrix_terminalLoops_endpointProtection
      hm hqSucc hA hfull hloops hjqA
    let pRev := n - 1 - q
    let revCols : Fin 3 ↪o Fin n :=
      reverseOrderEmbedding (consecutiveThreeColumns pRev hbound)
    have hqTwo : 2 ≤ q := by
      omega
    let p := q - 2
    have hpBound : p + 2 < n := by dsimp only [p]; omega
    have hcols : revCols = consecutiveThreeColumns p hpBound := by
      apply RelEmbedding.ext
      intro t
      apply Fin.ext
      fin_cases t <;>
        simp [revCols, pRev, p, reverseOrderEmbedding,
          consecutiveThreeColumns, selectedTripleEmbedding] <;> omega
    have hrawARev : LinearIndependent ℝ (fun t : Fin 3 ↦ A.col (revCols t)) :=
      linearIndependent_columns_of_orderedMinor_ne_zero
        (reverseOrderEmbedding (topThreeRows m hm)) revCols hminor.ne'
    have hrawA : LinearIndependent ℝ
        (fun t : Fin 3 ↦ A.col (consecutiveThreeColumns p hpBound t)) := by
      rwa [← hcols]
    have hrawC := positiveCompression_preserves_ordered_independence le_rfl
      (threeRowPositiveCompression_totallyPositive m) hA
      (consecutiveThreeColumns p hpBound) hrawA
    apply finish p hpBound
    · have hground := K.ground_eq
      dsimp only [p, q]
      omega
    · simpa [C, A] using hrawC
  · have hrightZero : K.rightLoops = 0 := by
      by_contra hright
      have hrightPos : 0 < K.rightLoops := Nat.pos_of_ne_zero hright
      have := K.terminal_singleton_of_loops hrightPos
      omega
    let L := K.terminalClass
    have hL : 2 ≤ L := by dsimp only [L]; omega
    have hLle : L ≤ n := by
      have hground := K.ground_eq
      dsimp only [L]
      omega
    let b := n - L
    have hbEnd : b + L = n := by dsimp only [b]; omega
    have hblock : IsMaximalToeplitzParallelBlock A b L := by
      refine ⟨hL, by omega, ?_, ?_, ?_, ?_⟩
      · intro t
        apply (isLoop_threeRowPositiveCompression_iff hA _).not.mp
        apply (threeRowCompression_nonloop_iff_inflationCounts
          hm hA hfull _).2
        have hground := K.ground_eq
        change K.leftLoops ≤ b + t.val ∧ b + t.val < n - K.rightLoops
        dsimp only [b]
        omega
      · intro t
        by_cases ht : t.val = 0
        · have hindex : (⟨b + t.val, by omega⟩ : Fin n) = ⟨b, by omega⟩ := by
            apply Fin.ext
            change b + t.val = b
            omega
          rw [hindex]
          exact columnsPositivelyParallel_refl A _
        · let z : Fin n := ⟨b, by omega⟩
          let x : Fin n := ⟨b + t.val, by omega⟩
          have hzC : ¬IsLoop C z := by
            apply (threeRowCompression_nonloop_iff_inflationCounts
              hm hA hfull z).2
            have hground := K.ground_eq
            change K.leftLoops ≤ b ∧ b < n - K.rightLoops
            dsimp only [b]
            omega
          have hxC : ¬IsLoop C x := by
            apply (threeRowCompression_nonloop_iff_inflationCounts
              hm hA hfull x).2
            have hground := K.ground_eq
            change K.leftLoops ≤ b + t.val ∧ b + t.val < n - K.rightLoops
            dsimp only [b]
            omega
          have hzFormula : (simplificationClassIndex C z hzC).val =
              if z.val < K.leftLoops + K.initialClass then 0
              else if z.val < K.leftLoops + K.initialClass +
                  (simplificationSize C - 2) then
                z.val - (K.leftLoops + K.initialClass) + 1
              else simplificationSize C - 1 := by
            simpa [C, K] using threeRowCompression_classIndex_formula
              hm hA hfull z hzC
          have hxFormula : (simplificationClassIndex C x hxC).val =
              if x.val < K.leftLoops + K.initialClass then 0
              else if x.val < K.leftLoops + K.initialClass +
                  (simplificationSize C - 2) then
                x.val - (K.leftLoops + K.initialClass) + 1
              else simplificationSize C - 1 := by
            simpa [C, K] using threeRowCompression_classIndex_formula
              hm hA hfull x hxC
          have hclass : simplificationClassIndex C z hzC =
              simplificationClassIndex C x hxC := by
            apply Fin.ext
            have hground := K.ground_eq
            rw [hzFormula, hxFormula]
            split_ifs <;> dsimp only [z, x, b] at * <;> omega
          have hparC :=
            (simplificationClassIndex_eq_iff_columnsPositivelyParallel
              C hzC hxC).mp hclass
          have hzA : ¬IsLoop A z :=
            (isLoop_threeRowPositiveCompression_iff hA z).not.mp hzC
          have hxA : ¬IsLoop A x :=
            (isLoop_threeRowPositiveCompression_iff hA x).not.mp hxC
          have hparA := (columnsPositivelyParallel_threeRowCompression_iff
            hA (Fin.mk_lt_mk.mpr (by omega)) hzA hxA).1 hparC
          simpa [z, x] using hparA
      · intro hbleft hparA
        let x : Fin n := ⟨b - 1, by omega⟩
        let y : Fin n := ⟨b, by omega⟩
        have hxC : ¬IsLoop C x := by
          apply (threeRowCompression_nonloop_iff_inflationCounts
            hm hA hfull x).2
          have hground := K.ground_eq
          change K.leftLoops ≤ b - 1 ∧ b - 1 < n - K.rightLoops
          dsimp only [b]
          omega
        have hyC : ¬IsLoop C y := by
          apply (threeRowCompression_nonloop_iff_inflationCounts
            hm hA hfull y).2
          have hground := K.ground_eq
          change K.leftLoops ≤ b ∧ b < n - K.rightLoops
          dsimp only [b]
          omega
        have hxA : ¬IsLoop A x :=
          (isLoop_threeRowPositiveCompression_iff hA x).not.mp hxC
        have hyA : ¬IsLoop A y :=
          (isLoop_threeRowPositiveCompression_iff hA y).not.mp hyC
        have hparC := (columnsPositivelyParallel_threeRowCompression_iff
          hA (Fin.mk_lt_mk.mpr (by omega)) hxA hyA).2
          (by simpa [x, y] using hparA)
        have hclass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel
            C hxC hyC).2 hparC
        have hxFormula : (simplificationClassIndex C x hxC).val =
            if x.val < K.leftLoops + K.initialClass then 0
            else if x.val < K.leftLoops + K.initialClass +
                (simplificationSize C - 2) then
              x.val - (K.leftLoops + K.initialClass) + 1
            else simplificationSize C - 1 := by
          simpa [C, K] using threeRowCompression_classIndex_formula
            hm hA hfull x hxC
        have hyFormula : (simplificationClassIndex C y hyC).val =
            if y.val < K.leftLoops + K.initialClass then 0
            else if y.val < K.leftLoops + K.initialClass +
                (simplificationSize C - 2) then
              y.val - (K.leftLoops + K.initialClass) + 1
            else simplificationSize C - 1 := by
          simpa [C, K] using threeRowCompression_classIndex_formula
            hm hA hfull y hyC
        have hval := congrArg Fin.val hclass
        have hground := K.ground_eq
        rw [hxFormula, hyFormula] at hval
        split_ifs at hval <;> dsimp only [x, y, b] at * <;> omega
      · intro hright
        omega
    obtain ⟨hbound, hminor⟩ := toeplitzMatrix_terminalParallel_endpointProtection
      hm hbEnd hA hfull hblock
    let revCols : Fin 3 ↪o Fin n :=
      reverseOrderEmbedding (consecutiveThreeColumns (L - 1) hbound)
    let p := b - 2
    have hpBound : p + 2 < n := by
      have hground := K.ground_eq
      dsimp only [p, b]
      omega
    have hcols : revCols = consecutiveThreeColumns p hpBound := by
      apply RelEmbedding.ext
      intro t
      apply Fin.ext
      fin_cases t <;>
        simp [revCols, p, b, reverseOrderEmbedding,
          consecutiveThreeColumns, selectedTripleEmbedding] <;> omega
    have hrawARev : LinearIndependent ℝ (fun t : Fin 3 ↦ A.col (revCols t)) :=
      linearIndependent_columns_of_orderedMinor_ne_zero
        (reverseOrderEmbedding (topThreeRows m hm)) revCols hminor.ne'
    have hrawA : LinearIndependent ℝ
        (fun t : Fin 3 ↦ A.col (consecutiveThreeColumns p hpBound t)) := by
      rwa [← hcols]
    have hrawC := positiveCompression_preserves_ordered_independence le_rfl
      (threeRowPositiveCompression_totallyPositive m) hA
      (consecutiveThreeColumns p hpBound) hrawA
    apply finish p hpBound
    · have hground := K.ground_eq
      dsimp only [p, b, L]
      omega
    · simpa [C, A] using hrawC

/-! ## Unconditional rank-three assembly -/

/-- The canonical three-row compression of every full-rank TNN Toeplitz
matrix has compatible rank-three support. -/
theorem threeRowCompression_hasCompatibleSupport
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) :
    HasCompatibleRankThreeSupport
      (columnMatroid (compressedThreeRowToeplitzMatrix m n a)) := by
  let C : Matrix (Fin 3) (Fin n) ℝ := compressedThreeRowToeplitzMatrix m n a
  let S : Matrix (Fin 3) (Fin (simplificationSize C)) ℝ := simplifiedMatrix C
  let K : RankThreeInflationCounts n (simplificationSize C) :=
    threeRowCompressionInflationCounts hm hA hfull
  have hC : TotallyNonnegative C := totallyNonnegative_mul
    (threeRowPositiveCompression_totallyPositive m).totallyNonnegative hA
  have hCfull : HasFullRowRank C :=
    threeRowPositiveCompression_fullRowRank hm hA hfull
  have hs : 3 ≤ simplificationSize C :=
    three_le_simplificationSize_of_hasFullRowRank (hC.tnUpTo 2) hCfull
  obtain ⟨hsn, ⟨D⟩⟩ := exists_threeRowCompression_coreIntervalData
    hm hA hfull
  change 2 < simplificationSize C at hsn
  change FirstCircuitIntervalData (p := 1) hsn S at D
  have hS : TotallyNonnegative S :=
    hC.submatrix (allRows 3) (simplificationEmbedding C)
  have hpair : ∀ cols : Fin 2 ↪o Fin (simplificationSize C),
      LinearIndependent ℝ (fun j : Fin 2 ↦ S.col (cols j)) := by
    intro cols
    have hpq : cols 0 < cols 1 := cols.strictMono (by decide)
    by_contra hdep
    have hcolsEq : cols = twoPointOrderEmbedding (cols 0) (cols 1) hpq := by
      apply RelEmbedding.ext
      intro t
      fin_cases t <;> rfl
    rw [hcolsEq] at hdep
    have hparallel := columnsPositivelyParallel_of_pair_not_independent
      hS hpq (simplifiedMatrix_not_isLoop C _)
        (simplifiedMatrix_not_isLoop C _) hdep
    have heq := (simplifiedMatrix_columnsPositivelyParallel_iff C _ _).1 hparallel
    exact (ne_of_lt hpq) heq
  have hleft : 0 < K.leftLoops ∨ 1 < K.initialClass →
      ∀ H ∈ firstCircuitRunIntervals D, H.left.val ≠ 0 := by
    intro hprotected H hH hleftZero
    obtain ⟨run, hrun, rfl⟩ := Finset.mem_image.mp hH
    let F : Set (Fin (simplificationSize C)) := runHyperplane hsn D.runs run
    have hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid S) F :=
      (isLargeFirstCircuitFlat_iff_runHyperplane hpair D F).2 ⟨run, rfl⟩
    have hfirst : LinearIndependent ℝ
        (fun j : Fin 3 ↦ S.col (consecutiveThreeColumns 0 (by omega) j)) := by
      simpa [C, S, K] using threeRowCompression_core_firstThree_independent
        hm hA hfull hprotected
    have hnot := first_not_mem_large_rankTwo_flat hs hS hpair hfirst hF
    apply hnot
    change (⟨0, by omega⟩ : Fin (simplificationSize C)) ∈
      runHyperplane hsn D.runs run
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftVal : (D.runs.left run).val = 0 := by
        simpa [firstCircuitRunInterval, runLeftColumn] using hleftZero
      omega
    · apply Fin.mk_le_mk.mpr
      change 0 ≤ (D.runs.right run).val + 2
      omega
  have hright : 0 < K.rightLoops ∨ 1 < K.terminalClass →
      ∀ H ∈ firstCircuitRunIntervals D,
        H.right.val + 1 ≠ simplificationSize C := by
    intro hprotected H hH hrightLast
    obtain ⟨run, hrun, rfl⟩ := Finset.mem_image.mp hH
    let F : Set (Fin (simplificationSize C)) := runHyperplane hsn D.runs run
    have hF : IsLargeFirstCircuitFlat (p := 1) (columnMatroid S) F :=
      (isLargeFirstCircuitFlat_iff_runHyperplane hpair D F).2 ⟨run, rfl⟩
    have hlast : LinearIndependent ℝ
        (fun j : Fin 3 ↦ S.col
          (lastThreeColumns (simplificationSize C) hs j)) := by
      simpa [C, S, K] using threeRowCompression_core_lastThree_independent
        hm hA hfull hprotected
    have hnot := last_not_mem_large_rankTwo_flat hs hS hpair hlast hF
    apply hnot
    change (⟨simplificationSize C - 1, by omega⟩ :
      Fin (simplificationSize C)) ∈ runHyperplane hsn D.runs run
    apply Finset.mem_Icc.mpr
    constructor
    · apply Fin.mk_le_mk.mpr
      have hleftBound := (D.runs.left run).isLt
      omega
    · apply Fin.mk_le_mk.mpr
      have hrightVal : (D.runs.right run).val + 2 + 1 =
          simplificationSize C := by
        simpa [firstCircuitRunInterval, runRightColumn] using hrightLast
      omega
  exact threeRowCompression_hasCompatibleSupport_of_endpointProtection
    hm hA hfull D hleft hright

/-- The complete `k = 3` case of Theorem 4.5: the rank-three truncation of
an arbitrary-rank TNN Toeplitz column matroid has a full-rank TNN Toeplitz
representation. -/
theorem threeSkeleton_toeplitzRealization
    {m n : ℕ} (hm : 3 ≤ m) {a : ℤ → ℝ}
    (hA : TotallyNonnegative (toeplitzMatrix m n a))
    (hfull : HasFullRowRank (toeplitzMatrix m n a)) :
    ∃ b : Fin (n + 2) → ℝ,
      TotallyNonnegative (rankThreeToeplitz b) ∧
        HasFullRowRank (rankThreeToeplitz b) ∧
        IsRankTruncationOf 3 (columnMatroid (rankThreeToeplitz b))
          (columnMatroid (toeplitzMatrix m n a)) := by
  apply threeSkeleton_toeplitzRealization_of_compatibleSupport hA
  simpa [compressedThreeRowToeplitzMatrix] using
    threeRowCompression_hasCompatibleSupport hm hA hfull

end

end FurtherToeplitzPositroids
