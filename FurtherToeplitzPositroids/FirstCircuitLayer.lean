import FurtherToeplitzPositroids.PositiveCompression
import PavingToeplitzPositroids.Classification
import PavingToeplitzPositroids.MatroidHyperplanes
import PavingToeplitzPositroids.ZeroRunExistence

/-!
# The first nonuniform circuit layer

The paper's lower rank is written as `p + 1`.  Thus the first circuits have
size `p + 2`, and compression uses `p + 2` rows.
-/

namespace FurtherToeplitzPositroids

open Matrix PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- The consecutive rank-defect set from equation (4). -/
def firstCircuitZeroSet
    {p m n : ℕ} (hpn : p + 1 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) : Finset (Fin (n - (p + 1))) :=
  by
    classical
    exact Finset.univ.filter fun t ↦
      ¬(columnMatroid A).Indep
        (Set.range (consecutiveColumns hpn t))

@[simp]
theorem mem_firstCircuitZeroSet_iff
    {p m n : ℕ} (hpn : p + 1 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (t : Fin (n - (p + 1))) :
    t ∈ firstCircuitZeroSet hpn A ↔
      ¬(columnMatroid A).Indep
        (Set.range (consecutiveColumns hpn t)) := by
  simp [firstCircuitZeroSet]

/-- A maximal minor of a square-row compression vanishes exactly when the
corresponding original columns are dependent. -/
theorem positiveCompression_maximalMinor_eq_zero_iff_not_indep
    {k m n : ℕ} {P : Matrix (Fin (k + 1)) (Fin m) ℝ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (hP : TotallyPositive P) (hA : TotallyNonnegative A)
    (J : Fin (k + 1) ↪o Fin n) :
    matrixMaximalMinor (P * A) J = 0 ↔
      ¬(columnMatroid A).Indep (Set.range J) := by
  have hlin :
      LinearIndependent ℝ (fun j : Fin (k + 1) ↦ (P * A).col (J j)) ↔
        LinearIndependent ℝ (fun j : Fin (k + 1) ↦ A.col (J j)) :=
    positiveCompression_ordered_independence_iff le_rfl hP hA J
  constructor
  · intro hzero hJind
    have hAind := (columnMatroid_indep_range_iff A J).1 hJind
    have hBind := hlin.2 hAind
    have hne : matrixMaximalMinor (P * A) J ≠ 0 := by
      rw [matrixMaximalMinor,
        orderedMinor_ne_zero_iff_linearIndependent_columns]
      exact hBind
    exact hne hzero
  · intro hdep
    by_contra hne
    apply hdep
    rw [columnMatroid_indep_range_iff]
    apply hlin.1
    rw [← orderedMinor_ne_zero_iff_linearIndependent_columns]
    exact hne

/-- Theorem 3.4(i), anchor form: a first-layer selection is dependent exactly
when every consecutive anchor in its endpoint span is rank-defective. -/
theorem firstCircuit_dependent_iff_all_anchors
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (J : Fin (p + 2) ↪o Fin n) :
    ¬(columnMatroid A).Indep (Set.range J) ↔
      ∀ t ∈ anchorFinset J, t ∈ firstCircuitZeroSet hpn A := by
  let B : Matrix (Fin (p + 2)) (Fin n) ℝ := P * A
  have hB : TotallyNonnegative B :=
    totallyNonnegative_mul hP.totallyNonnegative hA
  have hindB : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ B.col (cols j)) := by
    intro cols
    exact positiveCompression_preserves_ordered_independence
      (Nat.le_succ (p + 1)) hP hA cols (huniform cols)
  have hsupport := refinement_maximalMinor_eq_zero_iff hpn hB hindB J
  rw [positiveCompression_maximalMinor_eq_zero_iff_not_indep hP hA J] at hsupport
  rw [hsupport]
  constructor
  · intro h t ht
    exact (mem_firstCircuitZeroSet_iff hpn A t).2
      ((positiveCompression_maximalMinor_eq_zero_iff_not_indep hP hA
        (consecutiveColumns hpn t)).1 (h t ht))
  · intro h t ht
    apply (positiveCompression_maximalMinor_eq_zero_iff_not_indep hP hA
      (consecutiveColumns hpn t)).2
    exact (mem_firstCircuitZeroSet_iff hpn A t).1 (h t ht)

/-- The separated interval data occurring in Theorem 3.4. -/
structure FirstCircuitIntervalData
    {p m n : ℕ} (hpn : p + 1 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) where
  runCount : ℕ
  runs : ZeroRunDecomposition (firstCircuitZeroSet hpn A) runCount
  zeroSet_proper : firstCircuitZeroSet hpn A ≠ Finset.univ
  dependent_iff_interval : ∀ J : Fin (p + 2) ↪o Fin n,
    ¬(columnMatroid A).Indep (Set.range J) ↔
      ∃ a, ∀ i, J i ∈ runHyperplane hpn runs a
  pairwise_intersection : ∀ {a b : Fin runCount}, a ≠ b →
    ((runHyperplane hpn runs a) ∩ (runHyperplane hpn runs b)).card ≤ p

/-- Theorem 3.4(i,iii): first circuits are exactly the `(p+2)`-subsets lying
in enlarged maximal zero runs, and distinct intervals meet in at most `p`
elements. -/
theorem exists_firstCircuitIntervalData
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (hrank : ∃ J : Fin (p + 2) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 2) ↦ A.col (J j))) :
    Nonempty (FirstCircuitIntervalData hpn A) := by
  obtain ⟨runCount, ⟨D⟩⟩ :=
    exists_zeroRunDecomposition (firstCircuitZeroSet hpn A)
  have hproper : firstCircuitZeroSet hpn A ≠ Finset.univ := by
    rintro hzero
    obtain ⟨J, hJ⟩ := hrank
    have hJind : (columnMatroid A).Indep (Set.range J) :=
      (columnMatroid_indep_range_iff A J).2 hJ
    have hdep : ¬(columnMatroid A).Indep (Set.range J) :=
      (firstCircuit_dependent_iff_all_anchors hpn hA hP huniform J).2 (by
        intro t _
        rw [hzero]
        simp)
    exact hdep hJind
  refine ⟨{
    runCount := runCount
    runs := D
    zeroSet_proper := hproper
    dependent_iff_interval := ?_
    pairwise_intersection := ?_ }⟩
  · intro J
    rw [firstCircuit_dependent_iff_all_anchors hpn hA hP huniform J]
    constructor
    · intro hanchors
      apply (allAnchors_mem_iff_exists_columns_mem_runHyperplane hpn D J).1
      intro t ht
      exact hanchors t (by simp [anchorFinset, ht])
    · intro hinterval t ht
      apply (allAnchors_mem_iff_exists_columns_mem_runHyperplane hpn D J).2
        hinterval
      simpa [anchorFinset] using ht
  · intro a b hab
    simpa using card_runHyperplane_inter_le hpn D hab

/-- Theorem 3.4(ii), constructive direction: every enlarged zero-run interval
is a flat of the original matroid, and its first `p+1` columns form a basis of
that flat.  In particular, its rank in the original matroid is exactly
`p+1`, not merely its rank after compression. -/
theorem firstCircuit_runHyperplane_isFlat
    {p m n : ℕ} {hpn : p + 1 < n}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (D : FirstCircuitIntervalData hpn A) (a : Fin D.runCount) :
    (columnMatroid A).IsFlat
        (runHyperplane hpn D.runs a : Set (Fin n)) ∧
      (columnMatroid A).IsBasis
        (Set.range (runCoreColumns hpn D.runs a))
        (runHyperplane hpn D.runs a : Set (Fin n)) := by
  let M := columnMatroid A
  let H : Set (Fin n) := runHyperplane hpn D.runs a
  let core : Fin (p + 1) ↪o Fin n := runCoreColumns hpn D.runs a
  let I : Set (Fin n) := Set.range core
  have hIind : M.Indep I := by
    apply (columnMatroid_indep_range_iff A core).2
    exact huniform core
  have hIH : I ⊆ H := by
    rintro _ ⟨i, rfl⟩
    exact runCoreColumns_mem_runHyperplane hpn D.runs a i
  have hHclosure : H ⊆ M.closure I := by
    intro y hyH
    by_cases hyI : y ∈ I
    · exact M.subset_closure I hIind.subset_ground hyI
    · let Jy := sortedAppendOne core y hyI
      have hJyRange : Set.range Jy = insert y I := by
        rw [range_sortedAppendOne]
        ext z
        simp [I]
      have hJyH : ∀ i, Jy i ∈ runHyperplane hpn D.runs a := by
        intro i
        have hi : Jy i ∈ Set.range Jy := ⟨i, rfl⟩
        rw [hJyRange] at hi
        rcases hi with (hi | hi)
        · rw [hi]
          exact hyH
        · exact hIH hi
      have hnotind : ¬M.Indep (Set.range Jy) :=
        (D.dependent_iff_interval Jy).2 ⟨a, hJyH⟩
      have hdep : M.Dep (insert y I) := by
        rw [← hJyRange, Matroid.dep_iff]
        exact ⟨hnotind, by simp [M]⟩
      exact (hIind.mem_closure_iff_of_notMem hyI).2 hdep
  have hIbasis : M.IsBasis I H :=
    hIind.isBasis_of_subset_of_subset_closure hIH hHclosure
  have hclosureIH : M.closure I = M.closure H := hIbasis.closure_eq_closure
  have houtside_ind : ∀ (x : Fin n), x ∉ H → M.Indep (insert x I) := by
    intro x hxH
    have hxI : x ∉ I := fun hx ↦ hxH (hIH hx)
    let Jx := sortedAppendOne core x hxI
    have hJxRange : Set.range Jx = insert x I := by
      rw [range_sortedAppendOne]
      ext z
      simp [I]
    rw [← hJxRange]
    by_contra hnotind
    obtain ⟨b, hb⟩ := (D.dependent_iff_interval Jx).1 hnotind
    have hxJ : x ∈ Set.range Jx := by
      rw [hJxRange]
      simp
    have hxb : x ∈ runHyperplane hpn D.runs b := by
      obtain ⟨i, hi⟩ := hxJ
      rw [← hi]
      exact hb i
    by_cases hba : b = a
    · subst b
      exact hxH hxb
    · let s : Finset (Fin n) := Finset.univ.map core.toEmbedding
      have hscard : s.card = p + 1 := by simp [s]
      have hsub :
          s ⊆ runHyperplane hpn D.runs a ∩ runHyperplane hpn D.runs b := by
        intro z hz
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hz
        apply Finset.mem_inter.mpr
        refine ⟨runCoreColumns_mem_runHyperplane hpn D.runs a i, ?_⟩
        have hi : core i ∈ Set.range Jx := by
          rw [hJxRange]
          exact Or.inr ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := hi
        change core i ∈ runHyperplane hpn D.runs b
        rw [← hj]
        exact hb j
      have hcard := Finset.card_le_card hsub
      have hinter := D.pairwise_intersection (Ne.symm hba)
      rw [hscard] at hcard
      omega
  have hclosure : M.closure H = H := by
    apply Set.Subset.antisymm
    · intro x hxcl
      by_contra hxH
      have hxI : x ∉ I := fun hx ↦ hxH (hIH hx)
      have hxclI : x ∈ M.closure I := by
        rw [hclosureIH]
        exact hxcl
      have hxind := houtside_ind x hxH
      exact ((hIind.notMem_closure_iff_of_notMem hxI).2 hxind) hxclI
    · exact M.subset_closure H (by simp [M])
  exact ⟨Matroid.isFlat_iff_closure_eq.2 hclosure, hIbasis⟩

/-- A rank-`p+1` flat with at least `p+2` elements, expressed without a
separate matroid-rank API. -/
def IsLargeFirstCircuitFlat {p n : ℕ} (M : Matroid (Fin n))
    (F : Set (Fin n)) : Prop :=
  M.IsFlat F ∧
    ∃ K : Fin (p + 1) ↪o Fin n,
      M.IsBasis (Set.range K) F ∧
        ∃ x ∈ F, x ∉ Set.range K

/-- Theorem 3.4(ii), exhaustion direction: the enlarged maximal zero runs
are precisely the large rank-`p+1` flats of the original matroid. -/
theorem isLargeFirstCircuitFlat_iff_runHyperplane
    {p m n : ℕ} {hpn : p + 1 < n}
    {A : Matrix (Fin m) (Fin n) ℝ}
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (D : FirstCircuitIntervalData hpn A) (F : Set (Fin n)) :
    IsLargeFirstCircuitFlat (p := p) (columnMatroid A) F ↔
      ∃ a, F = (runHyperplane hpn D.runs a : Set (Fin n)) := by
  let M := columnMatroid A
  constructor
  · rintro ⟨hFflat, K, hKbasis, x, hxF, hxK⟩
    let J := sortedAppendOne K x hxK
    have hJrange : Set.range J = insert x (Set.range K) := by
      rw [range_sortedAppendOne]
      ext z
      simp
    have hJdep : M.Dep (Set.range J) := by
      rw [hJrange]
      exact hKbasis.insert_dep ⟨hxF, hxK⟩
    obtain ⟨a, hJa⟩ := (D.dependent_iff_interval J).1 hJdep.not_indep
    let H : Set (Fin n) := runHyperplane hpn D.runs a
    have hKH : Set.range K ⊆ H := by
      intro z hz
      have hzJ : z ∈ Set.range J := by
        rw [hJrange]
        exact Or.inr hz
      obtain ⟨i, hi⟩ := hzJ
      rw [← hi]
      exact hJa i
    have hKind : M.Indep (Set.range K) := hKbasis.indep
    have hHclosure : H ⊆ M.closure (Set.range K) := by
      intro y hyH
      by_cases hyK : y ∈ Set.range K
      · exact M.subset_closure _ hKind.subset_ground hyK
      · let Jy := sortedAppendOne K y hyK
        have hJyRange : Set.range Jy = insert y (Set.range K) := by
          rw [range_sortedAppendOne]
          ext z
          simp
        have hJyH : ∀ i, Jy i ∈ runHyperplane hpn D.runs a := by
          intro i
          have hi : Jy i ∈ Set.range Jy := ⟨i, rfl⟩
          rw [hJyRange] at hi
          rcases hi with hi | hi
          · rw [hi]
            exact hyH
          · exact hKH hi
        have hnotind : ¬M.Indep (Set.range Jy) :=
          (D.dependent_iff_interval Jy).2 ⟨a, hJyH⟩
        have hdep : M.Dep (insert y (Set.range K)) := by
          rw [← hJyRange, Matroid.dep_iff]
          exact ⟨hnotind, by simp [M]⟩
        exact (hKind.mem_closure_iff_of_notMem hyK).2 hdep
    have hKbasisH : M.IsBasis (Set.range K) H :=
      hKind.isBasis_of_subset_of_subset_closure hKH hHclosure
    have hHflat := (firstCircuit_runHyperplane_isFlat huniform D a).1
    refine ⟨a, ?_⟩
    rw [← hFflat.closure, ← hHflat.closure]
    exact hKbasis.closure_eq_closure.symm.trans hKbasisH.closure_eq_closure
  · rintro ⟨a, rfl⟩
    obtain ⟨hflat, hbasis⟩ := firstCircuit_runHyperplane_isFlat huniform D a
    refine ⟨hflat, runCoreColumns hpn D.runs a, hbasis, ?_⟩
    let x : Fin n := runFullColumns hpn D.runs a (Fin.last (p + 1))
    refine ⟨x, runFullColumns_mem_runHyperplane hpn D.runs a _, ?_⟩
    rintro ⟨i, hi⟩
    have hval := congrArg Fin.val hi
    simp only [x, runFullColumns, runCoreColumns,
      OrderEmbedding.coe_ofStrictMono, Fin.val_last] at hval
    have hi' := i.isLt
    omega

/-- The positive codimension-one model used to orient first-layer circuits. -/
def firstCircuitProjection
    {p m n : ℕ} (P : Matrix (Fin (p + 2)) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (p + 1)) (Fin n) ℝ :=
  firstRows (projectionTransform (P * A))

/-- A projection-normalized alternating circuit of a dependent selection is
also a kernel vector of the original matrix.  This is the kernel-line transfer
used in the final paragraph of the proof of Theorem 3.6. -/
theorem firstCircuitProjection_alternatingCircuit_mem_original_kernel
    {p m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (J : Fin (p + 2) ↪o Fin n)
    (hJ : ¬(columnMatroid A).Indep (Set.range J)) :
    A *ᵥ alternatingCircuit (firstCircuitProjection P A) J = 0 := by
  let U : Matrix (Fin (p + 1)) (Fin n) ℝ := firstCircuitProjection P A
  let Q : Matrix (Fin (p + 1)) (Fin m) ℝ := projectionQ (p + 1) * P
  have hQA : Q * A = U := by
    change (projectionQ (p + 1) * P) * A =
      firstRows (projectionTransform (P * A))
    rw [firstRows_projectionTransform]
    unfold projectedMatrix
    rw [Matrix.mul_assoc]
  funext row
  let selector : Fin m → ℝ := fun i => if i = row then 1 else 0
  let R : Matrix (Fin (p + 2)) (Fin m) ℝ := appendLastRow Q selector
  have hRA : R * A = appendLastRow U (A row) := by
    ext i j
    cases i using Fin.lastCases with
    | last =>
        simp only [Matrix.mul_apply, R, appendLastRow_last]
        rw [Finset.sum_eq_single row]
        · simp [selector]
        · intro b hb hbr
          simp [selector, hbr]
        · simp
    | cast i =>
        simp only [Matrix.mul_apply, R, appendLastRow_castSucc]
        exact congrFun (congrFun hQA i) j
  have hdet : matrixMaximalMinor (appendLastRow U (A row)) J = 0 := by
    by_contra hne
    have hLIappend : LinearIndependent ℝ
        (fun j : Fin (p + 2) ↦ (appendLastRow U (A row)).col (J j)) := by
      rw [← orderedMinor_ne_zero_iff_linearIndependent_columns]
      exact hne
    have hLIRA : LinearIndependent ℝ
        (fun j : Fin (p + 2) ↦ (R * A).col (J j)) := by
      rwa [hRA]
    have hLIA := positiveCompression_reflects_ordered_independence R A J hLIRA
    apply hJ
    exact (columnMatroid_indep_range_iff A J).2 hLIA
  have hpair := appendLastRow_maximalMinor_eq_circuit_pairing U J (A row)
  rw [hdet] at hpair
  have hsign : (-1 : ℝ) ^ (p + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzero : (∑ j, alternatingCircuit U J j * A row j) = 0 := by
    exact (mul_eq_zero.mp hpair.symm).resolve_left hsign
  simpa [Matrix.mulVec, dotProduct, U, mul_comm] using hzero

/-- Theorem 3.6 in its checked projection model.  The alternating circuit of
every first-layer selection is a positive combination of all consecutive
alternating circuits in its span, and dependence in the original matrix
guarantees that every anchor appearing in that sum is itself dependent in
the original matrix. -/
theorem exists_positive_firstCircuit_subdivision
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (J : Fin (p + 2) ↪o Fin n)
    (hJ : ¬(columnMatroid A).Indep (Set.range J)) :
    Nonempty (FullPositiveModuleAnchorExpansion
        (alternatingCircuit (firstCircuitProjection P A) J)
        (fun t ↦ alternatingCircuit (firstCircuitProjection P A)
          (consecutiveColumns hpn t))
        (anchorFinset J)) ∧
      ∀ t ∈ anchorFinset J,
        ¬(columnMatroid A).Indep
          (Set.range (consecutiveColumns hpn t)) := by
  let B : Matrix (Fin (p + 2)) (Fin n) ℝ := P * A
  have hB : TotallyNonnegative B :=
    totallyNonnegative_mul hP.totallyNonnegative hA
  have hindB : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ B.col (cols j)) := by
    intro cols
    exact positiveCompression_preserves_ordered_independence
      (Nat.le_succ (p + 1)) hP hA cols (huniform cols)
  have hpos : ∀ cols : Fin (p + 1) ↪o Fin n,
      0 < orderedMinor (firstCircuitProjection P A)
        (allRows (p + 1)) cols := by
    intro cols
    exact firstRows_projectionTransform_maximalMinor_pos hB hindB cols
  obtain ⟨E⟩ := exists_positive_alternatingCircuit_subdivision hpn
    (firstCircuitProjection P A) hpos J
  refine ⟨⟨E⟩, ?_⟩
  have hall :=
    (firstCircuit_dependent_iff_all_anchors hpn hA hP huniform J).1 hJ
  intro t ht
  exact (mem_firstCircuitZeroSet_iff hpn A t).1 (hall t ht)

/-- Theorem 3.6 in the original matrix: the same positive subdivision from
the canonical projection is an identity among kernel vectors of `A`, both for
the given circuit and for every consecutive anchor in its span. -/
theorem exists_positive_firstCircuit_subdivision_original
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (J : Fin (p + 2) ↪o Fin n)
    (hJ : ¬(columnMatroid A).Indep (Set.range J)) :
    Nonempty (FullPositiveModuleAnchorExpansion
        (alternatingCircuit (firstCircuitProjection P A) J)
        (fun t ↦ alternatingCircuit (firstCircuitProjection P A)
          (consecutiveColumns hpn t))
        (anchorFinset J)) ∧
      A *ᵥ alternatingCircuit (firstCircuitProjection P A) J = 0 ∧
      ∀ t ∈ anchorFinset J,
        A *ᵥ alternatingCircuit (firstCircuitProjection P A)
          (consecutiveColumns hpn t) = 0 := by
  obtain ⟨hE, hanchors⟩ :=
    exists_positive_firstCircuit_subdivision hpn hA hP huniform J hJ
  refine ⟨hE,
    firstCircuitProjection_alternatingCircuit_mem_original_kernel J hJ, ?_⟩
  intro t ht
  exact firstCircuitProjection_alternatingCircuit_mem_original_kernel
    (consecutiveColumns hpn t) (hanchors t ht)

/-- Corollary 3.5, support-level form: the first circuit layer has an
all-minor totally nonnegative Toeplitz realization with exactly the same
dependent `(p+2)`-subsets. -/
theorem exists_toeplitz_realization_of_firstCircuitLayer
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (hrank : ∃ J : Fin (p + 2) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 2) ↦ A.col (J j))) :
    ∃ R : ClassifiedToeplitzRealization (p + 1) n hpn
        (firstCircuitZeroSet hpn A),
      ∀ J : Fin (p + 2) ↪o Fin n,
        matrixMaximalMinor R.matrix J = 0 ↔
          ¬(columnMatroid A).Indep (Set.range J) := by
  obtain ⟨D⟩ := exists_firstCircuitIntervalData hpn hA hP huniform hrank
  obtain ⟨R⟩ := exists_classifiedToeplitzRealization
    (Nat.succ_pos p) hpn (firstCircuitZeroSet hpn A) D.zeroSet_proper
  refine ⟨R, fun J ↦ ?_⟩
  rw [firstCircuit_dependent_iff_all_anchors hpn hA hP huniform J]
  constructor
  · intro hzero t ht
    by_contra htZ
    have hbasis := (R.basis_rule J).2 ⟨t, ht, htZ⟩
    exact hbasis hzero
  · intro hall
    by_contra hnonzero
    obtain ⟨t, ht, htZ⟩ := (R.basis_rule J).1 hnonzero
    exact htZ (hall t ht)

/-- Two full-row-rank matrices with the same maximal-minor support represent
the same column matroid. -/
theorem columnMatroid_eq_of_fullRowRank_of_maximalMinor_support
    {k n : ℕ} {A B : Matrix (Fin k) (Fin n) ℝ}
    (hAfull : HasFullRowRank A) (hBfull : HasFullRowRank B)
    (hsupport : ∀ J : Fin k ↪o Fin n,
      orderedMinor A (allRows k) J ≠ 0 ↔
        orderedMinor B (allRows k) J ≠ 0) :
    columnMatroid A = columnMatroid B := by
  obtain ⟨JA, hJAbase⟩ :=
    (hasFullRowRank_iff_exists_columnMatroid_isBase A).1 hAfull
  obtain ⟨JB, hJBbase⟩ :=
    (hasFullRowRank_iff_exists_columnMatroid_isBase B).1 hBfull
  apply Matroid.ext_isBase
  · rw [columnMatroid_ground, columnMatroid_ground]
  · intro S hSground
    constructor
    · intro hSA
      have hScard : S.ncard = k := by
        rw [hSA.ncard_eq_ncard_of_isBase hJAbase]
        simpa using Set.ncard_range_of_injective JA.injective
      let hSfin : S.Finite := Set.toFinite S
      let s : Finset (Fin n) := hSfin.toFinset
      let J : Fin k ↪o Fin n := s.orderEmbOfFin (by
        dsimp only [s]
        rw [← Set.ncard_eq_toFinset_card S hSfin]
        exact hScard)
      have hJrange : Set.range J = S := by
        rw [Finset.range_orderEmbOfFin]
        exact hSfin.coe_toFinset
      rw [← hJrange]
      apply (columnMatroid_isBase_range_iff B J).2
      apply (hsupport J).1
      apply (columnMatroid_isBase_range_iff A J).1
      simpa [hJrange] using hSA
    · intro hSB
      have hScard : S.ncard = k := by
        rw [hSB.ncard_eq_ncard_of_isBase hJBbase]
        simpa using Set.ncard_range_of_injective JB.injective
      let hSfin : S.Finite := Set.toFinite S
      let s : Finset (Fin n) := hSfin.toFinset
      let J : Fin k ↪o Fin n := s.orderEmbOfFin (by
        dsimp only [s]
        rw [← Set.ncard_eq_toFinset_card S hSfin]
        exact hScard)
      have hJrange : Set.range J = S := by
        rw [Finset.range_orderEmbOfFin]
        exact hSfin.coe_toFinset
      rw [← hJrange]
      apply (columnMatroid_isBase_range_iff A J).2
      apply (hsupport J).2
      apply (columnMatroid_isBase_range_iff B J).1
      simpa [hJrange] using hSB

/-- Corollary 3.5 in full matroid form: the classified Toeplitz realization
represents the rank-`p+2` truncation, not only the same maximal support. -/
theorem exists_toeplitz_realization_of_firstCircuitLayer_truncation
    {p m n : ℕ} (hpn : p + 1 < n)
    {A : Matrix (Fin m) (Fin n) ℝ}
    {P : Matrix (Fin (p + 2)) (Fin m) ℝ}
    (hA : TotallyNonnegative A) (hP : TotallyPositive P)
    (huniform : ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ A.col (cols j)))
    (hrank : ∃ J : Fin (p + 2) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 2) ↦ A.col (J j))) :
    ∃ R : ClassifiedToeplitzRealization (p + 1) n hpn
        (firstCircuitZeroSet hpn A),
      IsRankTruncationOf (p + 2) (columnMatroid R.matrix)
        (columnMatroid A) := by
  obtain ⟨R, hsupport⟩ :=
    exists_toeplitz_realization_of_firstCircuitLayer
      hpn hA hP huniform hrank
  let B : Matrix (Fin (p + 2)) (Fin n) ℝ := P * A
  have hBfull : HasFullRowRank B := by
    obtain ⟨J, hJ⟩ := hrank
    refine ⟨J, ?_⟩
    rw [orderedMinor_ne_zero_iff_linearIndependent_columns]
    exact positiveCompression_preserves_ordered_independence
      le_rfl hP hA J hJ
  have hRBsupport : ∀ J : Fin (p + 2) ↪o Fin n,
      matrixMaximalMinor R.matrix J ≠ 0 ↔
        matrixMaximalMinor B J ≠ 0 := by
    intro J
    have hzeroB : matrixMaximalMinor B J = 0 ↔
        ¬(columnMatroid A).Indep (Set.range J) := by
      change matrixMaximalMinor (P * A) J = 0 ↔ _
      exact positiveCompression_maximalMinor_eq_zero_iff_not_indep hP hA J
    exact not_congr ((hsupport J).trans hzeroB.symm)
  have hmatroid : columnMatroid R.matrix = columnMatroid B :=
    columnMatroid_eq_of_fullRowRank_of_maximalMinor_support
      R.fullRowRank hBfull (by simpa [matrixMaximalMinor] using hRBsupport)
  refine ⟨R, ?_⟩
  rw [hmatroid]
  exact positiveCompression_isRankTruncation hP hA

end

end FurtherToeplitzPositroids
