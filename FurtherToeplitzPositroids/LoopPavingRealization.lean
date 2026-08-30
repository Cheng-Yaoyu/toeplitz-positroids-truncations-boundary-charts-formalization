import FurtherToeplitzPositroids.QuantumChart
import FurtherToeplitzPositroids.LoopPavingClassification

/-!
# Realization of compatible loop-paving zero patterns

This module implements equations (38)--(39).  Boundary bits determine which
protected endpoint minors occur in the nonloop window, while every interior
coordinate is supplied by the quantum inverse-function chart.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Matrix PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- Arithmetic data of the target window in equations (38)--(39.  The
numbers `left` and `right` are the `0/1` loop-boundary indicators. -/
structure LoopBoundaryWindow (N d : ℕ) where
  left : ℕ
  right : ℕ
  left_le_one : left ≤ 1
  right_le_one : right ≤ 1
  bandwidth_eq : d + left + right = N + 1
  bandwidth_ge_two : 1 < d

def LoopBoundaryWindow.start {N d : ℕ} (W : LoopBoundaryWindow N d) : ℕ :=
  1 - W.left

theorem LoopBoundaryWindow.start_add_left {N d : ℕ}
    (W : LoopBoundaryWindow N d) : W.start + W.left = 1 := by
  unfold start
  have hl := W.left_le_one
  omega

theorem LoopBoundaryWindow.start_le_one {N d : ℕ}
    (W : LoopBoundaryWindow N d) : W.start ≤ 1 := by
  unfold start
  omega

theorem LoopBoundaryWindow.target_last {N d : ℕ}
    (W : LoopBoundaryWindow N d) (hN : 0 < N) :
    W.start + (N - 1) = d - 1 + W.right := by
  have hd := W.bandwidth_eq
  have hs := W.start_add_left
  have hl := W.left_le_one
  have hr := W.right_le_one
  have hb := W.bandwidth_ge_two
  omega

/-- Target consecutive coordinate `u` is the full-band anchor `start+u`. -/
def LoopBoundaryWindow.targetAnchor {N d : ℕ}
    (W : LoopBoundaryWindow N d) : Fin N ↪o Fin (d + 1) :=
  OrderEmbedding.ofStrictMono
    (fun u => ⟨W.start + u.val, by
      have hu := u.isLt
      have hd := W.bandwidth_eq
      have hs := W.start_add_left
      have hl := W.left_le_one
      have hr := W.right_le_one
      omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) W.start)

/-- Interior coordinate `t` corresponds to target coordinate `t+left`. -/
def LoopBoundaryWindow.interiorTarget {N d : ℕ}
    (W : LoopBoundaryWindow N d) : Fin (d - 1) ↪o Fin N :=
  OrderEmbedding.ofStrictMono
    (fun t => ⟨t.val + W.left, by
      have ht := t.isLt
      have hd := W.bandwidth_eq
      have hr := W.right_le_one
      omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_right (Fin.mk_lt_mk.mp hij) W.left)

theorem LoopBoundaryWindow.targetAnchor_interiorTarget
    {N d : ℕ} (W : LoopBoundaryWindow N d) (t : Fin (d - 1)) :
    W.targetAnchor (W.interiorTarget t) = ⟨t.val + 1, by omega⟩ := by
  apply Fin.ext
  change W.start + (t.val + W.left) = t.val + 1
  have hs := W.start_add_left
  omega

/-- Pull an admissible target zero set back to the interior chart. -/
def LoopBoundaryWindow.interiorZeroSet
    {N d : ℕ} (W : LoopBoundaryWindow N d) (Z : Finset (Fin N)) :
    Finset (Fin (d - 1)) :=
  Finset.univ.filter fun t => W.interiorTarget t ∈ Z

@[simp] theorem LoopBoundaryWindow.mem_interiorZeroSet_iff
    {N d : ℕ} (W : LoopBoundaryWindow N d) (Z : Finset (Fin N))
    (t : Fin (d - 1)) :
    t ∈ W.interiorZeroSet Z ↔ W.interiorTarget t ∈ Z := by
  simp [interiorZeroSet]

/-! ## The nonloop window -/

/-- The physical nonloop column window has length `N+r`. -/
def LoopBoundaryWindow.windowColumns
    {N d : ℕ} (W : LoopBoundaryWindow N d) (r : ℕ) :
    Fin (N + r) ↪o Fin (d + r + 1) :=
  OrderEmbedding.ofStrictMono
    (fun j => ⟨W.start + j.val, by
      have hj := j.isLt
      have hN : 0 < N := by
        have hd := W.bandwidth_eq
        have hb := W.bandwidth_ge_two
        omega
      have hb := W.bandwidth_ge_two
      have hlast := W.target_last hN
      have hr := W.right_le_one
      have hstartN : W.start + N ≤ d + 1 := by
        calc
          W.start + N = (W.start + (N - 1)) + 1 := by omega
          _ = (d - 1 + W.right) + 1 := by rw [hlast]
          _ ≤ d + 1 := by omega
      calc
        W.start + j.val < W.start + (N + r) :=
          Nat.add_lt_add_left hj _
        _ = (W.start + N) + r := by omega
        _ ≤ (d + 1) + r := Nat.add_le_add_right hstartN r
        _ = d + r + 1 := by omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) W.start)

/-- Target anchor in the exact finite type expected by the full matrix. -/
def LoopBoundaryWindow.targetAnchorFull
    {N d : ℕ} (W : LoopBoundaryWindow N d) (r : ℕ) :
    Fin N ↪o Fin (d + r + 1 - r) :=
  OrderEmbedding.ofStrictMono
    (fun u => ⟨W.start + u.val, by
      have hu := u.isLt
      have hN : 0 < N := by
        have hd := W.bandwidth_eq
        have hb := W.bandwidth_ge_two
        omega
      have hb := W.bandwidth_ge_two
      have hlast := W.target_last hN
      have hr := W.right_le_one
      rw [show d + r + 1 - r = d + 1 by omega]
      have huLe : u.val ≤ N - 1 := by omega
      calc
        W.start + u.val ≤ W.start + (N - 1) :=
          Nat.add_le_add_left huLe _
        _ = d - 1 + W.right := hlast
        _ ≤ (d - 1) + 1 := Nat.add_le_add_left hr _
        _ = d := by omega
        _ < d + 1 := Nat.lt_succ_self d⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) W.start)

theorem LoopBoundaryWindow.targetAnchorFull_apply_val
    {N d : ℕ} (W : LoopBoundaryWindow N d) (r : ℕ) (u : Fin N) :
    (W.targetAnchorFull r u).val = W.start + u.val := rfl

/-- Restrict the quantum band matrix to the target nonloop window. -/
def LoopBoundaryWindow.nonloopMatrix
    {N d : ℕ} (W : LoopBoundaryWindow N d) (r : ℕ)
    (x : Fin (d - 1) → ℝ) : Matrix (Fin (r + 1)) (Fin (N + r)) ℝ :=
  (quantumSliceMatrix r d x).submatrix (allRows (r + 1))
    (W.windowColumns r)

/-- Consecutive minors of the window are the target consecutive minors of
the full quantum slice. -/
theorem LoopBoundaryWindow.nonloopMatrix_consecutiveMinor
    {N d r : ℕ} (W : LoopBoundaryWindow N d)
    (x : Fin (d - 1) → ℝ) (u : Fin N) :
    matrixConsecutiveMinor (show r < N + r by
      have hN : 0 < N := by
        have hd := W.bandwidth_eq
        have hb := W.bandwidth_ge_two
        omega
      omega) (W.nonloopMatrix r x) ⟨u.val, by
        rw [show N + r - r = N by omega]
        exact u.isLt⟩ =
      matrixConsecutiveMinor (show r < d + r + 1 by omega)
        (quantumSliceMatrix r d x) (W.targetAnchorFull r u) := by
  unfold matrixConsecutiveMinor matrixMaximalMinor orderedMinor nonloopMatrix
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    consecutiveColumns_apply_val, windowColumns, targetAnchorFull]
  congr 1
  apply Fin.ext
  change W.start + (u.val + j.val) = W.start + u.val + j.val
  omega

theorem LoopBoundaryWindow.nonloopMatrix_totallyNonnegative
    {N d r : ℕ} (W : LoopBoundaryWindow N d)
    {delta : Fin (d - 1) → ℝ}
    (R : QuantumTargetRealization r d W.bandwidth_ge_two delta) :
    TotallyNonnegative (W.nonloopMatrix r R.source) :=
  R.totallyNonnegative.submatrix (allRows (r + 1)) (W.windowColumns r)

theorem LoopBoundaryWindow.nonloopMatrix_columns_independent
    {N d r q : ℕ} (W : LoopBoundaryWindow N d)
    {delta : Fin (d - 1) → ℝ}
    (R : QuantumTargetRealization r d W.bandwidth_ge_two delta)
    (hq : q ≤ r) (cols : Fin q ↪o Fin (N + r)) :
    LinearIndependent ℝ
      (fun j : Fin q => (W.nonloopMatrix r R.source).col (cols j)) := by
  let fullCols := cols.trans (W.windowColumns r)
  have hfull := R.columns_independent q hq fullCols
  simpa [nonloopMatrix, fullCols, Matrix.submatrix_apply] using hfull

/-! ## Exact target zero pattern -/

theorem LoopBoundaryWindow.nonloopMatrix_consecutive_eq_zero_iff
    {N d r : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N)
    {Z : Finset (Fin N)}
    (hleft : W.left = 1 → (⟨0, hN⟩ : Fin N) ∉ Z)
    (hright : W.right = 1 → lastLoopIndex N hN ∉ Z)
    {delta : Fin (d - 1) → ℝ}
    (R : QuantumTargetRealization r d W.bandwidth_ge_two delta)
    (hdelta : ∀ t, delta t = 0 ↔ t ∈ W.interiorZeroSet Z)
    (u : Fin N) :
    matrixConsecutiveMinor (show r < N + r by omega)
      (W.nonloopMatrix r R.source) ⟨u.val, by
        rw [show N + r - r = N by omega]
        exact u.isLt⟩ = 0 ↔ u ∈ Z := by
  rw [W.nonloopMatrix_consecutiveMinor R.source u]
  let anchor := W.targetAnchorFull r u
  change matrixConsecutiveMinor (show r < d + r + 1 by omega)
    (quantumSliceMatrix r d R.source) anchor = 0 ↔ u ∈ Z
  by_cases hzero : anchor.val = 0
  · have ha : anchor = ⟨0, by omega⟩ := Fin.ext hzero
    have hstartZero : W.start = 0 := by
      change W.start + u.val = 0 at hzero
      omega
    have hleftOne : W.left = 1 := by
      have hs := W.start_add_left
      omega
    have huZero : u = ⟨0, hN⟩ := by
      apply Fin.ext
      change u.val = 0
      change W.start + u.val = 0 at hzero
      omega
    have huNot : u ∉ Z := by
      rw [huZero]
      exact hleft hleftOne
    rw [ha, R.firstConsecutive_eq]
    simp [huNot]
  · by_cases hlast : anchor.val = d
    · have ha : anchor = ⟨d, by omega⟩ := Fin.ext hlast
      have htargetLast := W.target_last hN
      have huLe : u.val ≤ N - 1 := by omega
      have hlastVal : W.start + u.val = d := by
        change W.start + u.val = d at hlast
        exact hlast
      have hrightOne : W.right = 1 := by
        have hr := W.right_le_one
        have hb := W.bandwidth_ge_two
        omega
      have huLast : u = lastLoopIndex N hN := by
        apply Fin.ext
        dsimp only [lastLoopIndex]
        omega
      have huNot : u ∉ Z := by
        rw [huLast]
        exact hright hrightOne
      rw [ha, R.lastConsecutive_eq]
      simp [huNot]
    · have hanchorPos : 0 < anchor.val := by omega
      have hanchorLt : anchor.val < d := by
        have haBound := anchor.isLt
        have hcard : d + r + 1 - r = d + 1 := by omega
        omega
      let t : Fin (d - 1) := ⟨anchor.val - 1, by omega⟩
      have hinterior : W.interiorTarget t = u := by
        apply Fin.ext
        change (anchor.val - 1) + W.left = u.val
        have hs := W.start_add_left
        have hanchorVal : anchor.val = W.start + u.val := rfl
        omega
      have hanchorEq : quantumInteriorAnchor (r := r)
          W.bandwidth_ge_two t = anchor := by
        apply Fin.ext
        change (anchor.val - 1) + 1 = anchor.val
        omega
      rw [← hanchorEq, R.interiorConsecutive_eq, hdelta,
        W.mem_interiorZeroSet_iff, hinterior]

/-- Reindex a target zero set into the exact anchor type of the window. -/
def targetZeroSetInWindow {N : ℕ} (r : ℕ) (Z : Finset (Fin N)) :
    Finset (Fin (N + r - r)) :=
  Z.map (finCongr (by omega : N = N + r - r)).toEmbedding

@[simp] theorem mem_targetZeroSetInWindow_iff
    {N : ℕ} (r : ℕ) (Z : Finset (Fin N)) (u : Fin N) :
    finCongr (by omega : N = N + r - r) u ∈ targetZeroSetInWindow r Z ↔
      u ∈ Z := by
  simp [targetZeroSetInWindow]

/-- Complete matrix-level realization data for a loop-free paving core. -/
structure LoopPavingCoreRealization
    {N d : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N) (p : ℕ)
    (Z : Finset (Fin N)) where
  delta : Fin (d - 1) → ℝ
  quantum : QuantumTargetRealization (p + 1) d W.bandwidth_ge_two delta
  delta_zero_iff : ∀ t, delta t = 0 ↔ t ∈ W.interiorZeroSet Z
  fullRowRank : HasFullRowRank (W.nonloopMatrix (p + 1) quantum.source)
  consecutiveZeroSet_eq :
    loopPavingZeroSet (show p + 1 < N + (p + 1) by omega)
      (W.nonloopMatrix (p + 1) quantum.source) =
        targetZeroSetInWindow (p + 1) Z
  maximalSupport : ∀ J : Fin (p + 2) ↪o Fin (N + (p + 1)),
    matrixMaximalMinor (W.nonloopMatrix (p + 1) quantum.source) J ≠ 0 ↔
      LoopPavingBasisPredicate (targetZeroSetInWindow (p + 1) Z) J

/-- The realization direction of Theorem 6.2 for every quantum-chart window
with `d ≥ 2`. -/
theorem exists_loopPavingCoreRealization
    {N d p : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N)
    (Z : Finset (Fin N)) (hZ : Z ≠ Finset.univ)
    (hleft : W.left = 1 → (⟨0, hN⟩ : Fin N) ∉ Z)
    (hright : W.right = 1 → lastLoopIndex N hN ∉ Z) :
    Nonempty (LoopPavingCoreRealization W hN p Z) := by
  obtain ⟨delta, ⟨R⟩, hdelta⟩ :=
    exists_quantumZeroPatternRealization (show 0 < p + 1 by omega)
      W.bandwidth_ge_two
      (W.interiorZeroSet Z)
  let A := W.nonloopMatrix (p + 1) R.source
  have hTN : TotallyNonnegative A := W.nonloopMatrix_totallyNonnegative R
  have hind : ∀ cols : Fin (p + 1) ↪o Fin (N + (p + 1)),
      LinearIndependent ℝ (fun j : Fin (p + 1) => A.col (cols j)) := by
    intro cols
    exact W.nonloopMatrix_columns_independent R (le_refl (p + 1)) cols
  have hzeroExact : ∀ u : Fin N,
      matrixConsecutiveMinor (show p + 1 < N + (p + 1) by omega) A
        ⟨u.val, by
          rw [show N + (p + 1) - (p + 1) = N by omega]
          exact u.isLt⟩ = 0 ↔
        u ∈ Z := by
    intro u
    exact W.nonloopMatrix_consecutive_eq_zero_iff hN hleft hright
      R hdelta u
  have hzeroSet : loopPavingZeroSet
      (show p + 1 < N + (p + 1) by omega) A =
      targetZeroSetInWindow (p + 1) Z := by
    ext t
    let u : Fin N :=
      (finCongr (by omega : N = N + (p + 1) - (p + 1))).symm t
    have ht : finCongr (by omega : N = N + (p + 1) - (p + 1)) u = t := by
      exact (finCongr
        (by omega : N = N + (p + 1) - (p + 1))).apply_symm_apply t
    rw [mem_loopPavingZeroSet_iff]
    have hminor := hzeroExact u
    have harg : (⟨u.val, by
        rw [show N + (p + 1) - (p + 1) = N by omega]
        exact u.isLt⟩ : Fin (N + (p + 1) - (p + 1))) = t := by
      apply Fin.ext
      exact congrArg Fin.val ht
    have hminorArg : matrixConsecutiveMinor
        (show p + 1 < N + (p + 1) by omega) A t =
      matrixConsecutiveMinor (show p + 1 < N + (p + 1) by omega) A
        ⟨u.val, by
          rw [show N + (p + 1) - (p + 1) = N by omega]
          exact u.isLt⟩ := congrArg _ harg.symm
    rw [hminorArg, hminor]
    constructor
    · intro hu
      have hfu := (mem_targetZeroSetInWindow_iff (p + 1) Z u).2 hu
      rwa [ht] at hfu
    · intro htZ
      have hfu : finCongr
          (by omega : N = N + (p + 1) - (p + 1)) u ∈
          targetZeroSetInWindow (p + 1) Z := by
        rwa [ht]
      exact (mem_targetZeroSetInWindow_iff (p + 1) Z u).1 hfu
  have hfull : HasFullRowRank A := by
    have hexists : ∃ u : Fin N, u ∉ Z := by
      by_contra hall
      push Not at hall
      apply hZ
      ext u
      simp only [Finset.mem_univ, iff_true]
      exact hall u
    obtain ⟨u, hu⟩ := hexists
    let cols := consecutiveColumns (show p + 1 < N + (p + 1) by omega)
      ⟨u.val, by
        rw [show N + (p + 1) - (p + 1) = N by omega]
        exact u.isLt⟩
    refine ⟨cols, ?_⟩
    change matrixConsecutiveMinor (show p + 1 < N + (p + 1) by omega) A
      ⟨u.val, by
        rw [show N + (p + 1) - (p + 1) = N by omega]
        exact u.isLt⟩ ≠ 0
    exact (hzeroExact u).not.mpr hu
  have hsupport : ∀ J : Fin (p + 2) ↪o Fin (N + (p + 1)),
      matrixMaximalMinor A J ≠ 0 ↔
        LoopPavingBasisPredicate (targetZeroSetInWindow (p + 1) Z) J := by
    intro J
    rw [← hzeroSet]
    exact loopPaving_basisPredicate_exact
      (show p + 1 < N + (p + 1) by omega) hTN hind J
  exact ⟨{
    delta := delta
    quantum := R
    delta_zero_iff := hdelta
    fullRowRank := hfull
    consecutiveZeroSet_eq := hzeroSet
    maximalSupport := hsupport }⟩

/-! ## Low-bandwidth uniform cases -/

/-- Matrix data needed for the uniform (`Z = ∅`) low-bandwidth core. -/
structure UniformLoopPavingCoreRealization (p N : ℕ) where
  matrix : Matrix (Fin (p + 2)) (Fin (N + (p + 1))) ℝ
  totallyNonnegative : TotallyNonnegative matrix
  fullRowRank : HasFullRowRank matrix
  columns_independent : ∀ q, q ≤ p + 1 →
    ∀ cols : Fin q ↪o Fin (N + (p + 1)),
      LinearIndependent ℝ (fun j : Fin q => matrix.col (cols j))
  maximalMinor_pos : ∀ cols : Fin (p + 2) ↪o Fin (N + (p + 1)),
    0 < orderedMinor matrix (allRows (p + 2)) cols

/-- Width-one quantum window. -/
def widthOneWindowColumns (p N start : ℕ)
    (hstart : start + N ≤ 2) :
    Fin (N + (p + 1)) ↪o Fin (1 + (p + 1) + 1) :=
  OrderEmbedding.ofStrictMono
    (fun j => ⟨start + j.val, by
      have hj := j.isLt
      omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) start)

def widthOneCoreMatrix (p N start : ℕ)
    (hstart : start + N ≤ 2) :
    Matrix (Fin (p + 2)) (Fin (N + (p + 1))) ℝ :=
  (quantumBandMatrix (p + 1) 1).submatrix (allRows (p + 2))
    (widthOneWindowColumns p N start hstart)

theorem widthOneCoreMatrix_totallyNonnegative
    {p N start : ℕ} (hstart : start + N ≤ 2) :
    TotallyNonnegative (widthOneCoreMatrix p N start hstart) :=
  (quantumBandMatrix_oneWidth_totallyNonnegative (show 0 < p + 1 by omega))
    |>.submatrix (allRows (p + 2))
      (widthOneWindowColumns p N start hstart)

theorem widthOneCoreMatrix_columns_independent
    {p N start q : ℕ} (hstart : start + N ≤ 2)
    (hq : q ≤ p + 1) (cols : Fin q ↪o Fin (N + (p + 1))) :
    LinearIndependent ℝ
      (fun j : Fin q => (widthOneCoreMatrix p N start hstart).col (cols j)) := by
  let window := widthOneWindowColumns p N start hstart
  let fullCols := cols.trans window
  let rows := quantumFeasibleRows hq fullCols
  have hminor : orderedMinor (quantumBandMatrix (p + 1) 1) rows fullCols ≠ 0 :=
    ((quantumBandMatrix_oneWidth_minor_pos_iff_bandFeasible
      (show 0 < p + 1 by omega) rows fullCols).2
      (quantumFeasibleRows_bandFeasible hq fullCols)).ne'
  have hLI := linearIndependent_columns_of_nonzero_selectedMinor
    (quantumBandMatrix (p + 1) 1) rows fullCols hminor
  simpa [widthOneCoreMatrix, window, fullCols, Matrix.submatrix_apply] using hLI

theorem widthOneCoreMatrix_maximalMinor_pos
    {p N start : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2)
    (cols : Fin (p + 2) ↪o Fin (N + (p + 1))) :
    0 < orderedMinor (widthOneCoreMatrix p N start hstart)
      (allRows (p + 2)) cols := by
  let window := widthOneWindowColumns p N start hstart
  let fullCols := cols.trans window
  have hupper : ∀ t : Fin (p + 2),
      (cols t).val ≤ t.val + (N - 1) := by
    intro t
    have hrev := orderEmbedding_fin_val_lower_bound
      (reverseOrderEmbedding cols) (Fin.rev t)
    simp only [reverseOrderEmbedding_apply, Fin.rev_rev, Fin.val_rev] at hrev
    have htRev : (Fin.rev t).val + t.val + 1 = p + 2 := by
      simp only [Fin.val_rev]
      omega
    have hJRev : (Fin.rev (cols t)).val + (cols t).val + 1 =
        N + (p + 1) := by
      simp only [Fin.val_rev]
      omega
    omega
  have hband : BandFeasible (allRows (p + 2)) fullCols := by
    intro t
    have hlower := orderEmbedding_fin_val_lower_bound cols t
    have hu := hupper t
    change t.val ≤ start + (cols t).val ∧
      start + (cols t).val ≤ t.val + 1
    constructor
    · omega
    · omega
  have hpos := (quantumBandMatrix_oneWidth_minor_pos_iff_bandFeasible
    (show 0 < p + 1 by omega) (allRows (p + 2)) fullCols).2 hband
  simpa [widthOneCoreMatrix, window, fullCols, orderedMinor_submatrix] using hpos

theorem widthOneCoreMatrix_fullRowRank
    {p N start : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2) :
    HasFullRowRank (widthOneCoreMatrix p N start hstart) := by
  let cols : Fin (p + 2) ↪o Fin (N + (p + 1)) :=
    Fin.castLEOrderEmb (by omega)
  exact ⟨cols, (widthOneCoreMatrix_maximalMinor_pos hN hstart cols).ne'⟩

/-- The `d=1` case in the final realization paragraph of Theorem 6.2. -/
theorem exists_uniformLoopPavingCoreRealization_widthOne
    {p N start : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2) :
    Nonempty (UniformLoopPavingCoreRealization p N) := by
  let full := quantumBandMatrix (p + 1) 1
  let window := widthOneWindowColumns p N start hstart
  let A : Matrix (Fin (p + 2)) (Fin (N + (p + 1))) ℝ :=
    widthOneCoreMatrix p N start hstart
  have hTN : TotallyNonnegative A := widthOneCoreMatrix_totallyNonnegative hstart
  have hJupper : ∀ {q : ℕ} (J : Fin q ↪o Fin (N + (p + 1)))
      (t : Fin q), (J t).val ≤ t.val + (N + (p + 1) - q) := by
    intro q J t
    have hrev := orderEmbedding_fin_val_lower_bound
      (reverseOrderEmbedding J) (Fin.rev t)
    simp only [reverseOrderEmbedding_apply, Fin.rev_rev, Fin.val_rev] at hrev
    have ht := t.isLt
    have hJt := (J t).isLt
    have htRev : (Fin.rev t).val + t.val + 1 = q := by
      simp only [Fin.val_rev]
      omega
    have hJRev : (Fin.rev (J t)).val + (J t).val + 1 = N + (p + 1) := by
      simp only [Fin.val_rev]
      omega
    omega
  have hmaxPos : ∀ cols : Fin (p + 2) ↪o Fin (N + (p + 1)),
      0 < orderedMinor A (allRows (p + 2)) cols := by
    intro cols
    let fullCols := cols.trans window
    have hband : BandFeasible (allRows (p + 2)) fullCols := by
      intro t
      have hlower := orderEmbedding_fin_val_lower_bound cols t
      have hupper := hJupper cols t
      change t.val ≤ start + (cols t).val ∧
        start + (cols t).val ≤ t.val + 1
      constructor
      · omega
      · have hsize : N + (p + 1) - (p + 2) = N - 1 := by omega
        rw [hsize] at hupper
        omega
    have hpos := (quantumBandMatrix_oneWidth_minor_pos_iff_bandFeasible
      (show 0 < p + 1 by omega) (allRows (p + 2)) fullCols).2 hband
    change 0 < orderedMinor full (allRows (p + 2)) fullCols at hpos
    simpa [A, full, fullCols, orderedMinor_submatrix] using hpos
  have hfull : HasFullRowRank A := by
    let cols : Fin (p + 2) ↪o Fin (N + (p + 1)) :=
      Fin.castLEOrderEmb (by omega)
    exact ⟨cols, (hmaxPos cols).ne'⟩
  have hind : ∀ q, q ≤ p + 1 →
      ∀ cols : Fin q ↪o Fin (N + (p + 1)),
        LinearIndependent ℝ (fun j : Fin q => A.col (cols j)) := by
    intro q hq cols
    let fullCols := cols.trans window
    let rows := quantumFeasibleRows hq fullCols
    have hminor : orderedMinor full rows fullCols ≠ 0 :=
      ((quantumBandMatrix_oneWidth_minor_pos_iff_bandFeasible
        (show 0 < p + 1 by omega) rows fullCols).2
        (quantumFeasibleRows_bandFeasible hq fullCols)).ne'
    have hLI := linearIndependent_columns_of_nonzero_selectedMinor
      (q := q) (R := p + 2) (C := 1 + (p + 1) + 1)
      full rows fullCols hminor
    simpa [A, full, fullCols, Matrix.submatrix_apply] using hLI
  exact ⟨{
    matrix := A
    totallyNonnegative := hTN
    fullRowRank := hfull
    columns_independent := hind
    maximalMinor_pos := hmaxPos }⟩

/-- The `d=0` case is the square identity Toeplitz matrix (`N=1`). -/
theorem exists_uniformLoopPavingCoreRealization_widthZero (p : ℕ) :
    Nonempty (UniformLoopPavingCoreRealization p 1) :=
  exists_uniformLoopPavingCoreRealization_widthOne (p := p)
    (N := 1) (start := 0) (by omega) (by omega)

/-! ## Inserting loop prefixes and suffixes -/

/-- Add zero columns on both sides of a matrix. -/
def zeroExtendColumns {m s : ℕ} (L R : ℕ)
    (B : Matrix (Fin m) (Fin s) ℝ) :
    Matrix (Fin m) (Fin (L + s + R)) ℝ := fun i j =>
  if h : L ≤ j.val ∧ j.val < L + s then
    B i ⟨j.val - L, by omega⟩
  else 0

/-- The embedded central column window. -/
def zeroExtendWindow (L R s : ℕ) : Fin s ↪o Fin (L + s + R) :=
  OrderEmbedding.ofStrictMono
    (fun j => ⟨L + j.val, by have hj := j.isLt; omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) L)

@[simp] theorem zeroExtendColumns_window
    {m s : ℕ} (L R : ℕ) (B : Matrix (Fin m) (Fin s) ℝ) :
    (zeroExtendColumns L R B).submatrix (allRows m)
      (zeroExtendWindow L R s) = B := by
  ext i j
  simp [zeroExtendColumns, zeroExtendWindow, allRows]

theorem zeroExtendColumns_totallyNonnegative
    {m s : ℕ} (L R : ℕ) {B : Matrix (Fin m) (Fin s) ℝ}
    (hB : TotallyNonnegative B) :
    TotallyNonnegative (zeroExtendColumns L R B) := by
  intro q rows cols
  by_cases hall : ∀ t, L ≤ (cols t).val ∧ (cols t).val < L + s
  · let coreCols : Fin q ↪o Fin s :=
      OrderEmbedding.ofStrictMono
        (fun t => ⟨(cols t).val - L, by have ht := hall t; omega⟩)
        (by
          intro i j hij
          apply Fin.mk_lt_mk.mpr
          have hcols := Fin.mk_lt_mk.mp (cols.strictMono hij)
          have hi := hall i
          have hj := hall j
          exact Nat.sub_lt_sub_right hi.1 hcols)
    have heq : orderedMinor (zeroExtendColumns L R B) rows cols =
        orderedMinor B rows coreCols := by
      unfold orderedMinor
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, zeroExtendColumns]
      rw [dif_pos (hall j)]
      rfl
    rw [heq]
    exact hB q rows coreCols
  · push Not at hall
    obtain ⟨t, ht⟩ := hall
    rw [orderedMinor]
    have hdet : ((zeroExtendColumns L R B).submatrix rows cols).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero t
      intro i
      simp only [Matrix.submatrix_apply, zeroExtendColumns]
      have ht' : ¬(L ≤ (cols t).val ∧ (cols t).val < L + s) := by
        intro h
        exact (not_lt_of_ge (ht h.1)) h.2
      rw [dif_neg ht']
    rw [hdet]

theorem zeroExtendColumns_isLoop_left
    {m s L R : ℕ} (B : Matrix (Fin m) (Fin s) ℝ)
    (j : Fin (L + s + R)) (hj : j.val < L) :
    IsLoop (zeroExtendColumns L R B) j := by
  rw [isLoop_iff_entry_eq_zero]
  intro i
  unfold zeroExtendColumns
  rw [dif_neg]
  omega

theorem zeroExtendColumns_isLoop_right
    {m s L R : ℕ} (B : Matrix (Fin m) (Fin s) ℝ)
    (j : Fin (L + s + R)) (hj : L + s ≤ j.val) :
    IsLoop (zeroExtendColumns L R B) j := by
  rw [isLoop_iff_entry_eq_zero]
  intro i
  unfold zeroExtendColumns
  rw [dif_neg]
  omega

/-- Translated width-one coefficient function. -/
def shiftedWidthOneCoefficient (p start L : ℕ) (z : ℤ) : ℝ :=
  quantumBandCoefficient (p + 1) 1 (z + (start : ℤ) - (L : ℤ))

def shiftedWidthOneMatrix (p N start L R : ℕ) :
    Matrix (Fin (p + 2)) (Fin (L + (N + (p + 1)) + R)) ℝ :=
  toeplitzMatrix (p + 2) (L + (N + (p + 1)) + R)
    (shiftedWidthOneCoefficient p start L)

theorem shiftedWidthOneMatrix_eq_zeroExtend
    {p N start L R : ℕ} (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2) :
    shiftedWidthOneMatrix p N start L R =
      zeroExtendColumns L R (widthOneCoreMatrix p N start hstart) := by
  ext i j
  unfold shiftedWidthOneMatrix toeplitzMatrix shiftedWidthOneCoefficient
  simp only [zeroExtendColumns]
  by_cases hcentral : L ≤ j.val ∧ j.val < L + (N + (p + 1))
  · rw [dif_pos hcentral]
    unfold widthOneCoreMatrix
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
      quantumBandMatrix_apply, widthOneWindowColumns]
    apply congrArg (quantumBandCoefficient (p + 1) 1)
    change (j.val : ℤ) - (i.val : ℤ) + start - L =
      ((start + (j.val - L) : ℕ) : ℤ) - i.val
    push_cast
    rw [Nat.cast_sub hcentral.1]
    ring
  · rw [dif_neg hcentral]
    unfold quantumBandCoefficient
    rw [dif_neg]
    by_cases hjL : j.val < L
    · intro hz
      rcases hleft with rfl | hstartZero
      · omega
      · omega
    · intro hz
      have hjRight : L + (N + (p + 1)) ≤ j.val := by omega
      rcases hright with rfl | hrightEq
      · have hjBound := j.isLt
        omega
      · have hi := i.isLt
        omega

theorem shiftedWidthOneMatrix_totallyNonnegative
    {p N start L R : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2) :
    TotallyNonnegative (shiftedWidthOneMatrix p N start L R) := by
  rw [shiftedWidthOneMatrix_eq_zeroExtend hstart hleft hright]
  exact zeroExtendColumns_totallyNonnegative L R
    (widthOneCoreMatrix_totallyNonnegative hstart)

theorem shiftedWidthOneMatrix_loops_exact
    {p N start L R : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2)
    (j : Fin (L + (N + (p + 1)) + R)) :
    IsLoop (shiftedWidthOneMatrix p N start L R) j ↔
      j.val < L ∨ L + (N + (p + 1)) ≤ j.val := by
  rw [shiftedWidthOneMatrix_eq_zeroExtend hstart hleft hright]
  constructor
  · intro hloop
    by_contra hnot
    push Not at hnot
    let u : Fin (N + (p + 1)) := ⟨j.val - L, by omega⟩
    have hLI := widthOneCoreMatrix_columns_independent hstart
      (by omega : 1 ≤ p + 1) (singletonOrderEmbedding u)
    have hne : (widthOneCoreMatrix p N start hstart).col u ≠ 0 := by
      simpa [singletonOrderEmbedding] using linearIndependent_unique_iff.mp hLI
    apply hne
    funext i
    have hz := isLoop_iff_entry_eq_zero.mp hloop i
    unfold zeroExtendColumns at hz
    rw [dif_pos hnot] at hz
    change (widthOneCoreMatrix p N start hstart).col u i = 0
    exact hz
  · rintro (hj | hj)
    · exact zeroExtendColumns_isLoop_left _ j hj
    · exact zeroExtendColumns_isLoop_right _ j hj

theorem shiftedWidthOneMatrix_nonloopRestriction
    {p N start L R : ℕ} (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2) :
    (shiftedWidthOneMatrix p N start L R).submatrix (allRows (p + 2))
      (zeroExtendWindow L R (N + (p + 1))) =
        widthOneCoreMatrix p N start hstart := by
  rw [shiftedWidthOneMatrix_eq_zeroExtend hstart hleft hright]
  exact zeroExtendColumns_window L R _

theorem shiftedWidthOneMatrix_fullRowRank
    {p N start L R : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2) :
    HasFullRowRank (shiftedWidthOneMatrix p N start L R) := by
  obtain ⟨cols, hcols⟩ := widthOneCoreMatrix_fullRowRank hN hstart
  let extCols : Fin (p + 2) ↪o Fin (L + (N + (p + 1)) + R) :=
    cols.trans (zeroExtendWindow L R (N + (p + 1)))
  refine ⟨extCols, ?_⟩
  rw [orderedMinor]
  have hsub := shiftedWidthOneMatrix_nonloopRestriction
    (p := p) (N := N) (start := start) (L := L) (R := R)
    hstart hleft hright
  change ((shiftedWidthOneMatrix p N start L R).submatrix
    (allRows (p + 2)) extCols).det ≠ 0
  have heq : (shiftedWidthOneMatrix p N start L R).submatrix
      (allRows (p + 2)) extCols =
    (widthOneCoreMatrix p N start hstart).submatrix
      (allRows (p + 2)) cols := by
    rw [← hsub]
    ext i j
    rfl
  rw [heq]
  exact hcols

structure UniformLoopPavingFullRealization (p N L R : ℕ) where
  matrix : Matrix (Fin (p + 2)) (Fin (L + (N + (p + 1)) + R)) ℝ
  totallyNonnegative : TotallyNonnegative matrix
  fullRowRank : HasFullRowRank matrix
  loops_exact : ∀ j, IsLoop matrix j ↔
    j.val < L ∨ L + (N + (p + 1)) ≤ j.val
  nonloopMatrix : Matrix (Fin (p + 2)) (Fin (N + (p + 1))) ℝ
  nonloopRestriction : matrix.submatrix (allRows (p + 2))
    (zeroExtendWindow L R (N + (p + 1))) = nonloopMatrix
  maximalMinor_pos : ∀ cols : Fin (p + 2) ↪o Fin (N + (p + 1)),
    0 < orderedMinor nonloopMatrix (allRows (p + 2)) cols

/-- Complete low-bandwidth (`d=1`, hence `Z=∅`) displayed realization. -/
theorem exists_uniformLoopPavingFullRealization_widthOne
    {p N start L R : ℕ} (hN : 0 < N) (hstart : start + N ≤ 2)
    (hleft : L = 0 ∨ start = 0)
    (hright : R = 0 ∨ start + N = 2) :
    Nonempty (UniformLoopPavingFullRealization p N L R) := by
  refine ⟨{
    matrix := shiftedWidthOneMatrix p N start L R
    totallyNonnegative := shiftedWidthOneMatrix_totallyNonnegative
      hN hstart hleft hright
    fullRowRank := shiftedWidthOneMatrix_fullRowRank hN hstart hleft hright
    loops_exact := shiftedWidthOneMatrix_loops_exact hN hstart hleft hright
    nonloopMatrix := widthOneCoreMatrix p N start hstart
    nonloopRestriction := shiftedWidthOneMatrix_nonloopRestriction
      hstart hleft hright
    maximalMinor_pos := widthOneCoreMatrix_maximalMinor_pos hN hstart }⟩

/-! ### The coincident-endpoint `d=0` case -/

def shiftedIdentityCoefficient (L : ℕ) (z : ℤ) : ℝ :=
  zeroExtendedNaturalSequence (betaNaturalCoefficient 0) (z - L)

def shiftedIdentityMatrix (p L R : ℕ) :
    Matrix (Fin (p + 2)) (Fin (L + (1 + (p + 1)) + R)) ℝ :=
  toeplitzMatrix (p + 2) (L + (1 + (p + 1)) + R)
    (shiftedIdentityCoefficient L)

def identityCoreMatrix (p : ℕ) :
    Matrix (Fin (p + 2)) (Fin (1 + (p + 1))) ℝ := fun i j =>
  if i.val = j.val then 1 else 0

theorem shiftedIdentityCoefficient_eq_one_iff (L : ℕ) (z : ℤ) :
    shiftedIdentityCoefficient L z = 1 ↔ z = L := by
  constructor
  · intro hone
    by_contra hne
    have hzero : shiftedIdentityCoefficient L z = 0 := by
      unfold shiftedIdentityCoefficient zeroExtendedNaturalSequence
        betaNaturalCoefficient
      by_cases hnonneg : 0 ≤ z - L
      · rw [if_pos hnonneg]
        have htoNat : (z - L).toNat ≠ 0 := by
          intro hz0
          apply hne
          omega
        rw [if_neg htoNat]
        split_ifs <;> rfl
      · rw [if_neg hnonneg]
    rw [hzero] at hone
    norm_num at hone
  · rintro rfl
    simp [shiftedIdentityCoefficient, zeroExtendedNaturalSequence,
      betaNaturalCoefficient]

theorem shiftedIdentityCoefficient_eq_zero_of_ne
    (L : ℕ) {z : ℤ} (hz : z ≠ L) :
    shiftedIdentityCoefficient L z = 0 := by
  unfold shiftedIdentityCoefficient zeroExtendedNaturalSequence
    betaNaturalCoefficient
  by_cases hnonneg : 0 ≤ z - L
  · rw [if_pos hnonneg]
    have htoNat : (z - L).toNat ≠ 0 := by
      intro hzero
      apply hz
      omega
    rw [if_neg htoNat]
    split_ifs <;> rfl
  · rw [if_neg hnonneg]

theorem shiftedIdentityMatrix_totallyNonnegative (p L R : ℕ) :
    TotallyNonnegative (shiftedIdentityMatrix p L R) := by
  let n := L + (1 + (p + 1)) + R
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
    zeroExtendedNaturalSequence (betaNaturalCoefficient 0)
      ((j : ℤ) - (i : ℤ))
  let rows : Fin (p + 2) ↪o Fin (n + 1) :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨L + i.val, by have hi := i.isLt; dsimp only [n]; omega⟩)
      (by
        intro i j hij
        apply Fin.mk_lt_mk.mpr
        exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) L)
  let cols : Fin n ↪o Fin (n + 1) := Fin.castLEOrderEmb (by omega)
  have hB : TotallyNonnegative B :=
    betaToeplitz_totallyNonnegative (b := 0) (by norm_num) n
  have heq : B.submatrix rows cols = shiftedIdentityMatrix p L R := by
    ext i j
    unfold B shiftedIdentityMatrix toeplitzMatrix shiftedIdentityCoefficient
    simp only [Matrix.submatrix_apply, cols]
    congr 1
    change (j.val : ℤ) - ((L + i.val : ℕ) : ℤ) =
      (j.val : ℤ) - (i.val : ℤ) - (L : ℤ)
    push_cast
    ring
  rw [← heq]
  exact hB.submatrix rows cols

theorem shiftedIdentityMatrix_coreRestriction (p L R : ℕ) :
    (shiftedIdentityMatrix p L R).submatrix (allRows (p + 2))
      (zeroExtendWindow L R (1 + (p + 1))) = identityCoreMatrix p := by
  ext i j
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    zeroExtendWindow, shiftedIdentityMatrix, toeplitzMatrix_apply,
    identityCoreMatrix]
  change shiftedIdentityCoefficient L
      (((L + j.val : ℕ) : ℤ) - (i.val : ℤ)) =
    if i.val = j.val then 1 else 0
  by_cases hij : i.val = j.val
  · rw [if_pos hij]
    apply (shiftedIdentityCoefficient_eq_one_iff L _).2
    push_cast
    rw [hij]
    ring
  · rw [if_neg hij]
    apply shiftedIdentityCoefficient_eq_zero_of_ne
    intro heq
    apply hij
    push_cast at heq
    omega

theorem shiftedIdentityMatrix_fullRowRank (p L R : ℕ) :
    HasFullRowRank (shiftedIdentityMatrix p L R) := by
  let cols : Fin (p + 2) ↪o Fin (L + (1 + (p + 1)) + R) :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨L + i.val, by have hi := i.isLt; omega⟩)
      (by
        intro i j hij
        apply Fin.mk_lt_mk.mpr
        exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) L)
  refine ⟨cols, ?_⟩
  rw [orderedMinor]
  have heq : (shiftedIdentityMatrix p L R).submatrix
      (allRows (p + 2)) cols = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
      shiftedIdentityMatrix, toeplitzMatrix_apply, cols]
    change shiftedIdentityCoefficient L
        (((L + j.val : ℕ) : ℤ) - (i.val : ℤ)) =
      if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      apply (shiftedIdentityCoefficient_eq_one_iff L _).2
      push_cast
      ring
    · rw [if_neg hij]
      apply shiftedIdentityCoefficient_eq_zero_of_ne
      intro hz
      apply hij
      apply Fin.ext
      push_cast at hz
      omega
  rw [heq]
  simp

theorem shiftedIdentityMatrix_loops_exact
    (p L R : ℕ) (j : Fin (L + (1 + (p + 1)) + R)) :
    IsLoop (shiftedIdentityMatrix p L R) j ↔
      j.val < L ∨ L + (1 + (p + 1)) ≤ j.val := by
  constructor
  · intro hloop
    by_contra hnot
    push Not at hnot
    let i : Fin (p + 2) := ⟨j.val - L, by omega⟩
    have hz := isLoop_iff_entry_eq_zero.mp hloop i
    change shiftedIdentityCoefficient L ((j : ℤ) - (i : ℤ)) = 0 at hz
    have hone : shiftedIdentityCoefficient L ((j : ℤ) - (i : ℤ)) = 1 := by
      apply (shiftedIdentityCoefficient_eq_one_iff L _).2
      dsimp only [i]
      rw [Nat.cast_sub hnot.1]
      push_cast
      ring
    rw [hone] at hz
    norm_num at hz
  · rintro (hj | hj)
    · rw [isLoop_iff_entry_eq_zero]
      intro i
      apply shiftedIdentityCoefficient_eq_zero_of_ne
      push_cast
      omega
    · rw [isLoop_iff_entry_eq_zero]
      intro i
      apply shiftedIdentityCoefficient_eq_zero_of_ne
      have hi := i.isLt
      push_cast
      omega

/-- Complete `d=0`, `N=1` displayed realization with arbitrary loop
prefix and suffix lengths. -/
theorem exists_uniformLoopPavingFullRealization_widthZero
    (p L R : ℕ) : Nonempty (UniformLoopPavingFullRealization p 1 L R) := by
  refine ⟨{
    matrix := shiftedIdentityMatrix p L R
    totallyNonnegative := shiftedIdentityMatrix_totallyNonnegative p L R
    fullRowRank := shiftedIdentityMatrix_fullRowRank p L R
    loops_exact := shiftedIdentityMatrix_loops_exact p L R
    nonloopMatrix := identityCoreMatrix p
    nonloopRestriction := shiftedIdentityMatrix_coreRestriction p L R
    maximalMinor_pos := ?_ }⟩
  intro cols
  let e : Fin (p + 2) ↪o Fin (1 + (p + 1)) :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨i.val, by have hi := i.isLt; omega⟩)
      (by intro i j hij; exact hij)
  have hcols : cols = e :=
    Finset.orderEmbOfFin_unique' (s := Finset.univ) (by simp; omega)
      (by simp) |>.trans
      (Finset.orderEmbOfFin_unique' (s := Finset.univ) (by simp; omega)
        (f := e) (by simp)).symm
  rw [hcols]
  unfold orderedMinor identityCoreMatrix
  have heq : (Matrix.submatrix
      (fun (i : Fin (p + 2)) (j : Fin (1 + (p + 1))) =>
        if i.val = j.val then (1 : ℝ) else 0)
      (allRows (p + 2)) e) = 1 := by
    ext i j
    change (if i.val = j.val then (1 : ℝ) else 0) =
      if i = j then 1 else 0
    simp [Fin.ext_iff]
  rw [heq]
  simp

/-- In the `d ≤ 1` arithmetic cases of (38), the endpoint protections force
the admissible target zero set to be empty. -/
theorem lowBandwidth_endpointConditions_force_empty
    {N d left right : ℕ} (hN : 0 < N)
    (hleftBit : left ≤ 1) (hrightBit : right ≤ 1)
    (hband : d + left + right = N + 1) (hd : d ≤ 1)
    (Z : Finset (Fin N))
    (hleft : left = 1 → (⟨0, hN⟩ : Fin N) ∉ Z)
    (hright : right = 1 → lastLoopIndex N hN ∉ Z) :
    Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hdCases : d = 0 ∨ d = 1 := by omega
  rcases hdCases with rfl | rfl
  · have hbits : left = 1 ∧ right = 1 ∧ N = 1 := by omega
    have hu0 : u = ⟨0, hN⟩ := by
      apply Fin.ext
      omega
    apply hleft hbits.1
    rwa [← hu0]
  · by_cases hL : left = 0
    · have hR : right = 1 := by omega
      have hN1 : N = 1 := by omega
      have huLast : u = lastLoopIndex N hN := by
        apply Fin.ext
        simp [lastLoopIndex]
        omega
      apply hright hR
      rwa [← huLast]
    · have hL1 : left = 1 := by omega
      by_cases hR : right = 0
      · have hN1 : N = 1 := by omega
        have hu0 : u = ⟨0, hN⟩ := by
          apply Fin.ext
          omega
        apply hleft hL1
        rwa [← hu0]
      · have hR1 : right = 1 := by omega
        have hN2 : N = 2 := by omega
        by_cases hu : u.val = 0
        · have hu0 : u = ⟨0, hN⟩ := Fin.ext hu
          apply hleft hL1
          rwa [← hu0]
        · have huLast : u = lastLoopIndex N hN := by
            apply Fin.ext
            simp [lastLoopIndex]
            omega
          apply hright hR1
          rwa [← huLast]

/-- All compatible `d ≤ 1` data are realized by the uniform constructions
above. -/
theorem exists_compatibleLowBandwidthFullRealization
    {N d left right p L R : ℕ} (hN : 0 < N)
    (hleftBit : left ≤ 1) (hrightBit : right ≤ 1)
    (hband : d + left + right = N + 1) (hd : d ≤ 1)
    (Z : Finset (Fin N))
    (hleftProtected : left = 1 → (⟨0, hN⟩ : Fin N) ∉ Z)
    (hrightProtected : right = 1 → lastLoopIndex N hN ∉ Z)
    (hleftLoops : L = 0 ∨ left = 1)
    (hrightLoops : R = 0 ∨ right = 1) :
    Z = ∅ ∧ Nonempty (UniformLoopPavingFullRealization p N L R) := by
  have hZ := lowBandwidth_endpointConditions_force_empty hN hleftBit
    hrightBit hband hd Z hleftProtected hrightProtected
  refine ⟨hZ, ?_⟩
  have hdCases : d = 0 ∨ d = 1 := by omega
  rcases hdCases with hd0 | hd1
  · have hN1 : N = 1 := by omega
    subst N
    exact exists_uniformLoopPavingFullRealization_widthZero p L R
  · subst d
    let start := 1 - left
    have hstart : start + N ≤ 2 := by
      dsimp only [start]
      omega
    have hL : L = 0 ∨ start = 0 := by
      rcases hleftLoops with hzero | hone
      · exact Or.inl hzero
      · right
        dsimp only [start]
        omega
    have hR : R = 0 ∨ start + N = 2 := by
      rcases hrightLoops with hzero | hone
      · exact Or.inl hzero
      · right
        dsimp only [start]
        omega
    exact exists_uniformLoopPavingFullRealization_widthOne hN hstart hL hR

/-- Translate the quantum coefficient support so that the nonloop window
starts after `L` displayed loop columns. -/
def shiftedLoopPavingCoefficient
    {N d : ℕ} (W : LoopBoundaryWindow N d) (L : ℕ)
    (x : Fin (d - 1) → ℝ) (z : ℤ) : ℝ :=
  quantumSliceCoefficient x (z + (W.start : ℤ) - (L : ℤ))

/-- The full Toeplitz section with prescribed displayed loop lengths. -/
def shiftedLoopPavingMatrix
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    (x : Fin (d - 1) → ℝ) :
    Matrix (Fin (p + 2)) (Fin (L + (N + (p + 1)) + R)) ℝ :=
  toeplitzMatrix (p + 2) (L + (N + (p + 1)) + R)
    (shiftedLoopPavingCoefficient W L x)

/-- The central physical window in the extended display. -/
def shiftedLoopPavingWindow (N p L R : ℕ) :
    Fin (N + (p + 1)) ↪o Fin (L + (N + (p + 1)) + R) :=
  zeroExtendWindow L R (N + (p + 1))

/-- The translated Toeplitz section is literally the core matrix with zero
columns inserted on both sides. -/
theorem shiftedLoopPavingMatrix_eq_zeroExtend
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    (x : Fin (d - 1) → ℝ)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1) :
    shiftedLoopPavingMatrix W p L R x =
      zeroExtendColumns L R (W.nonloopMatrix (p + 1) x) := by
  ext i j
  unfold shiftedLoopPavingMatrix toeplitzMatrix
  simp only [shiftedLoopPavingCoefficient, zeroExtendColumns]
  by_cases hcentral : L ≤ j.val ∧ j.val < L + (N + (p + 1))
  · rw [dif_pos hcentral]
    unfold LoopBoundaryWindow.nonloopMatrix quantumSliceMatrix toeplitzMatrix
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
      LoopBoundaryWindow.windowColumns]
    apply congrArg (quantumSliceCoefficient x)
    change (j.val : ℤ) - (i.val : ℤ) + (W.start : ℤ) - (L : ℤ) =
      ((W.start + (j.val - L) : ℕ) : ℤ) - (i.val : ℤ)
    push_cast
    rw [Nat.cast_sub hcentral.1]
    ring
  · rw [dif_neg hcentral]
    unfold quantumSliceCoefficient
    rw [dif_neg]
    by_cases hjL : j.val < L
    · intro hz
      rcases hleft with rfl | hleftOne
      · omega
      · have hs := W.start_add_left
        push_cast
        omega
    · intro hz
      have hjRight : L + (N + (p + 1)) ≤ j.val := by omega
      rcases hright with rfl | hrightOne
      · have hjBound := j.isLt
        omega
      · have hN : 0 < N := by
          have hd := W.bandwidth_eq
          have hb := W.bandwidth_ge_two
          omega
        have hlast := W.target_last hN
        have hi := i.isLt
        push_cast
        omega

theorem shiftedLoopPavingMatrix_totallyNonnegative
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    {delta : Fin (d - 1) → ℝ}
    (Q : QuantumTargetRealization (p + 1) d W.bandwidth_ge_two delta)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1) :
    TotallyNonnegative (shiftedLoopPavingMatrix W p L R Q.source) := by
  rw [shiftedLoopPavingMatrix_eq_zeroExtend W p L R Q.source hleft hright]
  exact zeroExtendColumns_totallyNonnegative L R
    (W.nonloopMatrix_totallyNonnegative Q)

theorem shiftedLoopPavingMatrix_nonloopRestriction
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    (x : Fin (d - 1) → ℝ)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1) :
    (shiftedLoopPavingMatrix W p L R x).submatrix (allRows (p + 2))
      (shiftedLoopPavingWindow N p L R) =
        W.nonloopMatrix (p + 1) x := by
  rw [shiftedLoopPavingMatrix_eq_zeroExtend W p L R x hleft hright]
  exact zeroExtendColumns_window L R _

theorem shiftedLoopPavingMatrix_fullRowRank
    {N d : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N)
    (p L R : ℕ) {Z : Finset (Fin N)}
    (C : LoopPavingCoreRealization W hN p Z)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1) :
    HasFullRowRank (shiftedLoopPavingMatrix W p L R C.quantum.source) := by
  obtain ⟨cols, hcols⟩ := C.fullRowRank
  let extCols := cols.trans (shiftedLoopPavingWindow N p L R)
  refine ⟨extCols, ?_⟩
  rw [orderedMinor]
  have hsub := shiftedLoopPavingMatrix_nonloopRestriction W p L R
    C.quantum.source hleft hright
  change ((shiftedLoopPavingMatrix W p L R C.quantum.source).submatrix
    (allRows (p + 2)) extCols).det ≠ 0
  have heq : (shiftedLoopPavingMatrix W p L R C.quantum.source).submatrix
      (allRows (p + 2)) extCols =
    (W.nonloopMatrix (p + 1) C.quantum.source).submatrix
      (allRows (p + 2)) cols := by
    rw [← hsub]
    ext i j
    rfl
  rw [heq]
  exact hcols

theorem shiftedLoopPavingMatrix_prefixLoop
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    (x : Fin (d - 1) → ℝ)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1)
    (j : Fin (L + (N + (p + 1)) + R)) (hj : j.val < L) :
    IsLoop (shiftedLoopPavingMatrix W p L R x) j := by
  rw [shiftedLoopPavingMatrix_eq_zeroExtend W p L R x hleft hright]
  exact zeroExtendColumns_isLoop_left _ j hj

theorem shiftedLoopPavingMatrix_suffixLoop
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    (x : Fin (d - 1) → ℝ)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1)
    (j : Fin (L + (N + (p + 1)) + R))
    (hj : L + (N + (p + 1)) ≤ j.val) :
    IsLoop (shiftedLoopPavingMatrix W p L R x) j := by
  rw [shiftedLoopPavingMatrix_eq_zeroExtend W p L R x hleft hright]
  exact zeroExtendColumns_isLoop_right _ j hj

theorem shiftedLoopPavingMatrix_nonloop
    {N d : ℕ} (W : LoopBoundaryWindow N d) (p L R : ℕ)
    {delta : Fin (d - 1) → ℝ}
    (Q : QuantumTargetRealization (p + 1) d W.bandwidth_ge_two delta)
    (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1)
    (j : Fin (L + (N + (p + 1)) + R))
    (hj : L ≤ j.val ∧ j.val < L + (N + (p + 1))) :
    ¬IsLoop (shiftedLoopPavingMatrix W p L R Q.source) j := by
  let u : Fin (N + (p + 1)) := ⟨j.val - L, by omega⟩
  let sel : Fin 1 ↪o Fin (N + (p + 1)) := singletonOrderEmbedding u
  have hLI := W.nonloopMatrix_columns_independent Q (by omega : 1 ≤ p + 1) sel
  have hneFamily := linearIndependent_unique_iff.mp hLI
  have hne : (W.nonloopMatrix (p + 1) Q.source).col u ≠ 0 := by
    simpa [sel, singletonOrderEmbedding] using hneFamily
  intro hloop
  apply hne
  funext i
  have hz := isLoop_iff_entry_eq_zero.mp hloop i
  rw [shiftedLoopPavingMatrix_eq_zeroExtend W p L R Q.source
    hleft hright] at hz
  change zeroExtendColumns L R (W.nonloopMatrix (p + 1) Q.source) i j = 0 at hz
  unfold zeroExtendColumns at hz
  rw [dif_pos hj] at hz
  change (W.nonloopMatrix (p + 1) Q.source) i u = 0
  exact hz

/-- Full displayed realization, including the prescribed loop columns. -/
structure LoopPavingFullRealization
    {N d : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N)
    (p : ℕ) (Z : Finset (Fin N)) (L R : ℕ) where
  core : LoopPavingCoreRealization W hN p Z
  left_boundary : L = 0 ∨ W.left = 1
  right_boundary : R = 0 ∨ W.right = 1
  totallyNonnegative : TotallyNonnegative
    (shiftedLoopPavingMatrix W p L R core.quantum.source)
  fullRowRank : HasFullRowRank
    (shiftedLoopPavingMatrix W p L R core.quantum.source)
  loops_exact : ∀ j : Fin (L + (N + (p + 1)) + R),
    IsLoop (shiftedLoopPavingMatrix W p L R core.quantum.source) j ↔
      j.val < L ∨ L + (N + (p + 1)) ≤ j.val
  nonloopRestriction :
    (shiftedLoopPavingMatrix W p L R core.quantum.source).submatrix
      (allRows (p + 2)) (shiftedLoopPavingWindow N p L R) =
        W.nonloopMatrix (p + 1) core.quantum.source
  maximalSupport : ∀ J : Fin (p + 2) ↪o Fin (N + (p + 1)),
    matrixMaximalMinor
        ((shiftedLoopPavingMatrix W p L R core.quantum.source).submatrix
          (allRows (p + 2)) (shiftedLoopPavingWindow N p L R)) J ≠ 0 ↔
      LoopPavingBasisPredicate (targetZeroSetInWindow (p + 1) Z) J

/-- Complete `d ≥ 2` realization direction of Theorem 6.2, including
arbitrary positive lengths of the compatible loop prefix and suffix. -/
theorem exists_loopPavingFullRealization
    {N d p : ℕ} (W : LoopBoundaryWindow N d) (hN : 0 < N)
    (Z : Finset (Fin N)) (hZ : Z ≠ Finset.univ)
    (hleftProtected : W.left = 1 → (⟨0, hN⟩ : Fin N) ∉ Z)
    (hrightProtected : W.right = 1 → lastLoopIndex N hN ∉ Z)
    (L R : ℕ) (hleft : L = 0 ∨ W.left = 1)
    (hright : R = 0 ∨ W.right = 1) :
    Nonempty (LoopPavingFullRealization W hN p Z L R) := by
  obtain ⟨C⟩ := exists_loopPavingCoreRealization
    (p := p) W hN Z hZ hleftProtected hrightProtected
  refine ⟨{
    core := C
    left_boundary := hleft
    right_boundary := hright
    totallyNonnegative := shiftedLoopPavingMatrix_totallyNonnegative
      W p L R C.quantum hleft hright
    fullRowRank := shiftedLoopPavingMatrix_fullRowRank
      W hN p L R C hleft hright
    loops_exact := ?_
    nonloopRestriction := shiftedLoopPavingMatrix_nonloopRestriction
      W p L R C.quantum.source hleft hright
    maximalSupport := ?_ }⟩
  · intro j
    constructor
    · intro hloop
      by_contra hnot
      push Not at hnot
      exact shiftedLoopPavingMatrix_nonloop W p L R C.quantum
        hleft hright j hnot hloop
    · rintro (hj | hj)
      · exact shiftedLoopPavingMatrix_prefixLoop W p L R
          C.quantum.source hleft hright j hj
      · exact shiftedLoopPavingMatrix_suffixLoop W p L R
          C.quantum.source hleft hright j hj
  · intro J
    rw [shiftedLoopPavingMatrix_nonloopRestriction W p L R
      C.quantum.source hleft hright]
    exact C.maximalSupport J

end

end FurtherToeplitzPositroids
