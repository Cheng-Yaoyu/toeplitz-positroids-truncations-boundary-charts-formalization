import FurtherToeplitzPositroids.QuantumLocalRealization
import ToeplitzPositroids.RankThree.OrderTwo
import Mathlib.Data.Int.Interval

/-!
# A rectangular Toeplitz TN2 criterion

This module formalizes Proposition 4.1 for arbitrary finite rectangular
Toeplitz matrices.
-/

namespace FurtherToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- The smallest coefficient offset displayed by an `m`-row Toeplitz
matrix. -/
def displayedLower (m : ℕ) : ℤ :=
  1 - (m : ℤ)

/-- The largest coefficient offset displayed by an `n`-column Toeplitz
matrix. -/
def displayedUpper (n : ℕ) : ℤ :=
  (n : ℤ) - 1

/-- Coefficientwise nonnegativity on the displayed offset interval. -/
def DisplayedNonnegative (m n : ℕ) (a : ℤ → ℝ) : Prop :=
  ∀ z : ℤ, displayedLower m ≤ z → z ≤ displayedUpper n → 0 ≤ a z

/-- The positive displayed coefficients form an ordinary integer interval. -/
def DisplayedIntervalPositiveSupport (m n : ℕ) (a : ℤ → ℝ) : Prop :=
  ∀ p q z : ℤ,
    displayedLower m ≤ p → q ≤ displayedUpper n →
    0 < a p → 0 < a q → p ≤ z → z ≤ q → 0 < a z

/-- Adjacent log-concavity at every interior displayed offset. -/
def DisplayedLogConcave (m n : ℕ) (a : ℤ → ℝ) : Prop :=
  ∀ z : ℤ, displayedLower m < z → z < displayedUpper n →
    a z * a z ≥ a (z - 1) * a (z + 1)

/-- The determinant of an arbitrary rectangular two-row, two-column
Toeplitz submatrix. -/
theorem toeplitzMatrix_orderedMinor_two_rectangular
    {m n : ℕ} (a : ℤ → ℝ)
    (i₀ i₁ : Fin m) (hi : i₀ < i₁)
    (j₀ j₁ : Fin n) (hj : j₀ < j₁) :
    orderedMinor (toeplitzMatrix m n a)
        (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) =
      a ((j₀ : ℤ) - (i₀ : ℤ)) * a ((j₁ : ℤ) - (i₁ : ℤ)) -
        a ((j₁ : ℤ) - (i₀ : ℤ)) * a ((j₀ : ℤ) - (i₁ : ℤ)) := by
  rw [orderedMinor_two]
  simp

/-- Every displayed coefficient is a matrix entry. -/
theorem toeplitzMatrix_coefficient_nonneg
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a : ℤ → ℝ} (hA : TNUpTo (toeplitzMatrix m n a) 2) :
    DisplayedNonnegative m n a := by
  intro z hzLower hzUpper
  by_cases hz : 0 ≤ z
  · have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    let j : Fin n := ⟨z.toNat, by
      have hzUpper' : z < n := by
        dsimp only [displayedUpper] at hzUpper
        omega
      omega⟩
    let i0 : Fin m := ⟨0, hm⟩
    have hentry := hA.entry_nonneg (by omega) i0 j
    rw [toeplitzMatrix_apply] at hentry
    convert hentry using 1
    congr 1
    dsimp only [i0, j]
    omega
  · have hzneg : z < 0 := lt_of_not_ge hz
    have hnegNonneg : 0 ≤ -z := by omega
    have hnegNat : (((-z).toNat : ℕ) : ℤ) = -z :=
      Int.toNat_of_nonneg hnegNonneg
    let i : Fin m := ⟨(-z).toNat, by
      dsimp only [displayedLower] at hzLower
      omega⟩
    let j0 : Fin n := ⟨0, hn⟩
    have hentry := hA.entry_nonneg (by omega) i j0
    rw [toeplitzMatrix_apply] at hentry
    convert hentry using 1
    congr 1
    dsimp only [i, j0]
    omega

/-- Adjacent two-by-two minors force displayed log-concavity. -/
theorem toeplitzMatrix_displayedLogConcave
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℤ → ℝ} (hA : TNUpTo (toeplitzMatrix m n a) 2) :
    DisplayedLogConcave m n a := by
  intro z hzLower hzUpper
  by_cases hz : 0 ≤ z
  · have hzNat : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    let j₀ : Fin n := ⟨z.toNat, by
      dsimp only [displayedUpper] at hzUpper
      omega⟩
    let j₁ : Fin n := ⟨z.toNat + 1, by
      dsimp only [displayedUpper] at hzUpper
      omega⟩
    have hj : j₀ < j₁ := by simp [j₀, j₁]
    let i₀ : Fin m := ⟨0, by omega⟩
    let i₁ : Fin m := ⟨1, by omega⟩
    have hi : i₀ < i₁ := by simp [i₀, i₁]
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj)
    rw [toeplitzMatrix_orderedMinor_two_rectangular] at hminor
    have h₀₀ : (j₀ : ℤ) - (i₀ : ℤ) = z := by
      dsimp only [j₀, i₀]
      omega
    have h₁₁ : (j₁ : ℤ) - (i₁ : ℤ) = z := by
      dsimp only [j₁, i₁]
      omega
    have h₀₁ : (j₁ : ℤ) - (i₀ : ℤ) = z + 1 := by
      dsimp only [j₁, i₀]
      omega
    have h₁₀ : (j₀ : ℤ) - (i₁ : ℤ) = z - 1 := by
      dsimp only [j₀, i₁]
      omega
    rw [h₀₀, h₁₁, h₀₁, h₁₀] at hminor
    linarith
  · have hzneg : z < 0 := lt_of_not_ge hz
    have hnegNonneg : 0 ≤ -z := by omega
    have hnegNat : (((-z).toNat : ℕ) : ℤ) = -z :=
      Int.toNat_of_nonneg hnegNonneg
    let i₀ : Fin m := ⟨(-z).toNat, by
      dsimp only [displayedLower] at hzLower
      omega⟩
    let i₁ : Fin m := ⟨(-z).toNat + 1, by
      dsimp only [displayedLower] at hzLower
      omega⟩
    have hi : i₀ < i₁ := by simp [i₀, i₁]
    let j₀ : Fin n := ⟨0, by omega⟩
    let j₁ : Fin n := ⟨1, by omega⟩
    have hj : j₀ < j₁ := by simp [j₀, j₁]
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj)
    rw [toeplitzMatrix_orderedMinor_two_rectangular] at hminor
    have h₀₀ : (j₀ : ℤ) - (i₀ : ℤ) = z := by
      dsimp only [j₀, i₀]
      omega
    have h₁₁ : (j₁ : ℤ) - (i₁ : ℤ) = z := by
      dsimp only [j₁, i₁]
      omega
    have h₀₁ : (j₁ : ℤ) - (i₀ : ℤ) = z + 1 := by
      dsimp only [j₁, i₀]
      omega
    have h₁₀ : (j₀ : ℤ) - (i₁ : ℤ) = z - 1 := by
      dsimp only [j₀, i₁]
      omega
    rw [h₀₀, h₁₁, h₀₁, h₁₀] at hminor
    linarith

/-- A positive gap with zero interior coefficients produces a negative
two-by-two minor. -/
theorem toeplitzMatrix_positive_gap_contradiction
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℤ → ℝ} (hA : TNUpTo (toeplitzMatrix m n a) 2)
    {p q : ℤ}
    (hpLower : displayedLower m ≤ p) (hqUpper : q ≤ displayedUpper n)
    (hp : 0 < a p) (hq : 0 < a q)
    (hzero : ∀ z : ℤ, p < z → z < q → a z = 0)
    (h ell : ℕ) (hhPos : 1 ≤ h) (hh : h ≤ m - 1)
    (hellPos : 1 ≤ ell) (hell : ell ≤ n - 1)
    (hsum : (h : ℤ) + ell = q - p) : False := by
  let x : ℤ := p + h
  have hpx : p < x := by dsimp only [x]; omega
  have hxq : x < q := by dsimp only [x]; omega
  have hpy : p < p + ell := by omega
  have hyq : p + ell < q := by omega
  have hxzero : a x = 0 := hzero x hpx hxq
  have hyzero : a (p + ell) = 0 := hzero (p + ell) hpy hyq
  by_cases hx : 0 ≤ x
  · have hxNat : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx
    have hqUpper' : q < n := by
      dsimp only [displayedUpper] at hqUpper
      omega
    let i₀ : Fin m := ⟨0, by omega⟩
    let i₁ : Fin m := ⟨h, by omega⟩
    let j₀ : Fin n := ⟨x.toNat, by omega⟩
    let j₁ : Fin n := ⟨x.toNat + ell, by omega⟩
    have hi : i₀ < i₁ := by simp [i₀, i₁]; omega
    have hj : j₀ < j₁ := by simp [j₀, j₁]; omega
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj)
    rw [toeplitzMatrix_orderedMinor_two_rectangular] at hminor
    have h₀₀ : (j₀ : ℤ) - (i₀ : ℤ) = x := by
      dsimp only [j₀, i₀]
      omega
    have h₁₁ : (j₁ : ℤ) - (i₁ : ℤ) = p + ell := by
      dsimp only [j₁, i₁, x]
      omega
    have h₀₁ : (j₁ : ℤ) - (i₀ : ℤ) = q := by
      dsimp only [j₁, i₀, x]
      omega
    have h₁₀ : (j₀ : ℤ) - (i₁ : ℤ) = p := by
      dsimp only [j₀, i₁, x]
      omega
    rw [h₀₀, h₁₁, h₀₁, h₁₀, hxzero, hyzero] at hminor
    nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnegNonneg : 0 ≤ -x := by omega
    have hnegNat : (((-x).toNat : ℕ) : ℤ) = -x :=
      Int.toNat_of_nonneg hnegNonneg
    have hpLower' : 1 - (m : ℤ) ≤ p := by
      simpa [displayedLower] using hpLower
    let i₀ : Fin m := ⟨(-x).toNat, by omega⟩
    let i₁ : Fin m := ⟨(-x).toNat + h, by omega⟩
    let j₀ : Fin n := ⟨0, by omega⟩
    let j₁ : Fin n := ⟨ell, by omega⟩
    have hi : i₀ < i₁ := by simp [i₀, i₁]; omega
    have hj : j₀ < j₁ := by simp [j₀, j₁]; omega
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj)
    rw [toeplitzMatrix_orderedMinor_two_rectangular] at hminor
    have h₀₀ : (j₀ : ℤ) - (i₀ : ℤ) = x := by
      dsimp only [j₀, i₀]
      omega
    have h₁₁ : (j₁ : ℤ) - (i₁ : ℤ) = p + ell := by
      dsimp only [j₁, i₁, x]
      omega
    have h₀₁ : (j₁ : ℤ) - (i₀ : ℤ) = q := by
      dsimp only [j₁, i₀, x]
      omega
    have h₁₀ : (j₀ : ℤ) - (i₁ : ℤ) = p := by
      dsimp only [j₀, i₁, x]
      omega
    rw [h₀₀, h₁₁, h₀₁, h₁₀, hxzero, hyzero] at hminor
    nlinarith

/-- No two positive displayed coefficients can have an all-zero gap between
them. -/
theorem toeplitzMatrix_no_positive_gap
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℤ → ℝ} (hA : TNUpTo (toeplitzMatrix m n a) 2)
    {p q : ℤ}
    (hpLower : displayedLower m ≤ p) (hqUpper : q ≤ displayedUpper n)
    (hpq : p + 1 < q) (hp : 0 < a p) (hq : 0 < a q)
    (hzero : ∀ z : ℤ, p < z → z < q → a z = 0) : False := by
  let gap : ℕ := (q - p).toNat
  have hgapNonneg : 0 ≤ q - p := by omega
  have hgapCast : ((gap : ℕ) : ℤ) = q - p := by
    exact Int.toNat_of_nonneg hgapNonneg
  have hgapTwo : 2 ≤ gap := by omega
  have hgapBound : gap ≤ (m - 1) + (n - 1) := by
    dsimp only [displayedLower] at hpLower
    dsimp only [displayedUpper] at hqUpper
    omega
  let h : ℕ := max 1 (gap - (n - 1))
  let ell : ℕ := gap - h
  have hhPos : 1 ≤ h := le_max_left _ _
  have hh : h ≤ m - 1 := by
    dsimp only [h]
    omega
  have hellPos : 1 ≤ ell := by
    dsimp only [ell, h]
    omega
  have hell : ell ≤ n - 1 := by
    dsimp only [ell, h]
    omega
  have hsumNat : h + ell = gap := by
    dsimp only [ell]
    omega
  have hsum : (h : ℤ) + ell = q - p := by
    rw [← hgapCast]
    exact_mod_cast hsumNat
  exact toeplitzMatrix_positive_gap_contradiction hm hn hA hpLower hqUpper
    hp hq hzero h ell hhPos hh hellPos hell hsum

/-- Total nonnegativity through order two forces interval positive support
on the displayed coefficient interval. -/
theorem toeplitzMatrix_displayedIntervalPositiveSupport
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℤ → ℝ} (hA : TNUpTo (toeplitzMatrix m n a) 2) :
    DisplayedIntervalPositiveSupport m n a := by
  intro p q z hpLower hqUpper hp hq hpz hzq
  have hnonneg := toeplitzMatrix_coefficient_nonneg (by omega) (by omega) hA
  have hzLower : displayedLower m ≤ z := hpLower.trans hpz
  have hzUpper : z ≤ displayedUpper n := hzq.trans hqUpper
  by_contra hzpos
  have hzzero : a z = 0 :=
    le_antisymm (le_of_not_gt hzpos) (hnonneg z hzLower hzUpper)
  rcases hpz.eq_or_lt with rfl | hpz
  · exact hp.ne' hzzero
  rcases hzq.eq_or_lt with rfl | hzq
  · exact hq.ne' hzzero
  let left : Finset ℤ := (Finset.Icc p z).filter fun t ↦ 0 < a t
  have hpLeft : p ∈ left := by
    simp [left, hp, hpz.le]
  have hleftNonempty : left.Nonempty := ⟨p, hpLeft⟩
  let p' : ℤ := left.max' hleftNonempty
  have hp'Left : p' ∈ left := left.max'_mem hleftNonempty
  have hp'Pos : 0 < a p' := (Finset.mem_filter.mp hp'Left).2
  have hp'p : p ≤ p' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp'Left).1).1
  have hp'z : p' ≤ z := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp'Left).1).2
  have hp'zlt : p' < z := lt_of_le_of_ne hp'z fun h ↦ by
    exact hzpos (h ▸ hp'Pos)
  let right : Finset ℤ := (Finset.Icc z q).filter fun t ↦ 0 < a t
  have hqRight : q ∈ right := by
    simp [right, hq, hzq.le]
  have hrightNonempty : right.Nonempty := ⟨q, hqRight⟩
  let q' : ℤ := right.min' hrightNonempty
  have hq'Right : q' ∈ right := right.min'_mem hrightNonempty
  have hq'Pos : 0 < a q' := (Finset.mem_filter.mp hq'Right).2
  have hzq' : z ≤ q' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq'Right).1).1
  have hq'q : q' ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq'Right).1).2
  have hzq'lt : z < q' := lt_of_le_of_ne hzq' fun h ↦ by
    exact hzpos (h.symm ▸ hq'Pos)
  have hgap : p' + 1 < q' := by omega
  have hzero : ∀ t : ℤ, p' < t → t < q' → a t = 0 := by
    intro t hp't htq'
    have htNonpos : ¬0 < a t := by
      intro htpos
      rcases le_total t z with htz | hzt
      · have htLeft : t ∈ left := by
          simp only [left, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hp'p.trans hp't.le, htz⟩, htpos⟩
        have htle : t ≤ p' := left.le_max' t htLeft
        exact (not_le_of_gt hp't) htle
      · have htRight : t ∈ right := by
          simp only [right, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hzt, htq'.le.trans hq'q⟩, htpos⟩
        have hq'le : q' ≤ t := right.min'_le t htRight
        exact (not_le_of_gt htq') hq'le
    have htLower : displayedLower m ≤ t := hpLower.trans (hp'p.trans hp't.le)
    have htUpper : t ≤ displayedUpper n := htq'.le.trans (hq'q.trans hqUpper)
    exact le_antisymm (le_of_not_gt htNonpos) (hnonneg t htLower htUpper)
  exact toeplitzMatrix_no_positive_gap hm hn hA
    (hpLower.trans hp'p) (hq'q.trans hqUpper) hgap hp'Pos hq'Pos hzero

/-! ## Sufficiency via decreasing coefficient ratios -/

/-- The adjacent displayed coefficient ratio. -/
def displayedRatio (a : ℤ → ℝ) (z : ℤ) : ℝ :=
  a (z + 1) / a z

/-- Adjacent log-concavity makes the ratio sequence weakly decreasing. -/
theorem displayedRatio_succ_le
    {m n : ℕ} {a : ℤ → ℝ} (hlog : DisplayedLogConcave m n a)
    {z : ℤ} (hzLower : displayedLower m ≤ z)
    (hzUpper : z + 2 ≤ displayedUpper n)
    (hz : 0 < a z) (hz1 : 0 < a (z + 1)) :
    displayedRatio a (z + 1) ≤ displayedRatio a z := by
  unfold displayedRatio
  have hidx : z + 1 + 1 = z + 2 := by omega
  rw [hidx]
  rw [div_le_div_iff₀ hz1 hz]
  have h := hlog (z + 1) (by omega) (by omega)
  have hm : z + 1 - 1 = z := by omega
  have hp : z + 1 + 1 = z + 2 := by omega
  rw [hm, hp] at h
  nlinarith

/-- Ratios at later positions are no larger throughout a positive displayed
coefficient interval. -/
theorem displayedRatio_le_of_le
    {m n : ℕ} {a : ℤ → ℝ} (hlog : DisplayedLogConcave m n a)
    {p q : ℤ} (hpLower : displayedLower m ≤ p)
    (hqUpper : q + 1 ≤ displayedUpper n) (hpq : p ≤ q)
    (hpos : ∀ z : ℤ, p ≤ z → z ≤ q + 1 → 0 < a z) :
    displayedRatio a q ≤ displayedRatio a p := by
  let gap : ℕ := (q - p).toNat
  have hgapNonneg : 0 ≤ q - p := by omega
  have hgapCast : ((gap : ℕ) : ℤ) = q - p :=
    Int.toNat_of_nonneg hgapNonneg
  have hchain : ∀ k : ℕ, k ≤ gap →
      displayedRatio a (p + k) ≤ displayedRatio a p := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ gap := by omega
        have hstep : displayedRatio a (p + k + 1) ≤
            displayedRatio a (p + k) := by
          apply displayedRatio_succ_le hlog
          · omega
          · omega
          · apply hpos <;> omega
          · apply hpos <;> omega
        have hindex : p + ((k + 1 : ℕ) : ℤ) = p + (k : ℤ) + 1 := by
          push_cast
          ring
        rw [hindex]
        exact hstep.trans (ih hk')
  have hqeq : p + (gap : ℤ) = q := by omega
  simpa [hqeq] using hchain gap le_rfl

/-- A finite product of consecutive ratios telescopes. -/
theorem prod_displayedRatio_eq_div
    (a : ℤ → ℝ) (p : ℤ) (h : ℕ)
    (hpos : ∀ k : ℕ, k ≤ h → 0 < a (p + k)) :
    (∏ k ∈ Finset.range h, displayedRatio a (p + k)) =
      a (p + h) / a p := by
  induction h with
  | zero =>
      rw [Finset.prod_range_zero]
      simp only [Nat.cast_zero, add_zero]
      symm
      apply div_self
      simpa using (hpos 0 le_rfl).ne'
  | succ h ih =>
      rw [Finset.prod_range_succ, ih (fun k hk ↦ hpos k (by omega))]
      unfold displayedRatio
      have hh : a (p + h) ≠ 0 := (hpos h (by omega)).ne'
      have hp : a p ≠ 0 := by simpa using (hpos 0 (by omega)).ne'
      have hindex : p + (h : ℤ) + 1 = p + ((h + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hindex]
      field_simp

/-- Equality in a nonstructural rectangular Toeplitz two-by-two difference
is equivalent to constancy of every adjacent coefficient ratio between its
two extreme entries.  This is the equality assertion in Proposition 4.1. -/
theorem displayedToeplitzDifference_eq_zero_iff_ratio_const
    {m n : ℕ} {a : ℤ → ℝ}
    (hlog : DisplayedLogConcave m n a)
    {p : ℤ} {h ell : ℕ} (hh : 1 ≤ h) (hell : 1 ≤ ell)
    (hpLower : displayedLower m ≤ p)
    (hupper : p + ell + h ≤ displayedUpper n)
    (hpos : ∀ z : ℤ, p ≤ z → z ≤ p + ell + h → 0 < a z) :
    a (p + h) * a (p + ell) - a (p + h + ell) * a p = 0 ↔
      ∀ z : ℤ, p ≤ z → z ≤ p + ell + h - 1 →
        displayedRatio a z = displayedRatio a p := by
  let leftProduct : ℝ :=
    ∏ k ∈ Finset.range h, displayedRatio a (p + k)
  let rightProduct : ℝ :=
    ∏ k ∈ Finset.range h, displayedRatio a (p + ell + k)
  have hleftProduct : leftProduct = a (p + h) / a p := by
    dsimp only [leftProduct]
    exact prod_displayedRatio_eq_div a p h fun k hk ↦ hpos _ (by omega) (by omega)
  have hrightProduct : rightProduct = a (p + ell + h) / a (p + ell) := by
    dsimp only [rightProduct]
    exact prod_displayedRatio_eq_div a (p + ell) h fun k hk ↦
      hpos _ (by omega) (by omega)
  have hcomponentLe : ∀ k : ℕ, k < h →
      displayedRatio a (p + ell + k) ≤ displayedRatio a (p + k) := by
    intro k hk
    apply displayedRatio_le_of_le hlog
    · omega
    · omega
    · omega
    · intro z hzLower hzUpper
      apply hpos <;> omega
  constructor
  · intro hzero
    have hproducts : leftProduct = rightProduct := by
      rw [hleftProduct, hrightProduct]
      rw [div_eq_div_iff (hpos p (by omega) (by omega)).ne'
        (hpos (p + ell) (by omega) (by omega)).ne']
      have hindex : p + (h : ℤ) + ell = p + (ell : ℤ) + h := by ring
      rw [hindex] at hzero
      exact sub_eq_zero.mp hzero
    have hcomponentEq : ∀ k : ℕ, k < h →
        displayedRatio a (p + ell + k) = displayedRatio a (p + k) := by
      intro k hk
      have hle := hcomponentLe k hk
      apply le_antisymm hle
      by_contra hnot
      have hstrict : displayedRatio a (p + ell + k) <
          displayedRatio a (p + k) :=
        lt_of_le_of_ne hle fun heq ↦ hnot heq.symm.le
      have hprodStrict : rightProduct < leftProduct := by
        dsimp only [rightProduct, leftProduct]
        apply Finset.prod_lt_prod
        · intro j hj
          simp only [Finset.mem_range] at hj
          exact div_pos
            (hpos _ (by omega) (by omega))
            (hpos _ (by omega) (by omega))
        · intro j hj
          simp only [Finset.mem_range] at hj
          exact hcomponentLe j hj
        · exact ⟨k, Finset.mem_range.mpr hk, hstrict⟩
      exact (ne_of_lt hprodStrict) hproducts.symm
    have hconst : ∀ k : ℕ, k < h →
        ∀ z : ℤ, p ≤ z → z ≤ p + ell + k →
          displayedRatio a z = displayedRatio a p := by
      intro k hk
      induction k with
      | zero =>
          intro z hpz hzend
          have hlater : displayedRatio a (p + ell) ≤ displayedRatio a z := by
            apply displayedRatio_le_of_le hlog
            · omega
            · omega
            · omega
            · intro q hqLower hqUpper
              apply hpos <;> omega
          have heq₀ := hcomponentEq 0 hk
          have heqEnd : displayedRatio a (p + ell) = displayedRatio a p := by
            simpa using heq₀
          have hearlier : displayedRatio a z ≤ displayedRatio a p := by
            apply displayedRatio_le_of_le hlog
            · exact hpLower
            · omega
            · exact hpz
            · intro q hqLower hqUpper
              apply hpos <;> omega
          exact le_antisymm hearlier (by simpa [heqEnd] using hlater)
      | succ k ih =>
          intro z hpz hzend
          by_cases hz : z ≤ p + ell + k
          · exact ih (by omega) z hpz hz
          · have hzEq : z = p + ell + (k + 1) := by omega
            have hsuccIndex : p + (ell : ℤ) + ((k : ℤ) + 1) =
                p + (ell : ℤ) + ((k + 1 : ℕ) : ℤ) := by
              push_cast
              ring
            rw [hzEq, hsuccIndex, hcomponentEq (k + 1) (by omega)]
            exact ih (by omega) (p + (k + 1)) (by omega) (by omega)
    intro z hpz hzUpper
    have hhPred : h - 1 < h := by omega
    have := hconst (h - 1) hhPred z hpz (by omega)
    exact this
  · intro hconst
    have hproducts : leftProduct = rightProduct := by
      dsimp only [leftProduct, rightProduct]
      apply Finset.prod_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hconst (p + k) (by omega) (by omega),
        hconst (p + ell + k) (by omega) (by omega)]
    rw [hleftProduct, hrightProduct] at hproducts
    have hpne := (hpos p (by omega) (by omega)).ne'
    have hellne := (hpos (p + ell) (by omega) (by omega)).ne'
    rw [div_eq_div_iff hpne hellne] at hproducts
    have hindex : p + (h : ℤ) + ell = p + (ell : ℤ) + h := by ring
    rw [hindex]
    exact sub_eq_zero.mpr hproducts

/-- The general cross-product inequality implied by interval support and
adjacent log-concavity. -/
theorem displayedToeplitzDifference_nonneg
    {m n : ℕ} {a : ℤ → ℝ}
    (hnonneg : DisplayedNonnegative m n a)
    (hsupport : DisplayedIntervalPositiveSupport m n a)
    (hlog : DisplayedLogConcave m n a)
    {x : ℤ} {h ell : ℕ} (hh : 1 ≤ h) (hell : 1 ≤ ell)
    (hleft : displayedLower m ≤ x - h)
    (hright : x + ell ≤ displayedUpper n) :
    0 ≤ a x * a (x + ell - h) - a (x + ell) * a (x - h) := by
  have hxBounds : displayedLower m ≤ x ∧ x ≤ displayedUpper n := by omega
  have hmidBounds : displayedLower m ≤ x + ell - h ∧
      x + ell - h ≤ displayedUpper n := by omega
  have hfirst : 0 ≤ a x * a (x + ell - h) :=
    mul_nonneg (hnonneg x hxBounds.1 hxBounds.2)
      (hnonneg (x + ell - h) hmidBounds.1 hmidBounds.2)
  have hsecond : 0 ≤ a (x + ell) * a (x - h) :=
    mul_nonneg (hnonneg (x + ell) (by omega) hright)
      (hnonneg (x - h) hleft (by omega))
  by_cases hsecondPos : 0 < a (x + ell) * a (x - h)
  · rcases mul_pos_iff.mp hsecondPos with hboth | hboth
    · have hpos : ∀ z : ℤ, x - h ≤ z → z ≤ x + ell → 0 < a z := by
        intro z hzL hzR
        exact hsupport (x - h) (x + ell) z hleft hright
          hboth.2 hboth.1 hzL hzR
      have hprodLe :
          (∏ k ∈ Finset.range h,
              displayedRatio a (x + ell - h + k)) ≤
            ∏ k ∈ Finset.range h, displayedRatio a (x - h + k) := by
        apply Finset.prod_le_prod
        · intro k hk
          simp only [Finset.mem_range] at hk
          exact (div_pos
            (hpos _ (by omega) (by omega))
            (hpos _ (by omega) (by omega))).le
        · intro k hk
          simp only [Finset.mem_range] at hk
          apply displayedRatio_le_of_le hlog
          · omega
          · omega
          · omega
          · intro z hzL hzR
            apply hpos <;> omega
      rw [prod_displayedRatio_eq_div a (x + ell - h) h
          (fun k hk ↦ hpos _ (by omega) (by omega)),
        prod_displayedRatio_eq_div a (x - h) h
          (fun k hk ↦ hpos _ (by omega) (by omega))] at hprodLe
      have hdenRight : 0 < a (x + ell - h) := hpos _ (by omega) (by omega)
      have hdenLeft : 0 < a (x - h) := hboth.2
      rw [div_le_div_iff₀ hdenRight hdenLeft] at hprodLe
      exact sub_nonneg.mpr (by simpa [mul_comm] using hprodLe)
    · exact ((not_lt_of_ge (hnonneg _ (by omega) hright)) hboth.1).elim
  · have hsecondZero : a (x + ell) * a (x - h) = 0 :=
      le_antisymm (le_of_not_gt hsecondPos) hsecond
    simpa [hsecondZero] using hfirst

/-- The three displayed coefficient conditions imply every minor of order at
most two is nonnegative. -/
theorem toeplitzMatrix_tnUpTo_two_of_displayedConditions
    {m n : ℕ} {a : ℤ → ℝ}
    (hnonneg : DisplayedNonnegative m n a)
    (hsupport : DisplayedIntervalPositiveSupport m n a)
    (hlog : DisplayedLogConcave m n a) :
    TNUpTo (toeplitzMatrix m n a) 2 := by
  intro l hl rows cols
  interval_cases l
  · simp
  · rw [orderedMinor_one, toeplitzMatrix_apply]
    apply hnonneg
    · have hi := (rows 0).isLt
      have hj := (cols 0).isLt
      simp only [displayedLower]
      omega
    · have hi := (rows 0).isLt
      have hj := (cols 0).isLt
      simp only [displayedUpper]
      omega
  · have hri : rows 0 < rows 1 := rows.strictMono (by decide)
    have hcj : cols 0 < cols 1 := cols.strictMono (by decide)
    have hrows : rows = twoPointOrderEmbedding (rows 0) (rows 1) hri := by
      ext i
      fin_cases i <;> rfl
    have hcols : cols = twoPointOrderEmbedding (cols 0) (cols 1) hcj := by
      ext j
      fin_cases j <;> rfl
    rw [hrows, hcols, toeplitzMatrix_orderedMinor_two_rectangular]
    let x : ℤ := (cols 0 : ℤ) - (rows 0 : ℤ)
    let h : ℕ := (rows 1).val - (rows 0).val
    let ell : ℕ := (cols 1).val - (cols 0).val
    have hh : 1 ≤ h := by dsimp only [h]; omega
    have hell : 1 ≤ ell := by dsimp only [ell]; omega
    have hleft : displayedLower m ≤ x - h := by
      have hi := (rows 1).isLt
      simp only [displayedLower]
      dsimp only [x, h]
      omega
    have hright : x + ell ≤ displayedUpper n := by
      have hj := (cols 1).isLt
      simp only [displayedUpper]
      dsimp only [x, ell]
      omega
    have hdiff := displayedToeplitzDifference_nonneg hnonneg hsupport hlog
      hh hell hleft hright
    have h₀₀ : x = (cols 0 : ℤ) - (rows 0 : ℤ) := rfl
    have h₁₁ : x + ell - h = (cols 1 : ℤ) - (rows 1 : ℤ) := by
      dsimp only [x, h, ell]
      omega
    have h₀₁ : x + ell = (cols 1 : ℤ) - (rows 0 : ℤ) := by
      dsimp only [x, ell]
      omega
    have h₁₀ : x - h = (cols 0 : ℤ) - (rows 1 : ℤ) := by
      dsimp only [x, h]
      omega
    rwa [h₀₀, h₁₁, h₀₁, h₁₀] at hdiff

/-- Proposition 4.1, rectangular Toeplitz `TN₂` criterion. -/
theorem toeplitzMatrix_tnUpTo_two_iff
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (a : ℤ → ℝ) :
    TNUpTo (toeplitzMatrix m n a) 2 ↔
      DisplayedNonnegative m n a ∧
        DisplayedIntervalPositiveSupport m n a ∧
          DisplayedLogConcave m n a := by
  constructor
  · intro hA
    exact ⟨toeplitzMatrix_coefficient_nonneg (by omega) (by omega) hA,
      toeplitzMatrix_displayedIntervalPositiveSupport hm hn hA,
      toeplitzMatrix_displayedLogConcave hm hn hA⟩
  · rintro ⟨hnonneg, hsupport, hlog⟩
    exact toeplitzMatrix_tnUpTo_two_of_displayedConditions
      hnonneg hsupport hlog

/-- A nonloop column of a totally nonnegative matrix contains a positive
entry. -/
theorem exists_entry_pos_of_not_isLoop
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : TotallyNonnegative A) {j : Fin n} (hj : ¬IsLoop A j) :
    ∃ i, 0 < A i j := by
  by_contra hnone
  push Not at hnone
  apply hj
  rw [isLoop_iff_entry_eq_zero]
  intro i
  exact le_antisymm (hnone i) (hA.entry_nonneg i j)

/-- Corollary 4.2, pointwise form: every column between two nonloop columns
is a nonloop. -/
theorem toeplitzMatrix_nonloop_interval
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a : ℤ → ℝ} (hA : TotallyNonnegative (toeplitzMatrix m n a))
    {j₀ k j₁ : Fin n} (hj₀k : j₀ ≤ k) (hkj₁ : k ≤ j₁)
    (hj₀ : ¬IsLoop (toeplitzMatrix m n a) j₀)
    (hj₁ : ¬IsLoop (toeplitzMatrix m n a) j₁) :
    ¬IsLoop (toeplitzMatrix m n a) k := by
  obtain ⟨i₀, hi₀⟩ := exists_entry_pos_of_not_isLoop hA hj₀
  obtain ⟨i₁, hi₁⟩ := exists_entry_pos_of_not_isLoop hA hj₁
  rw [toeplitzMatrix_apply] at hi₀ hi₁
  let p : ℤ := (j₀ : ℤ) - (i₀ : ℤ)
  let q : ℤ := (j₁ : ℤ) - (i₁ : ℤ)
  have hp : 0 < a p := by simpa [p] using hi₀
  have hq : 0 < a q := by simpa [q] using hi₁
  have hpLower : displayedLower m ≤ p := by
    have hi := i₀.isLt
    simp only [displayedLower]
    dsimp only [p]
    omega
  have hqUpper : q ≤ displayedUpper n := by
    have hj := j₁.isLt
    simp only [displayedUpper]
    dsimp only [q]
    omega
  have hsupport := toeplitzMatrix_displayedIntervalPositiveSupport
    hm hn (hA.tnUpTo 2)
  by_cases hqk : q ≤ (k : ℤ)
  · have hdelta : j₁.val - k.val ≤ i₁.val := by
      dsimp only [q] at hqk
      omega
    let i : Fin m := ⟨i₁.val - (j₁.val - k.val), by
      have hi := i₁.isLt
      omega⟩
    have hoffset : (k : ℤ) - (i : ℤ) = q := by
      dsimp only [i, q]
      omega
    intro hkloop
    have hzero := isLoop_iff_entry_eq_zero.mp hkloop i
    rw [toeplitzMatrix_apply, hoffset] at hzero
    exact hq.ne' hzero
  · have hkq : (k : ℤ) < q := lt_of_not_ge hqk
    have hpk : p ≤ (k : ℤ) := by
      dsimp only [p]
      omega
    have hkPos : 0 < a (k : ℤ) :=
      hsupport p q (k : ℤ) hpLower hqUpper hp hq hpk hkq.le
    let i : Fin m := ⟨0, by omega⟩
    intro hkloop
    have hzero := isLoop_iff_entry_eq_zero.mp hkloop i
    rw [toeplitzMatrix_apply] at hzero
    have hoffset : (k : ℤ) - (i : ℤ) = (k : ℤ) := by simp [i]
    rw [hoffset] at hzero
    exact hkPos.ne' hzero

end

end FurtherToeplitzPositroids
