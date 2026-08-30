import FurtherToeplitzPositroids.QuantumMinorSchur
import FurtherToeplitzPositroids.QuantumJacobian
import AlgebraicCombinatorics.SymmetricFunctions.Definitions
import Mathlib.GroupTheory.Perm.Fin

/-!
# The quantum complete-homogeneous recurrence

This module formalizes equations (27), (28), and (32).  The normalized
recurrence vector is expressed through elementary symmetric functions of the
quantum alphabet `X`; Newton--Girard gives the recurrence for all indices
needed by the interior consecutive blocks.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Finset MvPolynomial Matrix
open AlgebraicCombinatorics SymmetricPolynomials
open ToeplitzPositroids PavingToeplitzPositroids

noncomputable section

/-- Complete homogeneous specialization extended by zero to negative
indices. -/
def completeHomogeneousSpecializationExt
    {N : ℕ} (x : Fin N → ℂ) (z : ℤ) : ℂ :=
  if 0 ≤ z then completeHomogeneousSpecialization x z.toNat else 0

/-- Newton--Girard after evaluating the variables in a complex alphabet. -/
theorem evaluated_newtonGirard_eh
    {N n : ℕ} (x : Fin N → ℂ) (hn : 0 < n) :
    ∑ j ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ j *
          elementarySymmetricSpecialization x j *
          completeHomogeneousSpecialization x (n - j) = 0 := by
  have hng := AlgebraicCombinatorics.SymmetricPolynomials.newtonGirard_eh
    (K := ℂ) (N := N) n hn
  have heval := congrArg (MvPolynomial.aeval x) hng
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at heval
  simpa [elementarySymmetricSpecialization_eq_aeval_esymm,
    completeHomogeneousSpecialization] using heval

/-- Extended Newton--Girard recurrence, with both the elementary and complete
families continued by structural zeros beyond their natural ranges. -/
theorem evaluated_newtonGirard_eh_extended
    {N : ℕ} (x : Fin N → ℂ) {z : ℤ} (hz : 0 < z) :
    ∑ j : Fin (N + 1),
        (-1 : ℂ) ^ j.val *
          elementarySymmetricSpecialization x j.val *
          completeHomogeneousSpecializationExt x (z - j.val) = 0 := by
  let n := z.toNat
  have hn : 0 < n := by omega
  have hzNat : (n : ℤ) = z := Int.toNat_of_nonneg hz.le
  have hbase := evaluated_newtonGirard_eh x hn
  let F : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
      completeHomogeneousSpecializationExt x (z - j)
  change (∑ j : Fin (N + 1), F j.val) = 0
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hNn : N ≤ n
  · have hsubset : Finset.range (N + 1) ⊆ Finset.range (n + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    calc
      (∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
            completeHomogeneousSpecializationExt x (z - j)) =
          ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
              completeHomogeneousSpecializationExt x (z - j) := by
        apply Finset.sum_subset hsubset
        intro j hj hsmall
        have hjN : N < j := by
          simp only [Finset.mem_range] at hj
          have hnot := hsmall
          simp only [Finset.mem_range, not_lt] at hnot
          omega
        have he : elementarySymmetricSpecialization x j = 0 :=
          elementarySymmetricSpecialization_eq_zero_of_card_lt x hjN
        rw [he]
        simp
      _ = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
            completeHomogeneousSpecialization x (n - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        unfold completeHomogeneousSpecializationExt
        rw [if_pos (by rw [← hzNat]; push_cast; omega)]
        congr 2
        omega
      _ = 0 := hbase
  · have hnN : n ≤ N := by omega
    have hsubset : Finset.range (n + 1) ⊆ Finset.range (N + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    calc
      (∑ j ∈ Finset.range (N + 1),
          (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
            completeHomogeneousSpecializationExt x (z - j)) =
          ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
              completeHomogeneousSpecializationExt x (z - j) := by
        symm
        apply Finset.sum_subset hsubset
        intro j hj hsmall
        have hjn : n < j := by
          simp only [Finset.mem_range] at hj
          have hnot := hsmall
          simp only [Finset.mem_range, not_lt] at hnot
          omega
        unfold completeHomogeneousSpecializationExt
        rw [if_neg]
        · simp
        · rw [← hzNat]
          push_cast
          omega
      _ = ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ j * elementarySymmetricSpecialization x j *
            completeHomogeneousSpecialization x (n - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        unfold completeHomogeneousSpecializationExt
        rw [if_pos (by rw [← hzNat]; push_cast; omega)]
        congr 2
        omega
      _ = 0 := hbase

/-! ## The normalized recurrence kernel -/

/-- The normalized coefficient vector of the quantum root polynomial.  The
extra factor `(-1)^r` makes its zeroth entry equal to one. -/
def quantumRecurrenceKernelComplex (r d : ℕ) : Fin (r + 1) → ℂ :=
  fun q => (-1 : ℂ) ^ r * (-1 : ℂ) ^ (r - q.val) *
    elementarySymmetricSpecialization (quantumAlphabetX r d) (r - q.val)

@[simp] theorem quantumRecurrenceKernelComplex_zero
    {r d : ℕ} : quantumRecurrenceKernelComplex r d 0 = 1 := by
  unfold quantumRecurrenceKernelComplex
  simp only [Fin.val_zero, Nat.sub_zero,
    elementarySymmetricSpecialization_top, quantumAlphabetX_prod]
  rw [← pow_add]
  simp [two_mul]

/-- Equation (32), including the initial extended-zero indices. -/
theorem quantumRecurrenceKernelComplex_recurrence
    {r d : ℕ} (ell : ℤ) (hell : 1 - r ≤ ell) :
    ∑ q : Fin (r + 1), quantumRecurrenceKernelComplex r d q *
      completeHomogeneousSpecializationExt (quantumAlphabetX r d)
        (ell + q.val) = 0 := by
  have hz : 0 < ell + r := by omega
  have hng := evaluated_newtonGirard_eh_extended
    (quantumAlphabetX r d) hz
  have hscaled := congrArg (fun z : ℂ => (-1 : ℂ) ^ r * z) hng
  simp only [mul_zero] at hscaled
  rw [Finset.mul_sum] at hscaled
  calc
    (∑ q : Fin (r + 1), quantumRecurrenceKernelComplex r d q *
        completeHomogeneousSpecializationExt (quantumAlphabetX r d)
          (ell + q.val)) =
        ∑ q : Fin (r + 1), (-1 : ℂ) ^ r *
          ((-1 : ℂ) ^ (Fin.rev q).val *
            elementarySymmetricSpecialization (quantumAlphabetX r d)
              (Fin.rev q).val *
            completeHomogeneousSpecializationExt (quantumAlphabetX r d)
              (ell + r - (Fin.rev q).val)) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold quantumRecurrenceKernelComplex
      have hqr : q.val ≤ r := by omega
      have hrev : (Fin.rev q).val = r - q.val := by
        simp only [Fin.val_rev]
        omega
      have hindex : ell + (q.val : ℤ) =
          ell + (r : ℤ) - ((r - q.val : ℕ) : ℤ) := by
        rw [Nat.cast_sub hqr]
        ring
      rw [hrev, ← hindex]
      ring
    _ = ∑ j : Fin (r + 1), (-1 : ℂ) ^ r *
          ((-1 : ℂ) ^ j.val *
            elementarySymmetricSpecialization (quantumAlphabetX r d) j.val *
            completeHomogeneousSpecializationExt (quantumAlphabetX r d)
              (ell + r - j.val)) := by
      let f : Fin (r + 1) → ℂ := fun j => (-1 : ℂ) ^ r *
        ((-1 : ℂ) ^ j.val *
          elementarySymmetricSpecialization (quantumAlphabetX r d) j.val *
          completeHomogeneousSpecializationExt (quantumAlphabetX r d)
            (ell + r - j.val))
      change (∑ q : Fin (r + 1), f (Fin.revPerm q)) = ∑ j, f j
      exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (r + 1))) f
    _ = 0 := hscaled

/-- On the index interval occurring in the interior blocks, the extended
complete specialization equals the real quantum band coefficient. -/
theorem completeHomogeneousSpecializationExt_quantum_eq_bandCoefficient
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) {z : ℤ}
    (hzUpper : z < d + r) :
    completeHomogeneousSpecializationExt (quantumAlphabetX r d) z =
      (quantumBandCoefficient r d z : ℂ) := by
  by_cases hz0 : 0 ≤ z
  · unfold completeHomogeneousSpecializationExt
    rw [if_pos hz0]
    by_cases hzd : z ≤ d
    · rw [quantumAlphabetX_complete_eq_coe_quantumBinomialCoefficient
        hr hd (by omega)]
      unfold quantumBandCoefficient
      rw [dif_pos ⟨hz0, hzd⟩]
    · let s := z.toNat - d
      have hs : 1 ≤ s := by
        dsimp only [s]
        omega
      have hsr : s < r := by
        dsimp only [s]
        omega
      have hzEq : z.toNat = d + s := by
        dsimp only [s]
        omega
      rw [hzEq, quantumAlphabetX_complete_zero_above hr hd hs hsr]
      unfold quantumBandCoefficient
      rw [dif_neg]
      · norm_num
      · omega
  · unfold completeHomogeneousSpecializationExt
    rw [if_neg hz0]
    unfold quantumBandCoefficient
    rw [dif_neg]
    · norm_num
    · omega

/-! ## Reality and block kernels -/

/-- The quantum-binomial coefficient vector is palindromic. -/
theorem quantumBinomialCoefficient_symmetry
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    quantumBinomialCoefficient r d (d - t) =
      quantumBinomialCoefficient r d t := by
  unfold quantumBinomialCoefficient
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  congr 1
  have hN : ((d + r : ℕ) : ℝ) * quantumTheta r d = Real.pi := by
    rw [quantumTheta]
    have hne : ((d + r : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  calc
    (∏ l : Fin (r - 1),
        Real.sin (((d - t + l.val + 1 : ℕ) : ℝ) *
          quantumTheta r d)) =
        ∏ l : Fin (r - 1),
          Real.sin (((t + (Fin.rev l).val + 1 : ℕ) : ℝ) *
            quantumTheta r d) := by
      apply Finset.prod_congr rfl
      intro l hl
      have hsum : d + r =
          (d - t + l.val + 1) + (t + (Fin.rev l).val + 1) := by
        simp only [Fin.val_rev]
        have hlb := l.isLt
        omega
      have harg : (((d - t + l.val + 1 : ℕ) : ℝ) *
          quantumTheta r d) = Real.pi -
            (((t + (Fin.rev l).val + 1 : ℕ) : ℝ) *
              quantumTheta r d) := by
        rw [← hN]
        have hsumR : ((d + r : ℕ) : ℝ) =
            ((d - t + l.val + 1 : ℕ) : ℝ) +
              ((t + (Fin.rev l).val + 1 : ℕ) : ℝ) := by
          exact_mod_cast hsum
        rw [hsumR]
        ring
      rw [harg, Real.sin_pi_sub]
    _ = ∏ l : Fin (r - 1),
        Real.sin (((t + l.val + 1 : ℕ) : ℝ) * quantumTheta r d) := by
      simpa using Equiv.prod_comp
        (Fin.revPerm : Equiv.Perm (Fin (r - 1)))
        (fun l : Fin (r - 1) =>
          Real.sin (((t + l.val + 1 : ℕ) : ℝ) * quantumTheta r d))

/-- Palindromic continuation of the band-supported coefficient function. -/
theorem quantumBandCoefficient_reflect
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (z : ℤ) :
    quantumBandCoefficient r d (d - z) = quantumBandCoefficient r d z := by
  unfold quantumBandCoefficient
  by_cases hz : 0 ≤ z ∧ z ≤ d
  · have hreflect : 0 ≤ (d : ℤ) - z ∧ (d : ℤ) - z ≤ d := by
      omega
    rw [dif_pos hz, dif_pos hreflect]
    have htoNat : ((d : ℤ) - z).toNat = d - z.toNat := by omega
    rw [htoNat, quantumBinomialCoefficient_symmetry hr hd (by omega)]
  · have hreflect : ¬(0 ≤ (d : ℤ) - z ∧
        (d : ℤ) - z ≤ d) := by
      omega
    rw [dif_neg hz, dif_neg hreflect]

/-- The real normalized recurrence vector. -/
def quantumRecurrenceKernel (r d : ℕ) : Fin (r + 1) → ℝ :=
  fun q => (quantumRecurrenceKernelComplex r d q).re

@[simp] theorem quantumRecurrenceKernel_zero (r d : ℕ) :
    quantumRecurrenceKernel r d 0 = 1 := by
  simp [quantumRecurrenceKernel]

theorem quantumRecurrenceKernel_last (r d : ℕ) :
    quantumRecurrenceKernel r d (Fin.last r) = (-1 : ℝ) ^ r := by
  unfold quantumRecurrenceKernel quantumRecurrenceKernelComplex
  simp only [Fin.val_last, Nat.sub_self,
    elementarySymmetricSpecialization_zero, pow_zero, mul_one]
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, pow_succ, Complex.mul_re]
      simp [ih]

theorem quantumRecurrenceKernel_last_ne_zero (r d : ℕ) :
    quantumRecurrenceKernel r d (Fin.last r) ≠ 0 := by
  rw [quantumRecurrenceKernel_last]
  exact pow_ne_zero _ (by norm_num)

/-! ## Constant Casoratian of the quantum recurrence -/

/-- The order-`r` consecutive Toeplitz block whose determinant is the
principal cofactor in equation (33). -/
def quantumCofactorBlock (r d u : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => quantumBandCoefficient r d
    ((u : ℤ) + (j.val : ℤ) - (i.val : ℤ))

/-- The companion matrix advancing one consecutive order-`r` block. -/
def quantumShiftCompanion (r d : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    if j.val + 1 < r then
      if i.val = j.val + 1 then 1 else 0
    else
      -quantumRecurrenceKernel r d i.castSucc /
        quantumRecurrenceKernel r d (Fin.last r)

/-- Real form of the Newton--Girard recurrence on the full band interval. -/
theorem quantumBandCoefficient_recurrence
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (ell : ℤ) (hell : 1 - r ≤ ell) (hupper : ell + r < d + r) :
    ∑ q : Fin (r + 1), quantumRecurrenceKernel r d q *
      quantumBandCoefficient r d (ell + q.val) = 0 := by
  have hrec := quantumRecurrenceKernelComplex_recurrence
    (r := r) (d := d) ell hell
  have hcoeff : ∀ q : Fin (r + 1),
      completeHomogeneousSpecializationExt (quantumAlphabetX r d)
          (ell + q.val) =
        (quantumBandCoefficient r d (ell + q.val) : ℂ) := by
    intro q
    apply completeHomogeneousSpecializationExt_quantum_eq_bandCoefficient
      hr hd
    have hq := q.isLt
    omega
  simp_rw [hcoeff] at hrec
  have hre := congrArg Complex.re hrec
  simp only [map_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, map_zero] at hre
  simpa [quantumRecurrenceKernel] using hre

/-- Solve the recurrence for its last coefficient. -/
theorem quantumBandCoefficient_solve_last
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (ell : ℤ) (hell : 1 - r ≤ ell) (hupper : ell + r < d + r) :
    (∑ q : Fin r,
        quantumBandCoefficient r d (ell + q.val) *
          (-quantumRecurrenceKernel r d q.castSucc /
            quantumRecurrenceKernel r d (Fin.last r))) =
      quantumBandCoefficient r d (ell + r) := by
  have hrec := quantumBandCoefficient_recurrence hr hd ell hell hupper
  rw [Fin.sum_univ_castSucc] at hrec
  simp only [Fin.val_castSucc, Fin.val_last] at hrec
  have hv : quantumRecurrenceKernel r d (Fin.last r) ≠ 0 :=
    quantumRecurrenceKernel_last_ne_zero r d
  calc
    (∑ q : Fin r,
        quantumBandCoefficient r d (ell + q.val) *
          (-quantumRecurrenceKernel r d q.castSucc /
            quantumRecurrenceKernel r d (Fin.last r))) =
        ∑ q : Fin r,
          (-(quantumRecurrenceKernel r d q.castSucc *
            quantumBandCoefficient r d (ell + q.val))) /
              quantumRecurrenceKernel r d (Fin.last r) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ =
        -(∑ q : Fin r, quantumRecurrenceKernel r d q.castSucc *
          quantumBandCoefficient r d (ell + q.val)) /
            quantumRecurrenceKernel r d (Fin.last r) := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ = quantumBandCoefficient r d (ell + r) := by
      apply (div_eq_iff hv).2
      linarith

/-- Advancing the anchor multiplies the cofactor block by the fixed
companion matrix. -/
theorem quantumCofactorBlock_succ_eq_mul
    {r d u : ℕ} (hr : 0 < r) (hd : 0 < d) (hu : u + 1 < d) :
    quantumCofactorBlock r d (u + 1) =
      quantumCofactorBlock r d u * quantumShiftCompanion r d := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 < r
  · rw [show quantumCofactorBlock r d (u + 1) i j =
        quantumCofactorBlock r d u i ⟨j.val + 1, hj⟩ by
      unfold quantumCofactorBlock
      congr 2
      push_cast
      ring]
    rw [Finset.sum_eq_single ⟨j.val + 1, hj⟩]
    · simp [quantumShiftCompanion, hj]
    · intro k hk hne
      simp only [quantumShiftCompanion, hj]
      have hval : k.val ≠ j.val + 1 := by
        intro h
        apply hne
        apply Fin.ext
        exact h
      simp [hval]
    · simp
  · have hjlast : j.val + 1 = r := by
      have hjbound := j.isLt
      omega
    have hell : 1 - r ≤ (u : ℤ) - i.val := by
      have hi := i.isLt
      omega
    have hupper : (u : ℤ) - i.val + r < d + r := by
      omega
    rw [show quantumCofactorBlock r d (u + 1) i j =
        quantumBandCoefficient r d (((u : ℤ) - i.val) + r) by
      unfold quantumCofactorBlock
      congr 2
      push_cast
      omega]
    rw [← quantumBandCoefficient_solve_last hr hd
      ((u : ℤ) - i.val) hell hupper]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [quantumCofactorBlock, quantumShiftCompanion, hj]
    congr 1
    push_cast
    ring

/-- The initial cofactor block is upper triangular with unit diagonal. -/
theorem quantumCofactorBlock_zero_det
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (quantumCofactorBlock r d 0).det = 1 := by
  have htri : (quantumCofactorBlock r d 0).BlockTriangular id := by
    intro i j hji
    unfold quantumCofactorBlock
    have hji' : j.val < i.val := by simpa using hji
    unfold quantumBandCoefficient
    rw [dif_neg]
    omega
  rw [Matrix.det_of_upperTriangular htri]
  have hdiag : ∀ i : Fin r, quantumCofactorBlock r d 0 i i = 1 := by
    intro i
    unfold quantumCofactorBlock
    simp only [Nat.cast_zero, zero_add, sub_self]
    exact quantumBandCoefficient_zero hr hd
  simp_rw [hdiag]
  simp

/-- The shift companion has determinant one.  This is the finite
Casoratian form of the product-one property of the root alphabet. -/
theorem quantumShiftCompanion_det
    {r d : ℕ} (hr : 0 < r) :
    (quantumShiftCompanion r d).det = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  let C := quantumShiftCompanion (n + 1) d
  let σ : Equiv.Perm (Fin (n + 1)) := (finRotate (n + 1)).symm
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := C.submatrix id σ
  have hsigmaZero : σ 0 = Fin.last n := by
    apply (finRotate (n + 1)).injective
    simp [σ]
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hji
    have hij : i < j := by simpa using hji
    have hj0 : j ≠ 0 := by
      intro hj
      subst j
      exact (not_lt_of_ge (Fin.zero_le i) hij).elim
    have hsigmaVal : (σ j).val = j.val - 1 := by
      dsimp only [σ]
      rw [coe_finRotate_symm_of_ne_zero hj0]
    rw [show M i j = C i (σ j) by rfl]
    unfold C quantumShiftCompanion
    have hcond : (σ j).val + 1 < n + 1 := by
      have hjbound := j.isLt
      omega
    rw [if_pos hcond]
    have hne : i.val ≠ (σ j).val + 1 := by
      have hijVal : i.val < j.val := by simpa using hij
      omega
    rw [if_neg hne]
  have hdiag : ∀ i : Fin (n + 1), M i i =
      if i = 0 then (-1 : ℝ) ^ n else 1 := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      rw [show M 0 0 = C 0 (σ 0) by rfl, hsigmaZero]
      unfold C quantumShiftCompanion
      simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte,
        Fin.castSucc_zero, quantumRecurrenceKernel_zero,
        quantumRecurrenceKernel_last]
      rw [show -1 / (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n by
        have hpow : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ n) = -1 := by
          rw [← pow_add]
          have hodd : n + 1 + n = 2 * n + 1 := by omega
          rw [hodd, pow_succ, pow_mul, pow_two]
          norm_num
        apply (div_eq_iff (pow_ne_zero _ (by norm_num))).2
        nlinarith]
    · have hsigmaVal : (σ i).val = i.val - 1 := by
        dsimp only [σ]
        rw [coe_finRotate_symm_of_ne_zero hi0]
      rw [show M i i = C i (σ i) by rfl]
      unfold C quantumShiftCompanion
      have hcond : (σ i).val + 1 < n + 1 := by
        have hi := i.isLt
        omega
      have hiValNe : i.val ≠ 0 := by
        intro h
        apply hi0
        exact Fin.ext h
      have hiPos : 0 < i.val := Nat.pos_of_ne_zero hiValNe
      have heq : i.val = (σ i).val + 1 := by omega
      rw [if_pos hcond, if_pos heq]
      simp [hi0]
  have hdetM : M.det = (-1 : ℝ) ^ n := by
    rw [Matrix.det_of_lowerTriangular M htri]
    simp_rw [hdiag]
    rw [Fin.prod_univ_succ]
    simp
  have hperm := Matrix.det_permute' σ C
  change M.det = Equiv.Perm.sign σ * C.det at hperm
  rw [hdetM] at hperm
  simp [σ, Equiv.Perm.sign_inv, sign_finRotate] at hperm
  norm_num only [Int.cast_pow, Int.cast_neg, Int.cast_one] at hperm
  change C.det = 1
  exact hperm

/-- Every consecutive order-`r` cofactor block has determinant one. -/
theorem quantumCofactorBlock_det_eq_one
    {r d u : ℕ} (hr : 0 < r) (hd : 0 < d) (hu : u < d) :
    (quantumCofactorBlock r d u).det = 1 := by
  induction u with
  | zero => exact quantumCofactorBlock_zero_det hr hd
  | succ u ih =>
      have hu' : u < d := by omega
      have hstep := quantumCofactorBlock_succ_eq_mul hr hd hu
      rw [hstep, Matrix.det_mul, ih hu', quantumShiftCompanion_det hr, one_mul]

/-- The interior block with anchor `t+1`. -/
def quantumInteriorBlock (r d : ℕ) (t : Fin (d - 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j => quantumBandCoefficient r d
    ((t.val + 1 : ℕ) + (j.val : ℤ) - (i.val : ℤ))

/-- Every interior block has the normalized real recurrence vector in its
right kernel. -/
theorem quantumInteriorBlock_mulVec_kernel_eq_zero
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    quantumInteriorBlock r d t *ᵥ quantumRecurrenceKernel r d = 0 := by
  funext i
  let ell : ℤ := (t.val + 1 : ℕ) - (i.val : ℤ)
  have hell : 1 - r ≤ ell := by
    dsimp only [ell]
    have hi := i.isLt
    omega
  have hrec := quantumRecurrenceKernelComplex_recurrence
    (r := r) (d := d) ell hell
  have hcoeff : ∀ q : Fin (r + 1),
      completeHomogeneousSpecializationExt (quantumAlphabetX r d)
          (ell + q.val) =
        (quantumBandCoefficient r d (ell + q.val) : ℂ) := by
    intro q
    apply completeHomogeneousSpecializationExt_quantum_eq_bandCoefficient
      hr (by omega)
    dsimp only [ell]
    have ht := t.isLt
    have hq := q.isLt
    omega
  simp_rw [hcoeff] at hrec
  have hre := congrArg Complex.re hrec
  simp only [map_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, map_zero] at hre
  change (∑ q : Fin (r + 1), quantumBandCoefficient r d
      ((t.val + 1 : ℕ) + (q.val : ℤ) - (i.val : ℤ)) *
        quantumRecurrenceKernel r d q) = 0
  calc
    (∑ q : Fin (r + 1), quantumBandCoefficient r d
        ((t.val + 1 : ℕ) + (q.val : ℤ) - (i.val : ℤ)) *
          quantumRecurrenceKernel r d q) =
        ∑ q : Fin (r + 1), quantumRecurrenceKernel r d q *
          quantumBandCoefficient r d (ell + q.val) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hindex : ((t.val + 1 : ℕ) : ℤ) + (q.val : ℤ) -
          (i.val : ℤ) = ell + q.val := by
        dsimp only [ell]
        push_cast
        ring
      rw [hindex]
      ring
    _ = 0 := by
      simpa [quantumRecurrenceKernel] using hre

/-- Rows of the principal cofactor minor of an interior block. -/
def quantumInteriorPrincipalRows (r : ℕ) : Fin r ↪o Fin (r + 1) :=
  Fin.succOrderEmb r

/-- Columns of the principal cofactor minor inside the full quantum band
matrix. -/
def quantumInteriorPrincipalCols
    {r d : ℕ} (t : Fin (d - 1)) : Fin r ↪o Fin (d + r + 1) :=
  OrderEmbedding.ofStrictMono
    (fun j => ⟨t.val + 2 + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hij) (t.val + 2))

theorem quantumInteriorPrincipal_bandFeasible
    {r d : ℕ} (hd : 1 < d) (t : Fin (d - 1)) :
    BandFeasible (quantumInteriorPrincipalRows r)
      (quantumInteriorPrincipalCols (r := r) t) := by
  intro j
  change j.val + 1 ≤ t.val + 2 + j.val ∧
    t.val + 2 + j.val ≤ j.val + 1 + d
  have ht := t.isLt
  constructor <;> omega

/-- The principal cofactor minor is exactly a lower-order quantum band
minor. -/
theorem quantumInteriorBlock_principalMinor_eq_orderedMinor
    {r d : ℕ} (t : Fin (d - 1)) :
    ((quantumInteriorBlock r d t).submatrix
      (Fin.succOrderEmb r) (Fin.succOrderEmb r)).det =
      orderedMinor (quantumBandMatrix r d)
        (quantumInteriorPrincipalRows r)
        (quantumInteriorPrincipalCols (r := r) t) := by
  unfold orderedMinor
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, quantumInteriorBlock,
    quantumInteriorPrincipalRows, quantumInteriorPrincipalCols,
    Fin.val_succ, quantumBandMatrix_apply]
  change quantumBandCoefficient r d
      (((t.val + 1 : ℕ) : ℤ) + (j.val + 1 : ℕ) - (i.val + 1 : ℕ)) =
    quantumBandCoefficient r d
      ((t.val + 2 + j.val : ℕ) - (i.val + 1 : ℕ))
  congr 2
  push_cast
  ring

/-- Every interior principal cofactor is strictly positive. -/
theorem quantumInteriorBlock_principalMinor_pos
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    0 < ((quantumInteriorBlock r d t).submatrix
      (Fin.succOrderEmb r) (Fin.succOrderEmb r)).det := by
  rw [quantumInteriorBlock_principalMinor_eq_orderedMinor]
  apply quantumBandMatrix_orderedMinor_pos_of_bandFeasible
    hr (by omega) (le_refl r)
  exact quantumInteriorPrincipal_bandFeasible hd t

/-- Simultaneously reversing rows and columns identifies reflected interior
blocks. -/
theorem quantumInteriorBlock_reflect
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    (quantumInteriorBlock r d (Fin.rev t)).submatrix Fin.rev Fin.rev =
      quantumInteriorBlock r d t := by
  ext i j
  simp only [Matrix.submatrix_apply, quantumInteriorBlock, Fin.val_rev]
  let z : ℤ := (((Fin.rev t).val + 1 : ℕ) : ℤ) +
    ((Fin.rev j).val : ℤ) - ((Fin.rev i).val : ℤ)
  change quantumBandCoefficient r d z =
    quantumBandCoefficient r d
      (((t.val + 1 : ℕ) : ℤ) + j.val - i.val)
  calc
    quantumBandCoefficient r d z =
        quantumBandCoefficient r d (d - z) :=
      (quantumBandCoefficient_reflect hr (by omega) z).symm
    _ = quantumBandCoefficient r d
        (((t.val + 1 : ℕ) : ℤ) + j.val - i.val) := by
      apply congrArg (quantumBandCoefficient r d)
      have htRev : (Fin.rev t).val + t.val + 1 = d - 1 := by
        simp only [Fin.val_rev]
        have ht := t.isLt
        omega
      have hiRev : (Fin.rev i).val + i.val + 1 = r + 1 := by
        simp only [Fin.val_rev]
        have hi := i.isLt
        omega
      have hjRev : (Fin.rev j).val + j.val + 1 = r + 1 := by
        simp only [Fin.val_rev]
        have hj := j.isLt
        omega
      have htRevZ : ((Fin.rev t).val : ℤ) + t.val + 1 = d - 1 := by
        calc
          ((Fin.rev t).val : ℤ) + t.val + 1 = ((d - 1 : ℕ) : ℤ) := by
            exact_mod_cast htRev
          _ = (d : ℤ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            norm_num
      have hiRevZ : ((Fin.rev i).val : ℤ) + i.val + 1 = r + 1 := by
        exact_mod_cast hiRev
      have hjRevZ : ((Fin.rev j).val : ℤ) + j.val + 1 = r + 1 := by
        exact_mod_cast hjRev
      dsimp only [z]
      push_cast
      omega

/-- Reversing the normalized kernel multiplies it by its nonzero last
coefficient. -/
theorem quantumRecurrenceKernel_rev
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d)
    (t : Fin (d - 1)) (q : Fin (r + 1)) :
    quantumRecurrenceKernel r d (Fin.rev q) =
      quantumRecurrenceKernel r d (Fin.last r) *
        quantumRecurrenceKernel r d q := by
  let v := quantumRecurrenceKernel r d
  let vrev : Fin (r + 1) → ℝ := fun q => v (Fin.rev q)
  let B := quantumInteriorBlock r d t
  let Brev := quantumInteriorBlock r d (Fin.rev t)
  have hB : Brev.submatrix Fin.rev Fin.rev = B :=
    quantumInteriorBlock_reflect hr hd t
  have hright : B *ᵥ v = 0 :=
    quantumInteriorBlock_mulVec_kernel_eq_zero hr hd t
  have hrightRev : Brev *ᵥ v = 0 :=
    quantumInteriorBlock_mulVec_kernel_eq_zero hr hd (Fin.rev t)
  have hvrev : B *ᵥ vrev = 0 := by
    funext i
    have hi := congrFun hrightRev (Fin.rev i)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi ⊢
    calc
      (∑ j : Fin (r + 1), B i j * vrev j) =
          ∑ j : Fin (r + 1), Brev (Fin.rev i) (Fin.rev j) *
            v (Fin.rev j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hB]
        rfl
      _ = ∑ j : Fin (r + 1), Brev (Fin.rev i) j * v j := by
        let f : Fin (r + 1) → ℝ := fun j => Brev (Fin.rev i) j * v j
        change (∑ j : Fin (r + 1), f (Fin.revPerm j)) = ∑ j, f j
        exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (r + 1))) f
      _ = 0 := hi
  have hminorNe : ((B.submatrix (Fin.succOrderEmb r)
      (Fin.succOrderEmb r)).det) ≠ 0 :=
    (quantumInteriorBlock_principalMinor_pos hr hd t).ne'
  have huniq := eq_smul_kernelVector_of_mulVec_eq_zero B v vrev
    (quantumRecurrenceKernel_zero r d) hright hminorNe hvrev
  have hq := congrFun huniq q
  simpa [v, vrev, Pi.smul_apply, smul_eq_mul] using hq

/-- The same recurrence vector is a left kernel of every interior block. -/
theorem quantumRecurrenceKernel_vecMul_interiorBlock_eq_zero
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    quantumRecurrenceKernel r d ᵥ* quantumInteriorBlock r d t = 0 := by
  funext j
  let v := quantumRecurrenceKernel r d
  let c := v (Fin.last r)
  have hc : c ≠ 0 := quantumRecurrenceKernel_last_ne_zero r d
  have hright := quantumInteriorBlock_mulVec_kernel_eq_zero hr hd t
  have hrev : ∀ i, v (Fin.rev i) = c * v i :=
    quantumRecurrenceKernel_rev hr hd t
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  have hj := congrFun hright (Fin.rev j)
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hj
  have hscaled : c * (∑ i : Fin (r + 1),
      v i * quantumInteriorBlock r d t i j) = 0 := by
    calc
      c * (∑ i : Fin (r + 1), v i * quantumInteriorBlock r d t i j) =
          ∑ i : Fin (r + 1), v (Fin.rev i) *
            quantumInteriorBlock r d t i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrev]
        ring
      _ = ∑ i : Fin (r + 1), v i *
          quantumInteriorBlock r d t (Fin.rev i) j := by
        let f : Fin (r + 1) → ℝ := fun i =>
          v i * quantumInteriorBlock r d t (Fin.rev i) j
        have hs := Equiv.sum_comp
          (Fin.revPerm : Equiv.Perm (Fin (r + 1))) f
        simpa [f] using hs
      _ = ∑ i : Fin (r + 1),
          quantumInteriorBlock r d t (Fin.rev j) i * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold quantumInteriorBlock
        rw [mul_comm]
        congr 2
        simp only [Fin.val_rev]
        have hi' := i.isLt
        have hj' := j.isLt
        rw [Nat.cast_sub (by omega : i.val + 1 ≤ r + 1),
          Nat.cast_sub (by omega : j.val + 1 ≤ r + 1)]
        push_cast
        ring
      _ = 0 := hj
  exact (mul_eq_zero.mp hscaled).resolve_left hc

/-! ## The concrete quantum Jacobian -/

/-- Positive principal cofactor of an interior block. -/
def quantumInteriorKappa (r d : ℕ) (t : Fin (d - 1)) : ℝ :=
  ((quantumInteriorBlock r d t).submatrix
    (Fin.succOrderEmb r) (Fin.succOrderEmb r)).det

/-- The principal cofactor in equation (33) is exactly one. -/
@[simp]
theorem quantumInteriorKappa_eq_one
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    quantumInteriorKappa r d t = 1 := by
  rw [show quantumInteriorKappa r d t =
      (quantumCofactorBlock r d (t.val + 1)).det by
    unfold quantumInteriorKappa quantumInteriorBlock quantumCofactorBlock
    congr 1
    ext i j
    change quantumBandCoefficient r d
        (((t.val + 1 : ℕ) : ℤ) + (j.val + 1 : ℕ) - (i.val + 1 : ℕ)) =
      quantumBandCoefficient r d
        (((t.val + 1 : ℕ) : ℤ) + (j.val : ℤ) - (i.val : ℤ))
    apply congrArg (quantumBandCoefficient r d)
    push_cast
    ring]
  apply quantumCofactorBlock_det_eq_one hr (by omega)
  have ht := t.isLt
  omega

theorem quantumInteriorKappa_pos
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    0 < quantumInteriorKappa r d t :=
  by rw [quantumInteriorKappa_eq_one hr hd]; norm_num

theorem quantumInteriorBlock_det_eq_zero
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    (quantumInteriorBlock r d t).det = 0 := by
  apply (Matrix.exists_mulVec_eq_zero_iff).1
  refine ⟨quantumRecurrenceKernel r d, ?_,
    quantumInteriorBlock_mulVec_kernel_eq_zero hr hd t⟩
  intro hzero
  have hcoord := congrFun hzero 0
  simp at hcoord

/-- Equation (33), with the positive principal cofactor retained as an
explicit row scale. -/
theorem quantumInteriorBlock_adjugate_eq
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    (quantumInteriorBlock r d t).adjugate =
      quantumInteriorKappa r d t •
        Matrix.vecMulVec (quantumRecurrenceKernel r d)
          (quantumRecurrenceKernel r d) := by
  apply adjugate_eq_principalMinor_smul_vecMulVec_of_normalized_kernel
  · exact quantumRecurrenceKernel_zero r d
  · exact quantumInteriorBlock_mulVec_kernel_eq_zero hr hd t
  · exact quantumRecurrenceKernel_vecMul_interiorBlock_eq_zero hr hd t
  · exact (quantumInteriorKappa_pos hr hd t).ne'
  · exact quantumInteriorBlock_det_eq_zero hr hd t

/-- Equation (33) in the exact normalization used in the paper. -/
theorem quantumInteriorBlock_adjugate_eq_vecMulVec
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) (t : Fin (d - 1)) :
    (quantumInteriorBlock r d t).adjugate =
      Matrix.vecMulVec (quantumRecurrenceKernel r d)
        (quantumRecurrenceKernel r d) := by
  rw [quantumInteriorBlock_adjugate_eq hr hd t,
    quantumInteriorKappa_eq_one hr hd t, one_smul]

/-- The actual interior consecutive-minor Jacobian at the quantum point. -/
def quantumInteriorJacobian (r d : ℕ) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ := fun t s =>
  ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
    toeplitzBlockDirection t s i j *
      (quantumInteriorBlock r d t).adjugate j i

/-- The quantum Jacobian is a positive diagonal row scaling of the
autocorrelation Gram kernel. -/
theorem quantumInteriorJacobian_eq_diagonal_mul_autocorrelation
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumInteriorJacobian r d =
      Matrix.diagonal (quantumInteriorKappa r d) *
        autocorrelationKernel (quantumRecurrenceKernel r d) (d - 1) := by
  ext t s
  unfold quantumInteriorJacobian
  rw [quantumInteriorBlock_adjugate_eq hr hd t]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply]
  rw [show (∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      toeplitzBlockDirection t s i j *
        (quantumInteriorKappa r d t •
          (quantumRecurrenceKernel r d j *
            quantumRecurrenceKernel r d i))) =
      quantumInteriorKappa r d t *
        cofactorAutocorrelationJacobian (quantumRecurrenceKernel r d)
          (d - 1) t s by
    unfold cofactorAutocorrelationJacobian
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [smul_eq_mul]
    ring]
  rw [cofactorAutocorrelationJacobian_eq_autocorrelationKernel]
  exact (Matrix.diagonal_mul _ _ t s).symm

/-- Equation (30): the actual consecutive-minor Jacobian is exactly the
symmetric Toeplitz autocorrelation kernel. -/
theorem quantumInteriorJacobian_eq_autocorrelation
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    quantumInteriorJacobian r d =
      autocorrelationKernel (quantumRecurrenceKernel r d) (d - 1) := by
  rw [quantumInteriorJacobian_eq_diagonal_mul_autocorrelation hr hd]
  have hdiag : Matrix.diagonal (quantumInteriorKappa r d) =
      (1 : Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [quantumInteriorKappa_eq_one hr hd]
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  rw [hdiag, one_mul]

/-- Theorem 5.4: the actual Jacobian is symmetric positive definite. -/
theorem quantumInteriorJacobian_posDef
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    (quantumInteriorJacobian r d).PosDef := by
  rw [quantumInteriorJacobian_eq_autocorrelation hr hd]
  exact autocorrelationKernel_posDef (by simp)

/-- Symmetry of the actual Jacobian, stated separately for convenient use. -/
theorem quantumInteriorJacobian_isSymm
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    (quantumInteriorJacobian r d).IsSymm := by
  rw [quantumInteriorJacobian_eq_autocorrelation hr hd]
  exact autocorrelationKernel_isSymm _

/-- The concrete Jacobian has positive determinant and is invertible. -/
theorem quantumInteriorJacobian_det_pos
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    0 < (quantumInteriorJacobian r d).det := by
  rw [quantumInteriorJacobian_eq_diagonal_mul_autocorrelation hr hd,
    Matrix.det_mul, Matrix.det_diagonal]
  apply mul_pos
  · apply Finset.prod_pos
    intro t ht
    exact quantumInteriorKappa_pos hr hd t
  · exact (autocorrelationKernel_posDef
      (v := quantumRecurrenceKernel r d) (N := d - 1)
      (by simp)).det_pos

/-- Continuous linear equivalence represented by the concrete Jacobian. -/
noncomputable def quantumInteriorJacobianEquiv
    {r d : ℕ} (hr : 0 < r) (hd : 1 < d) :
    (Fin (d - 1) → ℝ) ≃L[ℝ] (Fin (d - 1) → ℝ) := by
  let J := quantumInteriorJacobian r d
  have hdet : J.det ≠ 0 := (quantumInteriorJacobian_det_pos hr hd).ne'
  letI : Invertible J.det := invertibleOfNonzero hdet
  letI : Invertible J := Matrix.invertibleOfDetInvertible J
  exact (J.toLinearEquiv' inferInstance).toContinuousLinearEquiv

end

end FurtherToeplitzPositroids
