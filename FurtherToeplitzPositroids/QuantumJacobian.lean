import FurtherToeplitzPositroids.LoopPavingEnumeration
import PavingToeplitzPositroids.PolynomialJacobian

/-!
# Adjugate kernels and the Toeplitz autocorrelation Jacobian

This module formalizes the linear-algebraic part of Theorem 5.4 independently
of the root-of-unity specialization.
-/

namespace FurtherToeplitzPositroids

open Matrix PavingToeplitzPositroids

noncomputable section

/-- A square matrix with a normalized one-dimensional left and right kernel
has rank-one adjugate. -/
theorem adjugate_eq_vecMulVec_of_normalized_kernel
    {p : ℕ} (B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (v : Fin (p + 1) → ℝ) (hv0 : v 0 = 1)
    (hright : B *ᵥ v = 0) (hleft : v ᵥ* B = 0)
    (hminor : (B.submatrix (Fin.succOrderEmb p)
      (Fin.succOrderEmb p)).det = 1)
    (hdet : B.det = 0) :
    B.adjugate = Matrix.vecMulVec v v := by
  have hminor_ne :
      (B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det ≠ 0 := by
    rw [hminor]
    norm_num
  have hBA : B * B.adjugate = 0 := by
    rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hAB : B.adjugate * B = 0 := by
    rw [Matrix.adjugate_mul, hdet, zero_smul]
  have h00 : B.adjugate 0 0 = 1 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hsub : B.submatrix (0 : Fin (p + 1)).succAbove
        (0 : Fin (p + 1)).succAbove =
        B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p) := by
      ext i j
      rfl
    rw [hsub, hminor]
    simp
  ext i j
  have hcolZero : B *ᵥ (fun q ↦ B.adjugate q j) = 0 := by
    funext q
    simpa [Matrix.mulVec, Matrix.mul_apply] using
      congrArg (fun X ↦ X q j) hBA
  have hcol := eq_smul_kernelVector_of_mulVec_eq_zero B v
    (fun q ↦ B.adjugate q j) hv0 hright hminor_ne hcolZero
  have hrowZero : (fun q ↦ B.adjugate 0 q) ᵥ* B = 0 := by
    funext q
    simpa [Matrix.vecMul, Matrix.mul_apply] using
      congrArg (fun X ↦ X 0 q) hAB
  have hrow := eq_smul_kernelVector_of_vecMul_eq_zero B v
    (fun q ↦ B.adjugate 0 q) hv0 hleft hminor_ne hrowZero
  have hcolij := congrFun hcol i
  have hrowj := congrFun hrow j
  simp only [Pi.smul_apply, smul_eq_mul] at hcolij hrowj
  simp only [Matrix.vecMulVec_apply]
  rw [hcolij, hrowj, h00]
  ring

/-- Variant with an arbitrary nonzero principal cofactor. -/
theorem adjugate_eq_principalMinor_smul_vecMulVec_of_normalized_kernel
    {p : ℕ} (B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (v : Fin (p + 1) → ℝ) (hv0 : v 0 = 1)
    (hright : B *ᵥ v = 0) (hleft : v ᵥ* B = 0)
    (hminor : (B.submatrix (Fin.succOrderEmb p)
      (Fin.succOrderEmb p)).det ≠ 0)
    (hdet : B.det = 0) :
    B.adjugate =
      (B.submatrix (Fin.succOrderEmb p)
        (Fin.succOrderEmb p)).det • Matrix.vecMulVec v v := by
  let kappa := (B.submatrix (Fin.succOrderEmb p)
    (Fin.succOrderEmb p)).det
  have hBA : B * B.adjugate = 0 := by
    rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hAB : B.adjugate * B = 0 := by
    rw [Matrix.adjugate_mul, hdet, zero_smul]
  have h00 : B.adjugate 0 0 = kappa := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hsub : B.submatrix (0 : Fin (p + 1)).succAbove
        (0 : Fin (p + 1)).succAbove =
        B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p) := by
      ext i j
      rfl
    rw [hsub]
    simp [kappa]
  ext i j
  have hcolZero : B *ᵥ (fun q => B.adjugate q j) = 0 := by
    funext q
    simpa [Matrix.mulVec, Matrix.mul_apply] using
      congrArg (fun X => X q j) hBA
  have hcol := eq_smul_kernelVector_of_mulVec_eq_zero B v
    (fun q => B.adjugate q j) hv0 hright hminor hcolZero
  have hrowZero : (fun q => B.adjugate 0 q) ᵥ* B = 0 := by
    funext q
    simpa [Matrix.vecMul, Matrix.mul_apply] using
      congrArg (fun X => X 0 q) hAB
  have hrow := eq_smul_kernelVector_of_vecMul_eq_zero B v
    (fun q => B.adjugate 0 q) hv0 hleft hminor hrowZero
  have hcolij := congrFun hcol i
  have hrowj := congrFun hrow j
  simp only [Pi.smul_apply, smul_eq_mul] at hcolij hrowj
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply]
  rw [hcolij, hrowj, h00]
  change kappa * v j * v i = kappa • (v i * v j)
  rw [smul_eq_mul]
  ring

/-- The coefficient-coordinate direction inside one consecutive Toeplitz
block. -/
def toeplitzBlockDirection {p N : ℕ} (t s : Fin N) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun i j ↦ if t.val + j.val = s.val + i.val then 1 else 0

/-- The cofactor sum obtained by differentiating consecutive determinants. -/
def cofactorAutocorrelationJacobian {p : ℕ}
    (v : Fin (p + 1) → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun t s ↦ ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    toeplitzBlockDirection t s i j * v j * v i

theorem cofactor_sum_eq_autocorrelationCoefficient_of_le
    {p N : ℕ} (v : Fin (p + 1) → ℝ) {t s : Fin N} (hts : t ≤ s) :
    cofactorAutocorrelationJacobian v N t s =
      autocorrelationCoefficient v (s.val - t.val) := by
  unfold cofactorAutocorrelationJacobian autocorrelationCoefficient
  apply Fintype.sum_congr
  intro i
  by_cases hi : i.val + (s.val - t.val) < p + 1
  · let j0 : Fin (p + 1) := ⟨i.val + (s.val - t.val), hi⟩
    rw [Finset.sum_eq_single j0]
    · have heq : t.val + j0.val = s.val + i.val := by
        dsimp only [j0]
        have hts' := Fin.le_iff_val_le_val.mp hts
        omega
      simp only [toeplitzBlockDirection, if_pos heq, one_mul, dif_pos hi]
      apply congrArg (fun z : Fin (p + 1) ↦ v z * v i)
      apply Fin.ext
      rfl
    · intro j _ hj
      simp only [toeplitzBlockDirection]
      split_ifs with heq
      · exfalso
        apply hj
        apply Fin.ext
        dsimp only [j0]
        omega
      · simp
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro j _
      simp only [toeplitzBlockDirection]
      split_ifs with heq
      · exfalso
        apply hi
        have hj := j.isLt
        omega
      · simp

theorem cofactorAutocorrelationJacobian_apply_comm
    {p N : ℕ} (v : Fin (p + 1) → ℝ) (t s : Fin N) :
    cofactorAutocorrelationJacobian v N t s =
      cofactorAutocorrelationJacobian v N s t := by
  unfold cofactorAutocorrelationJacobian
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold toeplitzBlockDirection
  by_cases h : t.val + i.val = s.val + j.val
  · rw [if_pos h, if_pos h.symm]
    ring
  · rw [if_neg h, if_neg (fun h' ↦ h h'.symm)]
    ring

/-- Equation (30): the diagonal cofactor sums are exactly the finite
autocorrelation Gram kernel. -/
theorem cofactorAutocorrelationJacobian_eq_autocorrelationKernel
    {p N : ℕ} (v : Fin (p + 1) → ℝ) :
    cofactorAutocorrelationJacobian v N = autocorrelationKernel v N := by
  ext t s
  rcases le_total t s with hts | hst
  · rw [cofactor_sum_eq_autocorrelationCoefficient_of_le v hts,
      autocorrelationKernel_apply_of_le hts]
  · rw [cofactorAutocorrelationJacobian_apply_comm v t s,
      cofactor_sum_eq_autocorrelationCoefficient_of_le v hst,
      show autocorrelationKernel v N t s =
          autocorrelationKernel v N s t by
        simpa [Matrix.transpose_apply] using
          (congrFun (congrFun (autocorrelationKernel_isSymm v) t) s).symm,
      autocorrelationKernel_apply_of_le hst]

/-- The explicit Jacobian is symmetric positive definite. -/
theorem cofactorAutocorrelationJacobian_posDef
    {p N : ℕ} {v : Fin (p + 1) → ℝ} (hv0 : v 0 ≠ 0) :
    (cofactorAutocorrelationJacobian v N).PosDef := by
  rw [cofactorAutocorrelationJacobian_eq_autocorrelationKernel]
  exact autocorrelationKernel_posDef hv0

/-! ## Toeplitz recurrence certificates -/

/-- A square consecutive Toeplitz block with integer-indexed coefficients. -/
def recurrenceToeplitzBlock
    {p N : ℕ} (b : ℤ → ℝ) (t : Fin N) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun i j ↦ b ((t : ℤ) + (j : ℤ) - (i : ℤ))

/-- The recurrence, reversal, and principal-minor facts needed to produce the
block certificate in Theorem 5.4.  The determinant-zero and left-kernel
fields are derived rather than assumed. -/
structure ToeplitzRecurrenceCertificate (p N : ℕ) where
  coefficient : ℤ → ℝ
  kernel : Fin (p + 1) → ℝ
  epsilon : ℝ
  kernel_zero : kernel 0 = 1
  kernel_rev : ∀ q, kernel q.rev = epsilon * kernel q
  right_kernel : ∀ t : Fin N,
    recurrenceToeplitzBlock (p := p) (N := N) coefficient t *ᵥ kernel = 0
  principal_minor : ∀ t : Fin N,
    ((recurrenceToeplitzBlock (p := p) (N := N) coefficient t).submatrix
      (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det = 1

/-- Reversal symmetry of the recurrence vector turns every right kernel into
the corresponding left kernel, as in equation (28). -/
theorem ToeplitzRecurrenceCertificate.left_kernel
    {p N : ℕ} (C : ToeplitzRecurrenceCertificate p N) (t : Fin N) :
    C.kernel ᵥ* recurrenceToeplitzBlock (p := p) (N := N) C.coefficient t = 0 := by
  funext j
  have hright := congrFun (C.right_kernel t) j.rev
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hright
  change (∑ q : Fin (p + 1),
    C.coefficient ((t : ℤ) + (q : ℤ) - (j.rev : ℤ)) * C.kernel q) = 0 at hright
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
  let f : Fin (p + 1) → ℝ := fun i ↦
    C.kernel i * C.coefficient ((t : ℤ) + (j : ℤ) - (i : ℤ))
  change ∑ i, f i = 0
  have hindex : ∀ q : Fin (p + 1),
      (t : ℤ) + (j : ℤ) - (q.rev : ℤ) =
        (t : ℤ) + (q : ℤ) - (j.rev : ℤ) := by
    intro q
    simp only [Fin.val_rev]
    omega
  calc
    (∑ i, f i) = ∑ q : Fin (p + 1), f q.rev :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (p + 1))) f).symm
    _ = C.epsilon * ∑ q : Fin (p + 1),
        C.coefficient ((t : ℤ) + (q : ℤ) - (j.rev : ℤ)) * C.kernel q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [f]
      rw [C.kernel_rev, hindex]
      ring
    _ = 0 := by rw [hright, mul_zero]

/-- A normalized nonzero kernel forces every consecutive block determinant
to vanish. -/
theorem ToeplitzRecurrenceCertificate.determinant_zero
    {p N : ℕ} (C : ToeplitzRecurrenceCertificate p N) (t : Fin N) :
    (recurrenceToeplitzBlock (p := p) (N := N) C.coefficient t).det = 0 := by
  apply (Matrix.exists_mulVec_eq_zero_iff).1
  refine ⟨C.kernel, ?_, C.right_kernel t⟩
  intro hzero
  have hcoord := congrFun hzero 0
  simp [C.kernel_zero] at hcoord

/-- The recurrence and cofactor facts required from the quantum-binomial
base blocks. -/
structure ConsecutiveBlockKernelCertificate (p N : ℕ) where
  block : Fin N → Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ
  kernel : Fin (p + 1) → ℝ
  kernel_zero : kernel 0 = 1
  right_kernel : ∀ t, block t *ᵥ kernel = 0
  left_kernel : ∀ t, kernel ᵥ* block t = 0
  principal_minor : ∀ t,
    ((block t).submatrix (Fin.succOrderEmb p)
      (Fin.succOrderEmb p)).det = 1
  determinant_zero : ∀ t, (block t).det = 0

/-- Every Toeplitz recurrence certificate supplies the more redundant block
certificate used by the Jacobian theorem. -/
def ToeplitzRecurrenceCertificate.toConsecutiveBlockKernelCertificate
    {p N : ℕ} (C : ToeplitzRecurrenceCertificate p N) :
    ConsecutiveBlockKernelCertificate p N where
  block := recurrenceToeplitzBlock (p := p) (N := N) C.coefficient
  kernel := C.kernel
  kernel_zero := C.kernel_zero
  right_kernel := C.right_kernel
  left_kernel := C.left_kernel
  principal_minor := C.principal_minor
  determinant_zero := C.determinant_zero

/-- The adjugate conclusion (33) extracted from a block certificate. -/
theorem ConsecutiveBlockKernelCertificate.adjugate_eq
    {p N : ℕ} (C : ConsecutiveBlockKernelCertificate p N) (t : Fin N) :
    (C.block t).adjugate = Matrix.vecMulVec C.kernel C.kernel :=
  adjugate_eq_vecMulVec_of_normalized_kernel (C.block t) C.kernel
    C.kernel_zero (C.right_kernel t) (C.left_kernel t)
    (C.principal_minor t) (C.determinant_zero t)

/-- The Jacobian obtained by differentiating the certified blocks. -/
def ConsecutiveBlockKernelCertificate.jacobian
    {p N : ℕ} (C : ConsecutiveBlockKernelCertificate p N) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun t s ↦ ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    toeplitzBlockDirection t s i j * (C.block t).adjugate j i

/-- A certified consecutive-minor Jacobian is the autocorrelation kernel. -/
theorem ConsecutiveBlockKernelCertificate.jacobian_eq
    {p N : ℕ} (C : ConsecutiveBlockKernelCertificate p N) :
    C.jacobian = autocorrelationKernel C.kernel N := by
  calc
    C.jacobian = cofactorAutocorrelationJacobian C.kernel N := by
      ext t s
      unfold ConsecutiveBlockKernelCertificate.jacobian
        cofactorAutocorrelationJacobian
      rw [C.adjugate_eq t]
      simp only [Matrix.vecMulVec_apply, mul_assoc]
    _ = autocorrelationKernel C.kernel N :=
      cofactorAutocorrelationJacobian_eq_autocorrelationKernel C.kernel

/-- Theorem 5.4, certificate form. -/
theorem ConsecutiveBlockKernelCertificate.jacobian_posDef
    {p N : ℕ} (C : ConsecutiveBlockKernelCertificate p N) :
    C.jacobian.PosDef := by
  rw [C.jacobian_eq]
  exact autocorrelationKernel_posDef (by simp [C.kernel_zero])

end

end FurtherToeplitzPositroids
