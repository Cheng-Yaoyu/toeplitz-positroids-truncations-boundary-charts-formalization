import FurtherToeplitzPositroids.FirstCircuitLayer
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive-definite autocorrelation kernels

The Fourier integral in equation (31) is replaced by a finite Gram
factorization.  This proves the same strict positive-definiteness statement
without measure theory.
-/

namespace FurtherToeplitzPositroids

open Matrix

noncomputable section

/-- A causal finite convolution coefficient. -/
def convolutionCoefficient {r : ℕ} (v : Fin (r + 1) → ℝ)
    (u t : ℕ) : ℝ :=
  if _htu : t ≤ u then
    if hur : u - t < r + 1 then v ⟨u - t, hur⟩ else 0
  else 0

/-- The rectangular causal convolution operator associated with `v`. -/
def convolutionMatrix {r : ℕ} (v : Fin (r + 1) → ℝ) (N : ℕ) :
    Matrix (Fin (N + r)) (Fin N) ℝ :=
  fun u t ↦ convolutionCoefficient v u.val t.val

@[simp]
theorem convolutionMatrix_diagonal
    {r N : ℕ} (v : Fin (r + 1) → ℝ) (t : Fin N) :
    convolutionMatrix v N (Fin.castAdd r t) t = v 0 := by
  simp [convolutionMatrix, convolutionCoefficient]

theorem convolutionMatrix_eq_zero_of_row_lt_col
    {r N : ℕ} {v : Fin (r + 1) → ℝ}
    {u : Fin (N + r)} {t : Fin N} (hut : u.val < t.val) :
    convolutionMatrix v N u t = 0 := by
  simp [convolutionMatrix, convolutionCoefficient, not_le_of_gt hut]

/-- A causal convolution matrix is injective when its leading coefficient is
nonzero. -/
theorem convolutionMatrix_mulVec_injective
    {r N : ℕ} {v : Fin (r + 1) → ℝ} (hv0 : v 0 ≠ 0) :
    Function.Injective (convolutionMatrix v N).mulVec := by
  change Function.Injective (convolutionMatrix v N).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  funext t
  have hmain : ∀ q : ℕ, ∀ hq : q < N, x ⟨q, hq⟩ = 0 := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hq
        let tq : Fin N := ⟨q, hq⟩
        have hrow := congrFun hx (Fin.castAdd r tq)
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
        have hsum :
            (∑ s : Fin N, convolutionMatrix v N (Fin.castAdd r tq) s * x s) =
              convolutionMatrix v N (Fin.castAdd r tq) tq * x tq := by
          apply Finset.sum_eq_single tq
          · intro s _ hst
            by_cases hsq : s.val < q
            · rw [ih s.val hsq s.isLt]
              simp
            · have hqs : q < s.val := by
                have hsne : s.val ≠ q := by
                  intro hs
                  apply hst
                  apply Fin.ext
                  exact hs
                omega
              rw [convolutionMatrix_eq_zero_of_row_lt_col hqs, zero_mul]
          · simp
        rw [hsum, convolutionMatrix_diagonal] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left hv0
  simpa using hmain t.val t.isLt

/-- The finite Toeplitz autocorrelation kernel is the Gram matrix of causal
convolution by `v`. -/
def autocorrelationKernel {r : ℕ} (v : Fin (r + 1) → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (convolutionMatrix v N)ᴴ * convolutionMatrix v N

/-- The nonnegative-lag autocorrelation coefficient from equation (29). -/
def autocorrelationCoefficient {r : ℕ} (v : Fin (r + 1) → ℝ)
    (h : ℕ) : ℝ :=
  ∑ i : Fin (r + 1),
    if hi : i.val + h < r + 1 then v ⟨i.val + h, hi⟩ * v i else 0

/-- A finite convolution-column inner product depends only on the lag. -/
theorem sum_range_convolutionCoefficient_mul_of_le
    {r N t s : ℕ} {v : Fin (r + 1) → ℝ}
    (hsN : s < N) (hts : t ≤ s) :
    (∑ u ∈ Finset.range (N + r),
      convolutionCoefficient v u t * convolutionCoefficient v u s) =
      autocorrelationCoefficient v (s - t) := by
  let I := Finset.Icc s (s + r)
  have hI : I ⊆ Finset.range (N + r) := by
    intro u hu
    simp only [I, Finset.mem_Icc, Finset.mem_range] at hu ⊢
    omega
  have hrestrict :
      (∑ u ∈ Finset.range (N + r),
        convolutionCoefficient v u t * convolutionCoefficient v u s) =
        ∑ u ∈ I,
          convolutionCoefficient v u t * convolutionCoefficient v u s := by
    symm
    apply Finset.sum_subset hI
    intro u hu hnot
    simp only [Finset.mem_range] at hu
    by_cases hus : u < s
    · simp [convolutionCoefficient, not_le_of_gt hus]
    · have hsu : s ≤ u := not_lt.mp hus
      have hupper : s + r < u := by
        simp only [I, Finset.mem_Icc, not_and_or, not_le] at hnot
        exact hnot.resolve_left (not_lt_of_ge hsu)
      have hband : ¬u - s < r + 1 := by omega
      simp [convolutionCoefficient, hsu, hband]
  rw [hrestrict]
  have hshift :
      (∑ u ∈ I,
        convolutionCoefficient v u t * convolutionCoefficient v u s) =
        ∑ i ∈ Finset.range (r + 1),
          convolutionCoefficient v (s + i) t *
            convolutionCoefficient v (s + i) s := by
    apply Finset.sum_bij (fun u _ ↦ u - s)
    · intro u hu
      simp only [I, Finset.mem_Icc] at hu
      simp only [Finset.mem_range]
      omega
    · intro u hu w hw huw
      simp only [I, Finset.mem_Icc] at hu hw
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨s + i, ?_, ?_⟩
      · simp [I]
        omega
      · omega
    · intro u hu
      have hsu : s ≤ u := (Finset.mem_Icc.mp hu).1
      rw [show s + (u - s) = u by omega]
  rw [hshift, autocorrelationCoefficient, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have htu : t ≤ s + i := hts.trans (Nat.le_add_right s i)
  have hsu : s ≤ s + i := Nat.le_add_right s i
  have hsubt : s + i - t = (s - t) + i := by omega
  have hsubs : s + i - s = i := by omega
  simp only [convolutionCoefficient, dif_pos htu, dif_pos hsu,
    hsubt, hsubs, Nat.add_comm i (s - t)]
  split_ifs <;> simp

/-- Entrywise Toeplitz autocorrelation formula for weakly ordered indices. -/
theorem autocorrelationKernel_apply_of_le
    {r N : ℕ} {v : Fin (r + 1) → ℝ} {t s : Fin N} (hts : t ≤ s) :
    autocorrelationKernel v N t s =
      autocorrelationCoefficient v (s.val - t.val) := by
  unfold autocorrelationKernel
  rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
  have hsum := sum_range_convolutionCoefficient_mul_of_le
    (v := v) s.isLt (Fin.le_iff_val_le_val.mp hts)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.mem_range] at hu
  simp [convolutionMatrix, Matrix.conjTranspose_apply, star_trivial, hu]

/-- The autocorrelation kernel is the symmetric Toeplitz matrix obtained by
evaluating the lag coefficient at the unsigned distance. -/
theorem autocorrelationKernel_apply
    {r N : ℕ} (v : Fin (r + 1) → ℝ) (t s : Fin N) :
    autocorrelationKernel v N t s =
      autocorrelationCoefficient v (Nat.dist t.val s.val) := by
  rcases le_total t s with hts | hst
  · rw [autocorrelationKernel_apply_of_le hts,
      Nat.dist_eq_sub_of_le (Fin.le_iff_val_le_val.mp hts)]
  · rw [show autocorrelationKernel v N t s =
        autocorrelationKernel v N s t by
        unfold autocorrelationKernel
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
        apply Finset.sum_congr rfl
        intro u _
        ring,
      autocorrelationKernel_apply_of_le hst,
      Nat.dist_eq_sub_of_le_right (Fin.le_iff_val_le_val.mp hst)]

/-- The kernel is symmetric. -/
theorem autocorrelationKernel_isSymm
    {r N : ℕ} (v : Fin (r + 1) → ℝ) :
    (autocorrelationKernel v N).IsSymm := by
  simpa [autocorrelationKernel] using
    Matrix.isHermitian_conjTranspose_mul_self (convolutionMatrix v N)

/-- Theorem 5.4, positive-definite core: an autocorrelation Jacobian with a
nonzero endpoint recurrence coefficient is symmetric positive definite. -/
theorem autocorrelationKernel_posDef
    {r N : ℕ} {v : Fin (r + 1) → ℝ} (hv0 : v 0 ≠ 0) :
    (autocorrelationKernel v N).PosDef := by
  exact Matrix.PosDef.conjTranspose_mul_self (convolutionMatrix v N)
    (convolutionMatrix_mulVec_injective hv0)

/-- The quadratic form is the squared Euclidean norm of the finite
convolution.  This is the finite Gram analogue of equation (31). -/
theorem autocorrelationKernel_quadratic_eq_sum_sq
    {r N : ℕ} (v : Fin (r + 1) → ℝ) (x : Fin N → ℝ) :
    x ⬝ᵥ (autocorrelationKernel v N *ᵥ x) =
      ∑ u : Fin (N + r), ((convolutionMatrix v N *ᵥ x) u) ^ 2 := by
  rw [autocorrelationKernel, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    Matrix.vecMul_conjTranspose]
  simp only [star_trivial]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The quadratic form is strictly positive on nonzero vectors. -/
theorem autocorrelationKernel_quadratic_pos
    {r N : ℕ} {v : Fin (r + 1) → ℝ} (hv0 : v 0 ≠ 0)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (autocorrelationKernel v N *ᵥ x) := by
  exact (autocorrelationKernel_posDef hv0).dotProduct_mulVec_pos hx

end

end FurtherToeplitzPositroids
