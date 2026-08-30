import FurtherToeplitzPositroids.QuantumBinomial
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Centered root-of-unity alphabets

This module formalizes the elementary alphabet facts in equations (17)--(18):
the centered roots are invariant under inversion and have product one.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators ComplexConjugate

noncomputable section

/-- The centered integral exponent `2a-count+1`, with zero-based `a`. -/
def centeredAlphabetExponent (count : ℕ) (a : Fin count) : ℤ :=
  2 * (a.val : ℤ) - (count : ℤ) + 1

/-- A centered unit-circle alphabet of prescribed size and angle. -/
def centeredAlphabetRoot (count : ℕ) (theta : ℝ) (a : Fin count) : ℂ :=
  Complex.exp (Complex.I * (centeredAlphabetExponent count a : ℂ) * (theta : ℂ))

/-- Common ratio of the centered geometric alphabet. -/
def centeredAlphabetRatio (theta : ℝ) : ℂ :=
  Complex.exp (Complex.I * 2 * (theta : ℂ))

/-- Initial scale of the centered geometric alphabet. -/
def centeredAlphabetScale (count : ℕ) (theta : ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((1 : ℤ) - count : ℂ) * (theta : ℂ))

/-- The centered roots form an explicit geometric progression. -/
theorem centeredAlphabetRoot_eq_scale_mul_ratio_pow
    (count : ℕ) (theta : ℝ) (a : Fin count) :
    centeredAlphabetRoot count theta a =
      centeredAlphabetScale count theta * centeredAlphabetRatio theta ^ a.val := by
  unfold centeredAlphabetRoot centeredAlphabetScale centeredAlphabetRatio
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  unfold centeredAlphabetExponent
  push_cast
  ring

/-- Reversing the alphabet index negates the centered exponent. -/
theorem centeredAlphabetExponent_rev
    (count : ℕ) (a : Fin count) :
    centeredAlphabetExponent count a.rev = -centeredAlphabetExponent count a := by
  unfold centeredAlphabetExponent
  simp only [Fin.val_rev]
  omega

/-- Reversing the alphabet index takes the multiplicative inverse. -/
theorem centeredAlphabetRoot_rev
    (count : ℕ) (theta : ℝ) (a : Fin count) :
    centeredAlphabetRoot count theta a.rev =
      (centeredAlphabetRoot count theta a)⁻¹ := by
  unfold centeredAlphabetRoot
  rw [centeredAlphabetExponent_rev]
  push_cast
  have harg : Complex.I * (-(centeredAlphabetExponent count a : ℂ)) * (theta : ℂ) =
      -(Complex.I * (centeredAlphabetExponent count a : ℂ) * (theta : ℂ)) := by ring
  rw [harg, Complex.exp_neg]

/-- The centered alphabet is invariant under inversion as a finite multiset. -/
theorem centeredAlphabet_inversion_invariant
    (count : ℕ) (theta : ℝ) :
    (Finset.univ.image fun a : Fin count ↦ centeredAlphabetRoot count theta a)
      = Finset.univ.image fun a : Fin count ↦
        (centeredAlphabetRoot count theta a)⁻¹ := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨a.rev, Finset.mem_univ _, ?_⟩
    rw [centeredAlphabetRoot_rev, inv_inv]
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨a.rev, Finset.mem_univ _, ?_⟩
    rw [centeredAlphabetRoot_rev]

/-- The product of every centered alphabet is one. -/
theorem prod_centeredAlphabetRoot
    (count : ℕ) (theta : ℝ) :
    (∏ a : Fin count, centeredAlphabetRoot count theta a) = 1 := by
  let phase : Fin count → ℂ := fun a ↦
    Complex.I * (centeredAlphabetExponent count a : ℂ) * (theta : ℂ)
  have hphaseRev : ∀ a, phase a.rev = -phase a := by
    intro a
    dsimp only [phase]
    rw [centeredAlphabetExponent_rev]
    push_cast
    ring
  have hsumRev := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin count)) phase
  have hsumNeg : (∑ a : Fin count, phase a.rev) = -∑ a : Fin count, phase a := by
    simp_rw [hphaseRev]
    rw [Finset.sum_neg_distrib]
  have hself : (∑ a : Fin count, phase a) = -∑ a : Fin count, phase a := by
    calc
      (∑ a : Fin count, phase a) = ∑ a : Fin count, phase a.rev := hsumRev.symm
      _ = -∑ a : Fin count, phase a := hsumNeg
  have hsumZero : (∑ a : Fin count, phase a) = 0 := by
    let S : ℂ := ∑ a : Fin count, phase a
    have hS : S = -S := hself
    have htwo : (2 : ℂ) * S = 0 := by
      calc
        (2 : ℂ) * S = S + S := by ring
        _ = S + (-S) := congrArg (fun z : ℂ ↦ S + z) hS
        _ = 0 := add_neg_cancel S
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  unfold centeredAlphabetRoot
  change (∏ a : Fin count, Complex.exp (phase a)) = 1
  rw [← Complex.exp_sum, hsumZero, Complex.exp_zero]

/-- The centered `r`-letter alphabet `X` from equation (17). -/
def quantumAlphabetX (r d : ℕ) : Fin r → ℂ :=
  centeredAlphabetRoot r (quantumTheta r d)

/-- The centered `d`-letter alphabet `Y` from equation (18). -/
def quantumAlphabetY (r d : ℕ) : Fin d → ℂ :=
  centeredAlphabetRoot d (quantumTheta r d)

theorem quantumAlphabetX_prod (r d : ℕ) :
    ∏ a, quantumAlphabetX r d a = 1 :=
  prod_centeredAlphabetRoot r (quantumTheta r d)

theorem quantumAlphabetY_prod (r d : ℕ) :
    ∏ a, quantumAlphabetY r d a = 1 :=
  prod_centeredAlphabetRoot d (quantumTheta r d)

/-! ## Finite elementary symmetric specializations -/

/-- The elementary symmetric specialization of degree `t` in a finite
alphabet. -/
def elementarySymmetricSpecialization
    {d : ℕ} (x : Fin d → ℂ) (t : ℕ) : ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard t, ∏ i ∈ S, x i

/-- The concrete finite-subset definition is exactly evaluation of mathlib's
elementary symmetric polynomial. -/
theorem elementarySymmetricSpecialization_eq_aeval_esymm
    {d : ℕ} (x : Fin d → ℂ) (t : ℕ) :
    elementarySymmetricSpecialization x t =
      MvPolynomial.aeval x (MvPolynomial.esymm (Fin d) ℂ t) := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm,
    Finset.esymm_map_val]
  rfl

@[simp]
theorem elementarySymmetricSpecialization_zero
    {d : ℕ} (x : Fin d → ℂ) :
    elementarySymmetricSpecialization x 0 = 1 := by
  simp [elementarySymmetricSpecialization]

@[simp]
theorem elementarySymmetricSpecialization_top
    {d : ℕ} (x : Fin d → ℂ) :
    elementarySymmetricSpecialization x d = ∏ i, x i := by
  unfold elementarySymmetricSpecialization
  rw [show (Finset.univ : Finset (Fin d)).powersetCard d =
      {(Finset.univ : Finset (Fin d))} by
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, hcard⟩
      apply Finset.eq_univ_of_card S
      simpa using hcard
    · rintro rfl
      simp]
  simp

@[simp]
theorem quantumAlphabetY_elementary_zero (r d : ℕ) :
    elementarySymmetricSpecialization (quantumAlphabetY r d) 0 = 1 := by
  simp

@[simp]
theorem quantumAlphabetY_elementary_top (r d : ℕ) :
    elementarySymmetricSpecialization (quantumAlphabetY r d) d = 1 := by
  rw [elementarySymmetricSpecialization_top, quantumAlphabetY_prod]

end

end FurtherToeplitzPositroids
