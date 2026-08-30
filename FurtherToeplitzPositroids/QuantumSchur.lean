import FurtherToeplitzPositroids.QuantumRankLevel
import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson
import AlgebraicCombinatorics.Partitions.QBinomialFormulas

/-!
# Schur expansions at the quantum alphabet

This module connects the root-of-unity data of Section 5 with the checked
Schur and Littlewood--Richardson infrastructure from Algebraic Combinatorics.
Only declarations whose axiom audit is free of exercise placeholders are
used here.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open AlgebraicCombinatorics MvPolynomial

noncomputable section

/-! ## Gaussian binomial base change -/

/-- The recursive Gaussian binomial commutes with the constant-polynomial
embedding. -/
theorem qBinomial_C (q : ℂ) : ∀ n k : ℕ,
    AlgebraicCombinatorics.QBinomialRec.qBinomial
        (Polynomial.C q) n k =
      Polynomial.C
        (AlgebraicCombinatorics.QBinomialRec.qBinomial q n k) := by
  intro n
  induction n with
  | zero =>
      intro k
      cases k <;>
        simp [AlgebraicCombinatorics.QBinomialRec.qBinomial]
  | succ n ih =>
      intro k
      cases k with
      | zero => simp [AlgebraicCombinatorics.QBinomialRec.qBinomial]
      | succ k =>
          simp only [AlgebraicCombinatorics.QBinomialRec.qBinomial]
          rw [ih k, ih (k + 1), map_add, map_mul, map_pow]

/-- The monotone-tuple and recursive Gaussian-binomial definitions agree. -/
theorem qBinomial_eq_qBinomialRec
    {R : Type*} [CommRing R] (n k : ℕ) (hk : k ≤ n) (q : R) :
    AlgebraicCombinatorics.qBinomial n k q =
      AlgebraicCombinatorics.QBinomialRec.qBinomial q n k := by
  rw [AlgebraicCombinatorics.qBinomial_eq_sum_increasing_tuples n k hk q,
    AlgebraicCombinatorics.QBinomialRec.qBinomial_eq_sum_monotone q n k hk]
  rfl

/-- Evaluation of the complete homogeneous symmetric polynomial in a finite
alphabet. -/
def completeHomogeneousSpecialization
    {count : ℕ} (x : Fin count → ℂ) (t : ℕ) : ℂ :=
  MvPolynomial.aeval x (MvPolynomial.hsymm (Fin count) ℂ t)

/-- Complete homogeneous specialization of a geometric alphabet of size
`ell + 1`. -/
theorem completeHomogeneousSpecialization_geometric_succ
    (ell t : ℕ) (scale ratio : ℂ) :
    completeHomogeneousSpecialization
        (fun a : Fin (ell + 1) ↦ scale * ratio ^ a.val) t =
      scale ^ t * AlgebraicCombinatorics.QBinomialRec.qBinomial
        ratio (ell + t) t := by
  let e := AlgebraicCombinatorics.monotoneFunctionsEquivSym t ell
  have hterm : ∀ u : {f : Fin t → Fin (ell + 1) // Monotone f},
      ((e u).val.map (fun a ↦ scale * ratio ^ a.val)).prod =
        scale ^ t * ratio ^ (∑ i, (u.val i).val) := by
    intro u
    change ((Multiset.ofList (List.ofFn u.val)).map
      (fun a ↦ scale * ratio ^ a.val)).prod = _
    simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      List.prod_ofFn, Function.comp_apply]
    have hsplit : (∏ i : Fin t, scale * ratio ^ (u.val i).val) =
        (∏ _i : Fin t, scale) *
          ∏ i : Fin t, ratio ^ (u.val i).val := by
      exact Finset.prod_mul_distrib
    have hconst : ∏ _i : Fin t, scale = scale ^ t := by simp
    have hpow : ∏ i : Fin t, ratio ^ (u.val i).val =
        ratio ^ (∑ i : Fin t, (u.val i).val) := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i : Fin t ↦ (u.val i).val) ratio
    rw [hsplit, hconst, hpow]
  unfold completeHomogeneousSpecialization MvPolynomial.hsymm
  rw [map_sum]
  have heval : ∀ s : Sym (Fin (ell + 1)) t,
      MvPolynomial.aeval (fun a : Fin (ell + 1) ↦ scale * ratio ^ a.val)
          (s.val.map (fun a ↦
            (MvPolynomial.X a : MvPolynomial (Fin (ell + 1)) ℂ))).prod =
        (s.val.map (fun a ↦ scale * ratio ^ a.val)).prod := by
    intro s
    rw [map_multiset_prod]
    congr 1
    simp
  simp_rw [heval]
  have hreindex :
      (∑ s : Sym (Fin (ell + 1)) t,
        (s.val.map (fun a ↦ scale * ratio ^ a.val)).prod) =
      ∑ u : {f : Fin t → Fin (ell + 1) // Monotone f},
        scale ^ t * ratio ^ (∑ i, (u.val i).val) := by
    symm
    apply Fintype.sum_equiv e
    intro u
    exact (hterm u).symm
  rw [hreindex]
  have hfactor :
      (∑ u : {f : Fin t → Fin (ell + 1) // Monotone f},
        scale ^ t * ratio ^ (∑ i, (u.val i).val)) =
      scale ^ t *
        ∑ u : {f : Fin t → Fin (ell + 1) // Monotone f},
          ratio ^ (∑ i, (u.val i).val) := by
    rw [Finset.mul_sum]
  rw [hfactor]
  congr 1
  rw [← qBinomial_eq_qBinomialRec (ell + t) t (by omega) ratio,
    AlgebraicCombinatorics.qBinomial_eq_sum_increasing_tuples
      (ell + t) t (by omega) ratio]
  have hwidth : ell + t - t = ell := by omega
  rw [hwidth]
  unfold AlgebraicCombinatorics.monotoneFunctions
  rw [← Finset.sum_subtype_eq_sum_filter]
  apply Finset.sum_congr
  · ext u
    simp
  · intro u hu
    rfl

/-- Complete specialization of the centered `X` alphabet in Gaussian
coordinates. -/
theorem quantumAlphabetX_complete_eq_qBinomial
    {r d t : ℕ} (hr : 0 < r) :
    completeHomogeneousSpecialization (quantumAlphabetX r d) t =
      centeredAlphabetScale r (quantumTheta r d) ^ t *
        AlgebraicCombinatorics.QBinomialRec.qBinomial
          (centeredAlphabetRatio (quantumTheta r d)) (r + t - 1) t := by
  obtain ⟨ell, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [show quantumAlphabetX (ell + 1) d =
      fun a ↦ centeredAlphabetScale (ell + 1)
          (quantumTheta (ell + 1) d) *
        centeredAlphabetRatio (quantumTheta (ell + 1) d) ^ a.val by
    funext a
    exact centeredAlphabetRoot_eq_scale_mul_ratio_pow
      (ell + 1) (quantumTheta (ell + 1) d) a]
  simpa [Nat.add_sub_cancel] using
    completeHomogeneousSpecialization_geometric_succ ell t
      (centeredAlphabetScale (ell + 1) (quantumTheta (ell + 1) d))
      (centeredAlphabetRatio (quantumTheta (ell + 1) d))

/-- The scale of the `r`-letter complete specialization supplies exactly
the extra Gaussian phase needed to use the elementary phase-cancellation
identity at top index `r+t-1`. -/
theorem centeredCompleteScale_eq_elementaryScale
    (ell t : ℕ) (theta : ℝ) :
    centeredAlphabetScale (ell + 1) theta ^ t =
      centeredAlphabetScale (ell + t) theta ^ t *
        centeredAlphabetRatio theta ^ (t * (t - 1) / 2) := by
  have heven : Even (t * (t - 1)) := by
    cases t with
    | zero => simp
    | succ t =>
        simpa [mul_comm] using Nat.even_mul_succ_self t
  have htwo : 2 * (t * (t - 1) / 2) = t * (t - 1) :=
    Nat.two_mul_div_two_of_even heven
  unfold centeredAlphabetScale centeredAlphabetRatio
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  have htwoC : (2 : ℂ) * ((t * (t - 1) / 2 : ℕ) : ℂ) =
      ((t * (t - 1) : ℕ) : ℂ) := by exact_mod_cast htwo
  have hpolyC : (t : ℂ) ^ 2 - (t : ℂ) =
      ((t * (t - 1) : ℕ) : ℂ) := by
    cases t with
    | zero => simp
    | succ t =>
        simp only [Nat.succ_sub_one]
        push_cast
        ring
  have hkey : (t : ℂ) ^ 2 - (t : ℂ) +
        ((t * (t - 1) : ℕ) : ℂ) -
        4 * ((t * (t - 1) / 2 : ℕ) : ℂ) = 0 := by
    rw [hpolyC, ← htwoC]
    ring
  have htwoZero : 2 * ((t * (t - 1) / 2 : ℕ) : ℂ) -
      ((t * (t - 1) : ℕ) : ℂ) = 0 := sub_eq_zero.mpr htwoC
  ring_nf at hkey htwoZero ⊢
  linear_combination
    Complex.I * (theta : ℂ) * hkey +
      Complex.I * (theta : ℂ) * htwoZero

/-- Elementary symmetric functions of a finite geometric progression are
the centered Gaussian-binomial coefficients. -/
theorem elementarySymmetricSpecialization_geometric
    (d t : ℕ) (ht : t ≤ d) (scale ratio : ℂ) :
    elementarySymmetricSpecialization
        (fun a : Fin d ↦ scale * ratio ^ a.val) t =
      scale ^ t * ratio ^ (t * (t - 1) / 2) *
        AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d t := by
  let P : Polynomial ℂ :=
    ∏ a : Fin d, (Polynomial.X +
      Polynomial.C (scale * ratio ^ a.val))
  have hcoeff : P.coeff (d - t) =
      elementarySymmetricSpecialization
        (fun a : Fin d ↦ scale * ratio ^ a.val) t := by
    unfold P
    rw [Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin d))
      (fun a : Fin d ↦ scale * ratio ^ a.val) (by simp)]
    have hindex : (Finset.univ : Finset (Fin d)).card - (d - t) = t := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    rw [hindex]
    change (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
      ∏ i ∈ S, scale * ratio ^ i.val) = _
    rfl
  have hq := AlgebraicCombinatorics.QBinomialRec.qBinomial_first_theorem
    (K := Polynomial ℂ) (Polynomial.C scale) Polynomial.X
      (Polynomial.C ratio) d
  have hleft :
      (∏ i ∈ Finset.range d,
        (Polynomial.C scale * Polynomial.C ratio ^ i + Polynomial.X)) = P := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only [P]
    rw [map_mul, map_pow]
    ring
  rw [hleft] at hq
  have hcoeffEq := congrArg (fun Q : Polynomial ℂ ↦ Q.coeff (d - t)) hq
  change P.coeff (d - t) = _ at hcoeffEq
  rw [hcoeff] at hcoeffEq
  dsimp only at hcoeffEq
  let coeffHom : Polynomial ℂ →+ ℂ :=
    { toFun := fun Q ↦ Q.coeff (d - t)
      map_zero' := by simp
      map_add' := by intro Q R; simp }
  have hmap :
      (∑ k ∈ Finset.range (d + 1),
        (Polynomial.C ratio) ^ (k * (k - 1) / 2) *
          AlgebraicCombinatorics.QBinomialRec.qBinomial
            (Polynomial.C ratio) d k *
          (Polynomial.C scale) ^ k * Polynomial.X ^ (d - k)).coeff (d - t) =
      ∑ k ∈ Finset.range (d + 1),
        ((Polynomial.C ratio) ^ (k * (k - 1) / 2) *
          AlgebraicCombinatorics.QBinomialRec.qBinomial
            (Polynomial.C ratio) d k *
          (Polynomial.C scale) ^ k * Polynomial.X ^ (d - k)).coeff (d - t) := by
    change coeffHom (∑ k ∈ Finset.range (d + 1),
        (Polynomial.C ratio) ^ (k * (k - 1) / 2) *
          AlgebraicCombinatorics.QBinomialRec.qBinomial
            (Polynomial.C ratio) d k *
          (Polynomial.C scale) ^ k * Polynomial.X ^ (d - k)) =
      ∑ k ∈ Finset.range (d + 1), coeffHom
        ((Polynomial.C ratio) ^ (k * (k - 1) / 2) *
          AlgebraicCombinatorics.QBinomialRec.qBinomial
            (Polynomial.C ratio) d k *
          (Polynomial.C scale) ^ k * Polynomial.X ^ (d - k))
    exact map_sum coeffHom _ _
  rw [hmap] at hcoeffEq
  have hsingle :
      (∑ k ∈ Finset.range (d + 1),
        ((Polynomial.C ratio) ^ (k * (k - 1) / 2) *
          AlgebraicCombinatorics.QBinomialRec.qBinomial
            (Polynomial.C ratio) d k *
          (Polynomial.C scale) ^ k * Polynomial.X ^ (d - k)).coeff (d - t)) =
      scale ^ t * ratio ^ (t * (t - 1) / 2) *
        AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d t := by
    rw [Finset.sum_eq_single t]
    · rw [qBinomial_C]
      have hconst :
          (Polynomial.C ratio) ^ (t * (t - 1) / 2) *
              Polynomial.C
                (AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d t) *
              (Polynomial.C scale) ^ t =
            Polynomial.C (ratio ^ (t * (t - 1) / 2) *
              AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d t *
              scale ^ t) := by
        rw [← map_pow (Polynomial.C : ℂ →+* Polynomial ℂ),
          ← map_pow (Polynomial.C : ℂ →+* Polynomial ℂ),
          ← map_mul, ← map_mul]
      rw [hconst, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
      ring
    · intro k hk hkt
      have hkBound : k ≤ d := by
        simp only [Finset.mem_range] at hk
        omega
      have hdegree : d - k ≠ d - t := by omega
      rw [qBinomial_C]
      have hconst :
          (Polynomial.C ratio) ^ (k * (k - 1) / 2) *
              Polynomial.C
                (AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d k) *
              (Polynomial.C scale) ^ k =
            Polynomial.C (ratio ^ (k * (k - 1) / 2) *
              AlgebraicCombinatorics.QBinomialRec.qBinomial ratio d k *
              scale ^ k) := by
        rw [← map_pow (Polynomial.C : ℂ →+* Polynomial ℂ),
          ← map_pow (Polynomial.C : ℂ →+* Polynomial ℂ),
          ← map_mul, ← map_mul]
      rw [hconst, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hdegree.symm]
    · intro htbad
      exact (htbad (Finset.mem_range.mpr (by omega))).elim
  exact hcoeffEq.trans hsingle

/-- The centered alphabet specialization in Gaussian-binomial form. -/
theorem elementarySymmetricSpecialization_centeredAlphabetRoot
    (count t : ℕ) (ht : t ≤ count) (theta : ℝ) :
    elementarySymmetricSpecialization
        (centeredAlphabetRoot count theta) t =
      centeredAlphabetScale count theta ^ t *
        centeredAlphabetRatio theta ^ (t * (t - 1) / 2) *
        AlgebraicCombinatorics.QBinomialRec.qBinomial
          (centeredAlphabetRatio theta) count t := by
  have hgeom := elementarySymmetricSpecialization_geometric count t ht
    (centeredAlphabetScale count theta) (centeredAlphabetRatio theta)
  rw [show centeredAlphabetRoot count theta =
      fun a ↦ centeredAlphabetScale count theta *
        centeredAlphabetRatio theta ^ a.val by
    funext a
    exact centeredAlphabetRoot_eq_scale_mul_ratio_pow count theta a]
  exact hgeom

/-- The `Y` alphabet in equation (18), in checked centered
Gaussian-binomial coordinates. -/
theorem quantumAlphabetY_elementary_eq_qBinomial
    {r d t : ℕ} (ht : t ≤ d) :
    elementarySymmetricSpecialization (quantumAlphabetY r d) t =
      centeredAlphabetScale d (quantumTheta r d) ^ t *
        centeredAlphabetRatio (quantumTheta r d) ^ (t * (t - 1) / 2) *
        AlgebraicCombinatorics.QBinomialRec.qBinomial
          (centeredAlphabetRatio (quantumTheta r d)) d t := by
  exact elementarySymmetricSpecialization_centeredAlphabetRoot
    d t ht (quantumTheta r d)

/-- Elementary exponential-to-sine factorization used to evaluate quantum
integers on the unit circle. -/
theorem one_sub_exp_two_mul_I (x : ℝ) :
    1 - Complex.exp (Complex.I * 2 * (x : ℂ)) =
      -2 * Complex.I * Complex.exp (Complex.I * (x : ℂ)) *
        (Real.sin x : ℂ) := by
  have hsin := Complex.two_sin (x : ℂ)
  rw [← Complex.ofReal_sin] at hsin
  have hexp : Complex.exp (Complex.I * 2 * (x : ℂ)) =
      Complex.exp (Complex.I * (x : ℂ)) *
        Complex.exp (Complex.I * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hone : Complex.exp (Complex.I * (x : ℂ)) *
      Complex.exp (-(x : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp [mul_comm]
  have hdiff : Complex.exp (-(x : ℂ) * Complex.I) -
        Complex.exp ((x : ℂ) * Complex.I) =
      -2 * Complex.I * (Real.sin x : ℂ) := by
    calc
      Complex.exp (-(x : ℂ) * Complex.I) -
          Complex.exp ((x : ℂ) * Complex.I) =
          ((Complex.exp (-(x : ℂ) * Complex.I) -
            Complex.exp ((x : ℂ) * Complex.I)) * Complex.I) *
              (-Complex.I) := by
            symm
            calc
              ((Complex.exp (-(x : ℂ) * Complex.I) -
                  Complex.exp ((x : ℂ) * Complex.I)) * Complex.I) *
                    (-Complex.I) =
                  -(Complex.exp (-(x : ℂ) * Complex.I) -
                    Complex.exp ((x : ℂ) * Complex.I)) *
                      (Complex.I * Complex.I) := by ring
              _ = -(Complex.exp (-(x : ℂ) * Complex.I) -
                    Complex.exp ((x : ℂ) * Complex.I)) * (-1) := by
                  rw [Complex.I_mul_I]
              _ = Complex.exp (-(x : ℂ) * Complex.I) -
                    Complex.exp ((x : ℂ) * Complex.I) := by ring
      _ = (2 * (Real.sin x : ℂ)) * (-Complex.I) := by rw [← hsin]
      _ = -2 * Complex.I * (Real.sin x : ℂ) := by ring
  rw [hexp]
  calc
    1 - Complex.exp (Complex.I * (x : ℂ)) *
          Complex.exp (Complex.I * (x : ℂ)) =
        Complex.exp (Complex.I * (x : ℂ)) *
          (Complex.exp (-(x : ℂ) * Complex.I) -
            Complex.exp ((x : ℂ) * Complex.I)) := by
      rw [mul_sub, hone]
      ring
    _ = -2 * Complex.I * Complex.exp (Complex.I * (x : ℂ)) *
          (Real.sin x : ℂ) := by
      rw [hdiff]
      ring

/-- A quantum integer at `exp(2 i theta)` is a phase times the usual sine
quotient. -/
theorem quantum_qNat_eq_sine
    {r d n : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hn : 0 < n) :
    AlgebraicCombinatorics.QBinomialRec.qNat
        (centeredAlphabetRatio (quantumTheta r d)) n =
      Complex.exp (Complex.I * ((n - 1 : ℕ) : ℂ) *
          (quantumTheta r d : ℂ)) *
        ((Real.sin (n * quantumTheta r d) : ℂ) /
          Real.sin (quantumTheta r d)) := by
  let theta := quantumTheta r d
  let q := centeredAlphabetRatio theta
  have hsinTheta : 0 < Real.sin theta := by
    simpa [theta] using quantum_sin_pos_of_index hr hd
      (u := 1) (by omega) (by omega)
  have hq : q ≠ 1 := by
    intro hqOne
    have hfactor := one_sub_exp_two_mul_I theta
    change 1 - q = _ at hfactor
    rw [hqOne, sub_self] at hfactor
    have hnonzero :
        -2 * Complex.I * Complex.exp (Complex.I * (theta : ℂ)) *
          (Real.sin theta : ℂ) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
          (Complex.exp_ne_zero _))
        (by exact_mod_cast hsinTheta.ne')
    exact hnonzero hfactor.symm
  rw [AlgebraicCombinatorics.QBinomialRec.qNat_eq_geom_sum q n hq]
  have hqpow : q ^ n =
      Complex.exp (Complex.I * 2 * ((n : ℕ) : ℂ) * (theta : ℂ)) := by
    unfold q centeredAlphabetRatio
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hnum := one_sub_exp_two_mul_I (n * theta)
  have hden := one_sub_exp_two_mul_I theta
  have hnumArg : Complex.I * 2 * ((n : ℕ) : ℂ) * (theta : ℂ) =
      Complex.I * 2 * ((n : ℝ) * theta : ℂ) := by
    push_cast
    ring
  have hphase : Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (theta : ℂ)) =
      Complex.exp (Complex.I * ((n - 1 : ℕ) : ℂ) * (theta : ℂ)) *
        Complex.exp (Complex.I * (theta : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    have hnCast : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
    rw [← hnCast]
    ring
  have hnum' :
      1 - Complex.exp (Complex.I * 2 * ((n : ℂ) * (theta : ℂ))) =
        -2 * Complex.I *
          Complex.exp (Complex.I * ((n : ℂ) * (theta : ℂ))) *
            (Real.sin (n * theta) : ℂ) := by
    have hcast : (((n : ℝ) * theta : ℝ) : ℂ) =
        (n : ℂ) * (theta : ℂ) := by norm_cast
    rw [hcast] at hnum
    exact hnum
  have hphase' :
      Complex.exp (Complex.I * ((n : ℂ) * (theta : ℂ))) =
        Complex.exp (Complex.I * ((n - 1 : ℕ) : ℂ) * (theta : ℂ)) *
          Complex.exp (Complex.I * (theta : ℂ)) := by
    simpa only [mul_assoc] using hphase
  rw [hqpow, hnumArg]
  dsimp only [q, centeredAlphabetRatio]
  change
    (1 - Complex.exp (Complex.I * 2 * ((n : ℂ) * (theta : ℂ)))) /
        (1 - Complex.exp (Complex.I * 2 * (theta : ℂ))) =
      Complex.exp (Complex.I * ((n - 1 : ℕ) : ℂ) * (theta : ℂ)) *
        ((Real.sin (n * theta) : ℂ) / Real.sin theta)
  rw [hnum', hden]
  rw [hphase']
  field_simp [Complex.I_ne_zero, Complex.exp_ne_zero _, hsinTheta.ne']

/-- The quantum integers below the root-of-unity order are nonzero. -/
theorem quantum_qNat_ne_zero
    {r d n : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hn : 0 < n) (hnN : n < d + r) :
    AlgebraicCombinatorics.QBinomialRec.qNat
      (centeredAlphabetRatio (quantumTheta r d)) n ≠ 0 := by
  rw [quantum_qNat_eq_sine hr hd hn]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply div_ne_zero
  · exact_mod_cast (quantum_sin_pos_of_index hr hd hn hnN).ne'
  · exact_mod_cast (by
      simpa using (quantum_sin_pos_of_index hr hd
        (u := 1) (by omega) (by omega)).ne')

/-- The quantum integer at the root-of-unity order vanishes. -/
theorem quantum_qNat_order_eq_zero
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    AlgebraicCombinatorics.QBinomialRec.qNat
      (centeredAlphabetRatio (quantumTheta r d)) (d + r) = 0 := by
  rw [quantum_qNat_eq_sine hr hd (by omega)]
  have harg : (d + r : ℕ) * quantumTheta r d = Real.pi := by
    rw [quantumTheta]
    have hne : ((d + r : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [harg, Real.sin_pi]
  simp

/-- The Gaussian coefficient underlying `h_{d+s}(X)` vanishes for the
`r-1` indices immediately beyond the band. -/
theorem quantum_complete_qBinomial_zero_above
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hs : 1 ≤ s) (hsr : s < r) :
    AlgebraicCombinatorics.QBinomialRec.qBinomial
      (centeredAlphabetRatio (quantumTheta r d))
        (r + (d + s) - 1) (d + s) = 0 := by
  let q := centeredAlphabetRatio (quantumTheta r d)
  rw [AlgebraicCombinatorics.QBinomialRec.qBinomial_eq_prod_div
    q (r + (d + s) - 1) (d + s) (by omega)]
  · refine Finset.prod_eq_zero (i := s - 1)
      (Finset.mem_range.mpr (by omega)) ?_
    have hindex : r + (d + s) - 1 - (s - 1) = d + r := by
      omega
    rw [hindex, quantum_qNat_order_eq_zero hr hd, zero_div]
  · intro i hi
    exact quantum_qNat_ne_zero hr hd (by omega) (by omega)

/-- Equation (20): `h_{d+s}(X)=0` for `1 ≤ s < r`. -/
theorem quantumAlphabetX_complete_zero_above
    {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hs : 1 ≤ s) (hsr : s < r) :
    completeHomogeneousSpecialization (quantumAlphabetX r d) (d + s) = 0 := by
  rw [quantumAlphabetX_complete_eq_qBinomial hr,
    quantum_complete_qBinomial_zero_above hr hd hs hsr, mul_zero]

/-- One factor in the Gaussian product separates into a phase quotient and
a positive sine quotient. -/
theorem quantum_qNat_ratio_eq
    {r d t i : ℕ} (hr : 0 < r) (hd : 0 < d)
    (ht : t ≤ d) (hi : i < t) :
    AlgebraicCombinatorics.QBinomialRec.qNat
          (centeredAlphabetRatio (quantumTheta r d)) (d - i) /
        AlgebraicCombinatorics.QBinomialRec.qNat
          (centeredAlphabetRatio (quantumTheta r d)) (i + 1) =
      (Complex.exp (Complex.I * ((d - i - 1 : ℕ) : ℂ) *
          (quantumTheta r d : ℂ)) /
        Complex.exp (Complex.I * (i : ℂ) *
          (quantumTheta r d : ℂ))) *
      ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
        Real.sin ((i + 1) * quantumTheta r d)) := by
  have hdi : 0 < d - i := by omega
  have hdiN : d - i < d + r := by omega
  have hip : 0 < i + 1 := by omega
  have hipN : i + 1 < d + r := by omega
  rw [quantum_qNat_eq_sine hr hd hdi,
    quantum_qNat_eq_sine hr hd hip]
  have htheta : (Real.sin (quantumTheta r d) : ℂ) ≠ 0 := by
    exact_mod_cast (by
      simpa using (quantum_sin_pos_of_index hr hd
        (u := 1) (by omega) (by omega)).ne')
  have hsin : (Real.sin ((i + 1) * quantumTheta r d) : ℂ) ≠ 0 := by
    exact_mod_cast (quantum_sin_pos_of_index hr hd hip hipN).ne'
  have hexp : Complex.exp (Complex.I * (i : ℂ) *
      (quantumTheta r d : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hnumArg : ((d - i : ℕ) : ℝ) * quantumTheta r d =
      quantumTheta r d * (d : ℝ) - quantumTheta r d * (i : ℝ) := by
    rw [Nat.cast_sub (by omega : i ≤ d)]
    ring
  have hsinNum := congrArg Real.sin hnumArg
  simp only [Nat.add_sub_cancel]
  field_simp [htheta, hsin, hexp]
  rw [hsinNum]
  congr 2 <;> congr 1 <;> push_cast <;> ring_nf

/-- Product form of the centered Gaussian binomial after separating every
factor into its phase and sine quotient. -/
theorem quantum_qBinomial_eq_phase_sineProduct
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    AlgebraicCombinatorics.QBinomialRec.qBinomial
        (centeredAlphabetRatio (quantumTheta r d)) d t =
      ∏ i ∈ Finset.range t,
        ((Complex.exp (Complex.I * ((d - i - 1 : ℕ) : ℂ) *
              (quantumTheta r d : ℂ)) /
            Complex.exp (Complex.I * (i : ℂ) *
              (quantumTheta r d : ℂ))) *
          ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
            Real.sin ((i + 1) * quantumTheta r d))) := by
  rw [AlgebraicCombinatorics.QBinomialRec.qBinomial_eq_prod_div
    (centeredAlphabetRatio (quantumTheta r d)) d t ht]
  · apply Finset.prod_congr rfl
    intro i hi
    exact quantum_qNat_ratio_eq hr hd ht (Finset.mem_range.mp hi)
  · intro i hi
    exact quantum_qNat_ne_zero hr hd (by omega) (by omega)

/-- The centering phase cancels the total phase in the Gaussian product. -/
theorem centeredGaussianPhase_eq_one
    {d t : ℕ} (hd : 0 < d) (ht : t ≤ d) (theta : ℝ) :
    centeredAlphabetScale d theta ^ t *
        centeredAlphabetRatio theta ^ (t * (t - 1) / 2) *
        (∏ i ∈ Finset.range t,
          Complex.exp (Complex.I * ((d - i - 1 : ℕ) : ℂ) * (theta : ℂ)) /
            Complex.exp (Complex.I * (i : ℂ) * (theta : ℂ))) = 1 := by
  let sumA : ℕ := Finset.sum (Finset.range t) fun i ↦ d - i - 1
  let sumI : ℕ := Finset.sum (Finset.range t) fun i ↦ i
  have hsum : sumA + sumI = t * (d - 1) := by
    dsimp only [sumA, sumI]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i ∈ Finset.range t, (d - i - 1 + i) =
          ∑ _i ∈ Finset.range t, (d - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hit : i < t := Finset.mem_range.mp hi
        omega
      _ = t * (d - 1) := by simp
  have htri : t * (t - 1) / 2 = sumI := by
    dsimp only [sumI]
    exact (Finset.sum_range_id t).symm
  have hsumAExp :
      (∑ i ∈ Finset.range t,
        Complex.I * ((d - i - 1 : ℕ) : ℂ) * (theta : ℂ)) =
      Complex.I * (sumA : ℂ) * (theta : ℂ) := by
    dsimp only [sumA]
    calc
      ∑ i ∈ Finset.range t,
          Complex.I * ((d - i - 1 : ℕ) : ℂ) * (theta : ℂ) =
          (∑ i ∈ Finset.range t,
            Complex.I * ((d - i - 1 : ℕ) : ℂ)) * (theta : ℂ) := by
              rw [Finset.sum_mul]
      _ = Complex.I *
            (∑ i ∈ Finset.range t, ((d - i - 1 : ℕ) : ℂ)) *
              (theta : ℂ) := by rw [Finset.mul_sum]
      _ = Complex.I *
            (↑(Finset.sum (Finset.range t) fun i ↦ d - i - 1) : ℂ) *
              (theta : ℂ) := by push_cast; rfl
  have hsumIExp :
      (∑ i ∈ Finset.range t,
        Complex.I * (i : ℂ) * (theta : ℂ)) =
      Complex.I * (sumI : ℂ) * (theta : ℂ) := by
    dsimp only [sumI]
    calc
      ∑ i ∈ Finset.range t, Complex.I * (i : ℂ) * (theta : ℂ) =
          (∑ i ∈ Finset.range t, Complex.I * (i : ℂ)) *
            (theta : ℂ) := by rw [Finset.sum_mul]
      _ = Complex.I * (∑ i ∈ Finset.range t, (i : ℂ)) *
            (theta : ℂ) := by rw [Finset.mul_sum]
      _ = Complex.I *
            (↑(Finset.sum (Finset.range t) fun i ↦ i) : ℂ) *
            (theta : ℂ) := by push_cast; rfl
  unfold centeredAlphabetScale centeredAlphabetRatio
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    Finset.prod_div_distrib, ← Complex.exp_sum, ← Complex.exp_sum,
    hsumAExp, hsumIExp, ← Complex.exp_sub, ← Complex.exp_add,
    ← Complex.exp_add]
  rw [show
      (t : ℂ) * (Complex.I * ((1 : ℤ) - d : ℂ) * (theta : ℂ)) +
          (t * (t - 1) / 2 : ℕ) * (Complex.I * 2 * (theta : ℂ)) +
          (Complex.I * (sumA : ℂ) * (theta : ℂ) -
            Complex.I * (sumI : ℂ) * (theta : ℂ)) = 0 by
    have hsumC : (sumA : ℂ) + (sumI : ℂ) =
        (t : ℂ) * ((d - 1 : ℕ) : ℂ) := by
      exact_mod_cast hsum
    have htriC : ((t * (t - 1) / 2 : ℕ) : ℂ) = (sumI : ℂ) := by
      exact_mod_cast htri
    rw [htriC]
    rw [Nat.cast_sub (by omega : 1 ≤ d)] at hsumC
    push_cast at hsumC ⊢
    linear_combination Complex.I * (theta : ℂ) * hsumC]
  exact Complex.exp_zero

/-- The elementary specialization of `Y` is the positive sine quotient from
the finite Gaussian product. -/
theorem quantumAlphabetY_elementary_eq_sineProduct
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    elementarySymmetricSpecialization (quantumAlphabetY r d) t =
      ∏ i ∈ Finset.range t,
        ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
          Real.sin ((i + 1) * quantumTheta r d)) := by
  rw [quantumAlphabetY_elementary_eq_qBinomial ht,
    quantum_qBinomial_eq_phase_sineProduct hr hd ht,
    Finset.prod_mul_distrib]
  let phaseProduct : ℂ :=
    ∏ i ∈ Finset.range t,
      Complex.exp (Complex.I * ((d - i - 1 : ℕ) : ℂ) *
          (quantumTheta r d : ℂ)) /
        Complex.exp (Complex.I * (i : ℂ) *
          (quantumTheta r d : ℂ))
  have hphase : centeredAlphabetScale d (quantumTheta r d) ^ t *
        centeredAlphabetRatio (quantumTheta r d) ^ (t * (t - 1) / 2) *
        phaseProduct = 1 := by
    exact centeredGaussianPhase_eq_one hd ht (quantumTheta r d)
  change centeredAlphabetScale d (quantumTheta r d) ^ t *
      centeredAlphabetRatio (quantumTheta r d) ^ (t * (t - 1) / 2) *
      (phaseProduct * _) = _
  calc
    centeredAlphabetScale d (quantumTheta r d) ^ t *
        centeredAlphabetRatio (quantumTheta r d) ^ (t * (t - 1) / 2) *
        (phaseProduct *
          ∏ i ∈ Finset.range t,
            ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
              Real.sin ((i + 1) * quantumTheta r d))) =
      (centeredAlphabetScale d (quantumTheta r d) ^ t *
        centeredAlphabetRatio (quantumTheta r d) ^ (t * (t - 1) / 2) *
        phaseProduct) *
          ∏ i ∈ Finset.range t,
            ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
              Real.sin ((i + 1) * quantumTheta r d)) := by ring
    _ = _ := by rw [hphase, one_mul]

/-- Complete specialization of `X` as its rank-side sine quotient. -/
theorem quantumAlphabetX_complete_eq_sineProduct
    {r d t : ℕ} (hr : 0 < r) (_hd : 0 < d) (ht : t ≤ d) :
    completeHomogeneousSpecialization (quantumAlphabetX r d) t =
      ∏ i ∈ Finset.range t,
        ((Real.sin ((((r + t - 1 : ℕ) : ℝ) - (i : ℝ)) *
            quantumTheta r d) : ℂ) /
          Real.sin (((i + 1 : ℕ) : ℝ) * quantumTheta r d)) := by
  by_cases htZero : t = 0
  · subst t
    simp [completeHomogeneousSpecialization]
  obtain ⟨ell, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [quantumAlphabetX_complete_eq_qBinomial (r := ell + 1) (d := d) (t := t)
    (by omega)]
  rw [centeredCompleteScale_eq_elementaryScale ell t
    (quantumTheta (ell + 1) d)]
  let r' := d - t + 1
  let d' := ell + t
  have hr' : 0 < r' := by dsimp only [r']; omega
  have hd' : 0 < d' := by dsimp only [d']; omega
  have ht' : t ≤ d' := by dsimp only [d']; omega
  have htheta : quantumTheta r' d' = quantumTheta (ell + 1) d := by
    have hsum : d' + r' = d + (ell + 1) := by
      dsimp only [r', d']
      omega
    unfold quantumTheta
    congr 1
    exact_mod_cast hsum
  have hfakeQ := quantumAlphabetY_elementary_eq_qBinomial
    (r := r') (d := d') ht'
  have hfakeS := quantumAlphabetY_elementary_eq_sineProduct hr' hd' ht'
  rw [hfakeS, htheta] at hfakeQ
  have hn : ell + 1 + t - 1 = ell + t := by omega
  rw [hn]
  dsimp only [d'] at hfakeQ
  rw [← hfakeQ]
  apply Finset.prod_congr rfl
  intro i hi
  have hit : i < t := Finset.mem_range.mp hi
  congr 2
  · congr 1
    dsimp only [d']
    push_cast
    ring

/-! ## Rank--level sine-product comparison -/

/-- Factorial product of the positive sine indices `1, ..., n`. -/
def quantumSineFactorial (r d n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, Real.sin ((i + 1) * quantumTheta r d)

/-- The sine factorial is nonzero below the root-of-unity order. -/
theorem quantumSineFactorial_ne_zero
    {r d n : ℕ} (hr : 0 < r) (hd : 0 < d) (hn : n < d + r) :
    quantumSineFactorial r d n ≠ 0 := by
  unfold quantumSineFactorial
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hiN : i + 1 < d + r := by
    have hit := Finset.mem_range.mp hi
    omega
  simpa only [Nat.cast_add, Nat.cast_one] using
    (quantum_sin_pos_of_index hr hd (by omega) hiN).ne'

/-- Complementary sine indices agree because `(d-i)+(r+i)=d+r`. -/
theorem quantum_sin_d_sub_eq_r_add
    {r d i : ℕ} (hr : 0 < r) (hd : 0 < d) (hi : i < d) :
    Real.sin ((d - i) * quantumTheta r d) =
      Real.sin ((r + i) * quantumTheta r d) := by
  have hN : ((d : ℝ) + r) * quantumTheta r d = Real.pi := by
    rw [quantumTheta]
    field_simp
  have harg : ((d - i : ℕ) : ℝ) * quantumTheta r d =
      Real.pi - ((r + i : ℕ) : ℝ) * quantumTheta r d := by
    rw [← hN]
    rw [Nat.cast_sub (by omega : i ≤ d)]
    push_cast
    ring
  have harg' : ((d : ℝ) - (i : ℝ)) * quantumTheta r d =
      Real.pi - ((r : ℝ) + (i : ℝ)) * quantumTheta r d := by
    simpa only [Nat.cast_sub (by omega : i ≤ d), Nat.cast_add] using harg
  rw [harg', Real.sin_pi_sub]

/-- The first sine quotient in the rank--level calculation can be written
with the factorial product. -/
theorem quantum_sineProduct_d_eq_factorial
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    (∏ i ∈ Finset.range t,
        Real.sin ((d - i) * quantumTheta r d) /
          Real.sin ((i + 1) * quantumTheta r d)) =
      quantumSineFactorial r d (r - 1 + t) /
        (quantumSineFactorial r d (r - 1) *
          quantumSineFactorial r d t) := by
  rw [Finset.prod_div_distrib]
  have hnum :
      (∏ i ∈ Finset.range t,
        Real.sin ((d - i) * quantumTheta r d)) =
      ∏ i ∈ Finset.range t,
        Real.sin ((r + i) * quantumTheta r d) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact quantum_sin_d_sub_eq_r_add hr hd (by
      have hit := Finset.mem_range.mp hi
      omega)
  rw [hnum]
  have hsplit := Finset.prod_range_add
    (fun i ↦ Real.sin ((i + 1) * quantumTheta r d)) (r - 1) t
  have hfactor : quantumSineFactorial r d (r - 1 + t) =
      quantumSineFactorial r d (r - 1) *
        ∏ i ∈ Finset.range t,
          Real.sin ((r + i) * quantumTheta r d) := by
    unfold quantumSineFactorial
    rw [hsplit]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    ring
  have hleftNonzero : quantumSineFactorial r d (r - 1) ≠ 0 :=
    quantumSineFactorial_ne_zero hr hd (by omega)
  have hden :
      (∏ i ∈ Finset.range t,
        Real.sin ((i + 1) * quantumTheta r d)) =
      quantumSineFactorial r d t := by
    unfold quantumSineFactorial
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
  have htNonzero : quantumSineFactorial r d t ≠ 0 :=
    quantumSineFactorial_ne_zero hr hd (by omega)
  rw [hden, hfactor]
  field_simp [hleftNonzero, htNonzero]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

/-- The coefficient product (15) has the same factorial quotient. -/
theorem quantumBinomialCoefficient_eq_factorial
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    quantumBinomialCoefficient r d t =
      quantumSineFactorial r d (t + (r - 1)) /
        (quantumSineFactorial r d t *
          quantumSineFactorial r d (r - 1)) := by
  unfold quantumBinomialCoefficient
  rw [Finset.prod_div_distrib]
  have hsplit := Finset.prod_range_add
    (fun i ↦ Real.sin ((i + 1) * quantumTheta r d)) t (r - 1)
  have hnum :
      (∏ l : Fin (r - 1),
        Real.sin ((t + l.val + 1 : ℕ) * quantumTheta r d)) =
      quantumSineFactorial r d (t + (r - 1)) /
        quantumSineFactorial r d t := by
    have hfactor : quantumSineFactorial r d (t + (r - 1)) =
        quantumSineFactorial r d t *
          ∏ i ∈ Finset.range (r - 1),
            Real.sin ((t + i + 1) * quantumTheta r d) := by
      simpa [quantumSineFactorial, add_assoc] using hsplit
    have htNonzero : quantumSineFactorial r d t ≠ 0 :=
      quantumSineFactorial_ne_zero hr hd (by omega)
    rw [hfactor]
    field_simp [htNonzero]
    calc
      (∏ l : Fin (r - 1),
          Real.sin ((t + l.val + 1 : ℕ) * quantumTheta r d)) =
          ∏ i ∈ Finset.range (r - 1),
            Real.sin ((t + i + 1 : ℕ) * quantumTheta r d) := by
        exact Fin.prod_univ_eq_prod_range
          (fun i ↦ Real.sin ((t + i + 1 : ℕ) * quantumTheta r d)) (r - 1)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 1
        push_cast
        ring
  rw [hnum]
  have hden :
      (∏ l : Fin (r - 1),
        Real.sin ((l.val + 1 : ℕ) * quantumTheta r d)) =
      quantumSineFactorial r d (r - 1) := by
    unfold quantumSineFactorial
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Fin.prod_univ_eq_prod_range
        (fun i ↦ Real.sin ((i + 1 : ℕ) * quantumTheta r d)) (r - 1))
  rw [hden]
  have htNonzero : quantumSineFactorial r d t ≠ 0 :=
    quantumSineFactorial_ne_zero hr hd (by omega)
  have hleftNonzero : quantumSineFactorial r d (r - 1) ≠ 0 :=
    quantumSineFactorial_ne_zero hr hd (by omega)
  field_simp [htNonzero, hleftNonzero]

/-- The two sine products in the rank--level calculation are equal. -/
theorem quantum_sineProduct_d_eq_quantumBinomialCoefficient
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    (∏ i ∈ Finset.range t,
        Real.sin ((d - i) * quantumTheta r d) /
          Real.sin ((i + 1) * quantumTheta r d)) =
      quantumBinomialCoefficient r d t := by
  rw [quantum_sineProduct_d_eq_factorial hr hd ht,
    quantumBinomialCoefficient_eq_factorial hr hd ht]
  rw [Nat.add_comm (r - 1) t, mul_comm]

/-- The reflected rank-side sine quotient is the same coefficient (15). -/
theorem quantum_sineProduct_complete_eq_quantumBinomialCoefficient
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    (∏ i ∈ Finset.range t,
        Real.sin ((((r + t - 1 : ℕ) : ℝ) - (i : ℝ)) *
            quantumTheta r d) /
          Real.sin (((i + 1 : ℕ) : ℝ) * quantumTheta r d)) =
      quantumBinomialCoefficient r d t := by
  rw [Finset.prod_div_distrib]
  have hreflect := Finset.prod_range_reflect
    (fun j ↦ Real.sin ((r + j) * quantumTheta r d)) t
  have hnum :
      (∏ i ∈ Finset.range t,
        Real.sin ((((r + t - 1 : ℕ) : ℝ) - (i : ℝ)) *
          quantumTheta r d)) =
      ∏ i ∈ Finset.range t,
        Real.sin ((r + i) * quantumTheta r d) := by
    rw [← hreflect]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    have hit : i < t := Finset.mem_range.mp hi
    rw [Nat.cast_sub (by omega : i ≤ t - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ r + t)]
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    rw [Nat.cast_add]
    ring
  rw [hnum]
  have hcomplement :
      (∏ i ∈ Finset.range t,
        Real.sin ((r + i) * quantumTheta r d)) =
      ∏ i ∈ Finset.range t,
        Real.sin ((d - i) * quantumTheta r d) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (quantum_sin_d_sub_eq_r_add hr hd (by
      have hit := Finset.mem_range.mp hi
      omega)).symm
  rw [hcomplement, ← Finset.prod_div_distrib]
  simpa only [Nat.cast_add, Nat.cast_one] using
    quantum_sineProduct_d_eq_quantumBinomialCoefficient hr hd ht

/-- Lemma 5.1, complete-homogeneous half: `h_t(X)=b_t`. -/
theorem quantumAlphabetX_complete_eq_coe_quantumBinomialCoefficient
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    completeHomogeneousSpecialization (quantumAlphabetX r d) t =
      (quantumBinomialCoefficient r d t : ℂ) := by
  rw [quantumAlphabetX_complete_eq_sineProduct hr hd ht]
  have hreal := quantum_sineProduct_complete_eq_quantumBinomialCoefficient
    hr hd ht
  calc
    (∏ i ∈ Finset.range t,
        ((Real.sin ((((r + t - 1 : ℕ) : ℝ) - (i : ℝ)) *
            quantumTheta r d) : ℂ) /
          Real.sin (((i + 1 : ℕ) : ℝ) * quantumTheta r d))) =
      ((∏ i ∈ Finset.range t,
        Real.sin ((((r + t - 1 : ℕ) : ℝ) - (i : ℝ)) *
            quantumTheta r d) /
          Real.sin (((i + 1 : ℕ) : ℝ) * quantumTheta r d)) : ℝ) := by
        push_cast
        rfl
    _ = (quantumBinomialCoefficient r d t : ℂ) := by exact_mod_cast hreal

/-- Lemma 5.1, elementary half: `b_t = e_t(Y)` for every displayed
coefficient. -/
theorem quantumAlphabetY_elementary_eq_coe_quantumBinomialCoefficient
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    elementarySymmetricSpecialization (quantumAlphabetY r d) t =
      (quantumBinomialCoefficient r d t : ℂ) := by
  rw [quantumAlphabetY_elementary_eq_sineProduct hr hd ht]
  have hreal := quantum_sineProduct_d_eq_quantumBinomialCoefficient hr hd ht
  calc
    (∏ i ∈ Finset.range t,
        ((Real.sin ((d - i) * quantumTheta r d) : ℂ) /
          Real.sin ((i + 1) * quantumTheta r d))) =
      ((∏ i ∈ Finset.range t,
        Real.sin ((d - i) * quantumTheta r d) /
          Real.sin ((i + 1) * quantumTheta r d)) : ℝ) := by
        push_cast
        rfl
    _ = (quantumBinomialCoefficient r d t : ℂ) := by exact_mod_cast hreal

/-- Lemma 5.1, bundled rank--level identity. -/
theorem quantum_rankLevel_identity
    {r d t : ℕ} (hr : 0 < r) (hd : 0 < d) (ht : t ≤ d) :
    (quantumBinomialCoefficient r d t : ℂ) =
        completeHomogeneousSpecialization (quantumAlphabetX r d) t ∧
      (quantumBinomialCoefficient r d t : ℂ) =
        elementarySymmetricSpecialization (quantumAlphabetY r d) t := by
  exact ⟨(quantumAlphabetX_complete_eq_coe_quantumBinomialCoefficient
      hr hd ht).symm,
    (quantumAlphabetY_elementary_eq_coe_quantumBinomialCoefficient
      hr hd ht).symm⟩

/-- The zero tuple is a partition. -/
theorem zero_isNPartition {N : ℕ} :
    AlgebraicCombinatorics.IsNPartition (0 : Fin N → ℕ) := by
  intro i j hij
  rfl

/-- The Schur polynomial of the zero partition is one. -/
theorem algebraicCombinatorics_schurPoly_zero
    {N : ℕ} {R : Type*} [CommRing R] [IsDomain R] :
    (schurPoly (R := R) (0 : Fin N → ℕ)) = 1 := by
  have h := schurPoly_eq_alternant_div (R := R) (0 : Fin N → ℕ)
    zero_isNPartition
  simp only [zero_add] at h
  exact (alternant_rho_isRegular (R := R) (N := N)).left (by
    simpa using h.symm)

/-- Littlewood--Richardson with zero initial weight expands a skew Schur
polynomial as a finite sum of ordinary Schur polynomials indexed by
zero-Yamanouchi tableaux. -/
theorem skewSchurPoly_eq_sum_schur_content
    {N : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (lam mu : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    (skewSchurPoly lam mu : MvPolynomial (Fin N) R) =
      ∑ T : {T : Tableau lam mu // IsYamanouchi 0 T},
        schurPoly (contentTableau T.val) := by
  have h := littlewoodRichardson (R := R) lam mu 0
    hlam hmu zero_isNPartition
  rw [algebraicCombinatorics_schurPoly_zero, one_mul] at h
  simpa only [Pi.add_apply, Pi.zero_apply, zero_add] using h

/-- Evaluation preserves the finite Littlewood--Richardson expansion. -/
theorem aeval_skewSchurPoly_eq_sum_schur_content
    {N : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S]
    (x : Fin N → S) (lam mu : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    MvPolynomial.aeval x (skewSchurPoly lam mu : MvPolynomial (Fin N) R) =
      ∑ T : {T : Tableau lam mu // IsYamanouchi 0 T},
        MvPolynomial.aeval x
          (schurPoly (contentTableau T.val) : MvPolynomial (Fin N) R) := by
  rw [skewSchurPoly_eq_sum_schur_content lam mu hlam hmu, map_sum]

/-- Filling every skew cell by its row index is semistandard. -/
def rowIndexTableau {N : ℕ} (lam mu : Fin N → ℕ) : Tableau lam mu :=
  fun c ↦ c.val.1

theorem rowIndexTableau_isSemistandard
    {N : ℕ} (lam mu : Fin N → ℕ) :
    IsSemistandard (rowIndexTableau lam mu) := by
  constructor
  · intro c e hrow hcol
    simpa [rowIndexTableau, hrow]
  · intro c e hcol hrow
    simpa [rowIndexTableau] using hrow

/-- Every skew Schur polynomial is nonzero: the row-index tableau supplies
one monomial with a positive coefficient. -/
theorem skewSchurPoly_ne_zero
    {N : ℕ} (lam mu : Fin N → ℕ) :
    (skewSchurPoly lam mu : MvPolynomial (Fin N) ℤ) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.aeval fun _i : Fin N ↦ (1 : ℤ)) hzero
  unfold skewSchurPoly at heval
  rw [map_sum] at heval
  simp only [map_zero] at heval
  have hone : ∀ T : {T : Tableau lam mu // IsSemistandard T},
      MvPolynomial.aeval (fun _i : Fin N ↦ (1 : ℤ))
        (xPow (contentTableau T.val) : MvPolynomial (Fin N) ℤ) = 1 := by
    intro T
    simp [xPow, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]
  simp_rw [hone] at heval
  have hnonempty : Nonempty {T : Tableau lam mu // IsSemistandard T} :=
    ⟨⟨rowIndexTableau lam mu, rowIndexTableau_isSemistandard lam mu⟩⟩
  have hcard : 0 < Fintype.card {T : Tableau lam mu // IsSemistandard T} :=
    Fintype.card_pos_iff.mpr hnonempty
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at heval
  have hcardZ : (Fintype.card {T : Tableau lam mu // IsSemistandard T} : ℤ) ≠ 0 := by
    exact_mod_cast hcard.ne'
  exact hcardZ heval

/-- The zero-Yamanouchi indexing family in the checked LR expansion is
nonempty for every pair of partitions. -/
theorem nonempty_zeroYamanouchi
    {N : ℕ} (lam mu : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    Nonempty {T : Tableau lam mu // IsYamanouchi 0 T} := by
  by_contra hnone
  letI : IsEmpty {T : Tableau lam mu // IsYamanouchi 0 T} :=
    not_nonempty_iff.mp hnone
  have hexp := skewSchurPoly_eq_sum_schur_content
    (R := ℤ) lam mu hlam hmu
  have hsum : (∑ T : {T : Tableau lam mu // IsYamanouchi 0 T},
      (schurPoly (contentTableau T.val) : MvPolynomial (Fin N) ℤ)) = 0 := by
    simp
  rw [hsum] at hexp
  exact skewSchurPoly_ne_zero lam mu hexp

/-- Ordinary Schur evaluation at the centered `d`-letter quantum alphabet. -/
def quantumSchurValue (r d : ℕ) (nu : Fin d → ℕ) : ℂ :=
  MvPolynomial.aeval (quantumAlphabetY r d)
    (schurPoly (R := ℂ) nu)

/-- Skew Schur evaluation at the centered `d`-letter quantum alphabet. -/
def quantumSkewSchurValue
    (r d : ℕ) (lam mu : Fin d → ℕ) : ℂ :=
  MvPolynomial.aeval (quantumAlphabetY r d)
    (skewSchurPoly lam mu : MvPolynomial (Fin d) ℂ)

/-- Equation (25), with the nonnegative integer multiplicities left as their
canonical zero-Yamanouchi tableau indexing type. -/
theorem quantumSkewSchurValue_eq_sum
    {r d : ℕ} (lam mu : Fin d → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu) :
    quantumSkewSchurValue r d lam mu =
      ∑ T : {T : Tableau lam mu // IsYamanouchi 0 T},
        quantumSchurValue r d (contentTableau T.val) := by
  exact aeval_skewSchurPoly_eq_sum_schur_content
    (R := ℂ) (quantumAlphabetY r d) lam mu hlam hmu

/-- In a semistandard tableau, entries equal to zero occupy distinct
columns.  Hence their number is bounded by the width of the outer
partition.  This is the precise tableau bound used after equation (25). -/
theorem contentTableau_zero_le_firstPart
    {N : ℕ} (hN : 0 < N) {lam mu : Fin N → ℕ}
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    contentTableau T ⟨0, hN⟩ ≤ lam ⟨0, hN⟩ := by
  let zeroCells :=
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = ⟨0, hN⟩}
  let column : zeroCells → Fin (lam ⟨0, hN⟩) := fun c ↦
    ⟨c.val.val.2 - 1, by
      have hcShape := c.val.property
      change mu c.val.val.1 < c.val.val.2 ∧
        c.val.val.2 ≤ lam c.val.val.1 at hcShape
      have hrow : lam c.val.val.1 ≤ lam ⟨0, hN⟩ :=
        hlam ⟨0, hN⟩ c.val.val.1 (by
          apply Fin.mk_le_mk.mpr
          omega)
      omega⟩
  have hcolumn : Function.Injective column := by
    intro c e hce
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rcases lt_trichotomy c.val.val.1 e.val.val.1 with hlt | heq | hgt
      · have hstrict := hT.2 c.val e.val (by
          have hval := congrArg Fin.val hce
          dsimp only [column] at hval
          have hcPos := c.val.property.1
          have hePos := e.val.property.1
          omega) hlt
        rw [c.property, e.property] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · exact heq
      · have hstrict := hT.2 e.val c.val (by
          have hval := congrArg Fin.val hce
          dsimp only [column] at hval
          have hcPos := c.val.property.1
          have hePos := e.val.property.1
          omega) hgt
        rw [c.property, e.property] at hstrict
        exact (lt_irrefl _ hstrict).elim
    · have hval := congrArg Fin.val hce
      dsimp only [column] at hval
      have hcPos := c.val.property.1
      have hePos := e.val.property.1
      omega
  have hcard := Fintype.card_le_of_injective column hcolumn
  rw [Fintype.card_fin] at hcard
  have hzeroCard : Fintype.card zeroCells =
      (Finset.univ.filter fun c ↦ T c = ⟨0, hN⟩).card := by
    dsimp only [zeroCells]
    rw [Fintype.card_subtype]
  rw [contentTableau_eq_card, ← hzeroCard]
  exact hcard

/-! ## Alternant evaluation -/

/-- Evaluation of the checked alternant polynomial is the corresponding
power-alternant determinant. -/
theorem aeval_alternant
    {N : ℕ} {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (x : Fin N → S) (alpha : Fin N → ℕ) :
    MvPolynomial.aeval x
        (AlgebraicCombinatorics.alternant (R := R) alpha) =
      (Matrix.of fun i j : Fin N ↦ x j ^ alpha i).det := by
  rw [AlgebraicCombinatorics.alternant_eq_det]
  change (MvPolynomial.aeval x).toRingHom
      (AlgebraicCombinatorics.alternantMatrix alpha).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [AlgebraicCombinatorics.alternantMatrix]

/-- A power alternant on a geometric progression factors into a diagonal
scale and a Vandermonde matrix. -/
theorem det_geometricAlternant
    {N : ℕ} {K : Type*} [Field K]
    (scale ratio : K) (alpha : Fin N → ℕ) :
    (Matrix.of fun i j : Fin N ↦
        (scale * ratio ^ j.val) ^ alpha i).det =
      (∏ i, scale ^ alpha i) *
        (Matrix.vandermonde fun i : Fin N ↦ ratio ^ alpha i).det := by
  let D : Matrix (Fin N) (Fin N) K := Matrix.diagonal fun i ↦ scale ^ alpha i
  let V : Matrix (Fin N) (Fin N) K :=
    Matrix.vandermonde fun i ↦ ratio ^ alpha i
  have hmatrix : (Matrix.of fun i j : Fin N ↦
      (scale * ratio ^ j.val) ^ alpha i) = D * V := by
    ext i j
    rw [Matrix.diagonal_mul]
    dsimp only [D, V]
    simp only [Matrix.vandermonde_apply]
    change (scale * ratio ^ j.val) ^ alpha i =
      scale ^ alpha i * (ratio ^ alpha i) ^ j.val
    rw [mul_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]

/-- No nontrivial power below `d+r` of the quantum common ratio is one. -/
theorem centeredAlphabetRatio_pow_ne_one
    {r d u : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hu : 0 < u) (huN : u < d + r) :
    centeredAlphabetRatio (quantumTheta r d) ^ u ≠ 1 := by
  intro hpow
  let theta := quantumTheta r d
  have hfactor := one_sub_exp_two_mul_I (u * theta)
  have hqpow : centeredAlphabetRatio theta ^ u =
      Complex.exp (Complex.I * 2 * ((u : ℂ) * (theta : ℂ))) := by
    unfold centeredAlphabetRatio
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hcast : (((u : ℝ) * theta : ℝ) : ℂ) =
      (u : ℂ) * (theta : ℂ) := by norm_cast
  rw [hcast] at hfactor
  rw [← hqpow, hpow, sub_self] at hfactor
  have hsin : (Real.sin (u * theta) : ℂ) ≠ 0 := by
    exact_mod_cast (quantum_sin_pos_of_index hr hd hu huN).ne'
  have hnonzero : -2 * Complex.I *
      Complex.exp (Complex.I * ((u : ℂ) * (theta : ℂ))) *
        (Real.sin (u * theta) : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (Complex.exp_ne_zero _)) hsin
  exact hnonzero hfactor.symm

/-- The geometric Vandermonde denominator for the quantum alphabet is
nonzero. -/
theorem quantum_rho_vandermonde_ne_zero
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (Matrix.vandermonde fun i : Fin d ↦
      centeredAlphabetRatio (quantumTheta r d) ^
        AlgebraicCombinatorics.rho d i).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hrho : AlgebraicCombinatorics.rho d j <
      AlgebraicCombinatorics.rho d i :=
    AlgebraicCombinatorics.rho_strictAnti hij
  let u := AlgebraicCombinatorics.rho d i - AlgebraicCombinatorics.rho d j
  have hu : 0 < u := by dsimp only [u]; omega
  have huN : u < d + r := by
    have huLe : u ≤ AlgebraicCombinatorics.rho d i := by
      dsimp only [u]
      exact Nat.sub_le _ _
    have hrhoBound : AlgebraicCombinatorics.rho d i < d + r := by
      simp only [AlgebraicCombinatorics.rho_apply]
      omega
    exact huLe.trans_lt hrhoBound
  intro hzero
  have heq : centeredAlphabetRatio (quantumTheta r d) ^
        AlgebraicCombinatorics.rho d j =
      centeredAlphabetRatio (quantumTheta r d) ^
        AlgebraicCombinatorics.rho d i := sub_eq_zero.mp hzero
  have hrhoAdd : AlgebraicCombinatorics.rho d j + u =
      AlgebraicCombinatorics.rho d i := by dsimp only [u]; omega
  rw [← hrhoAdd, pow_add] at heq
  have hbase : centeredAlphabetRatio (quantumTheta r d) ^
      AlgebraicCombinatorics.rho d j ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have huOne : centeredAlphabetRatio (quantumTheta r d) ^ u = 1 := by
    apply (mul_left_cancel₀ hbase)
    simpa using heq.symm
  exact (centeredAlphabetRatio_pow_ne_one hr hd hu huN) huOne

/-- Powers of the centered common ratio are elementary exponentials. -/
theorem centeredAlphabetRatio_pow (theta : ℝ) (n : ℕ) :
    centeredAlphabetRatio theta ^ n =
      Complex.exp (Complex.I * 2 * (n : ℂ) * (theta : ℂ)) := by
  unfold centeredAlphabetRatio
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- Difference of two ordered geometric nodes in sine form. -/
theorem centeredAlphabetRatio_pow_sub
    (theta : ℝ) {A B : ℕ} (hBA : B ≤ A) :
    centeredAlphabetRatio theta ^ B - centeredAlphabetRatio theta ^ A =
      -2 * Complex.I *
        Complex.exp (Complex.I * ((A + B : ℕ) : ℂ) * (theta : ℂ)) *
          (Real.sin ((A - B : ℕ) * theta) : ℂ) := by
  have hAB : B + (A - B) = A := Nat.add_sub_of_le hBA
  have hpA : centeredAlphabetRatio theta ^ A =
      centeredAlphabetRatio theta ^ B *
        centeredAlphabetRatio theta ^ (A - B) := by
    calc
      centeredAlphabetRatio theta ^ A =
          centeredAlphabetRatio theta ^ (B + (A - B)) := by rw [hAB]
      _ = _ := pow_add _ _ _
  have hfactor := one_sub_exp_two_mul_I ((A - B : ℕ) * theta)
  have hcast : ((((A - B : ℕ) : ℝ) * theta : ℝ) : ℂ) =
      ((A - B : ℕ) : ℂ) * (theta : ℂ) := by norm_cast
  rw [hcast] at hfactor
  have hpow :
      Complex.exp (Complex.I * 2 *
        (((A - B : ℕ) : ℂ) * (theta : ℂ))) =
        centeredAlphabetRatio theta ^ (A - B) := by
    symm
    simpa only [mul_assoc] using centeredAlphabetRatio_pow theta (A - B)
  rw [hpow] at hfactor
  calc
    centeredAlphabetRatio theta ^ B - centeredAlphabetRatio theta ^ A =
        centeredAlphabetRatio theta ^ B - centeredAlphabetRatio theta ^ B *
          centeredAlphabetRatio theta ^ (A - B) := by rw [hpA]
    _ = centeredAlphabetRatio theta ^ B *
        (1 - centeredAlphabetRatio theta ^ (A - B)) := by ring
    _ = centeredAlphabetRatio theta ^ B *
        (-2 * Complex.I *
          Complex.exp (Complex.I * ((A - B : ℕ) : ℂ) * (theta : ℂ)) *
            (Real.sin ((A - B : ℕ) * theta) : ℂ)) := by
      have h := congrArg (fun z : ℂ ↦ centeredAlphabetRatio theta ^ B * z) hfactor
      simpa only [mul_assoc] using h
    _ = -2 * Complex.I *
        (Complex.exp (Complex.I * 2 * (B : ℂ) * (theta : ℂ)) *
          Complex.exp (Complex.I * ((A - B : ℕ) : ℂ) * (theta : ℂ))) *
            (Real.sin ((A - B : ℕ) * theta) : ℂ) := by
      rw [centeredAlphabetRatio_pow]
      ring
    _ = -2 * Complex.I *
        Complex.exp (Complex.I * ((A + B : ℕ) : ℂ) * (theta : ℂ)) *
          (Real.sin ((A - B : ℕ) * theta) : ℂ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      rw [Nat.cast_sub hBA]
      ring

/-- The evaluated Weyl denominator for `Y` is nonzero. -/
theorem quantumAlphabetY_rhoAlternant_ne_zero
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (Matrix.of fun i j : Fin d ↦
      quantumAlphabetY r d j ^ AlgebraicCombinatorics.rho d i).det ≠ 0 := by
  have hmatrix : (Matrix.of fun i j : Fin d ↦
      quantumAlphabetY r d j ^ AlgebraicCombinatorics.rho d i) =
      Matrix.of fun i j : Fin d ↦
        (centeredAlphabetScale d (quantumTheta r d) *
          centeredAlphabetRatio (quantumTheta r d) ^ j.val) ^
            AlgebraicCombinatorics.rho d i := by
    ext i j
    change centeredAlphabetRoot d (quantumTheta r d) j ^
        AlgebraicCombinatorics.rho d i = _
    rw [centeredAlphabetRoot_eq_scale_mul_ratio_pow]
    rfl
  rw [hmatrix, det_geometricAlternant]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact quantum_rho_vandermonde_ne_zero hr hd

/-! ## Weyl phase cancellation -/

/-- Product over the strictly upper-triangular pairs of a finite ordinal. -/
def strictPairProduct {d : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin d → Fin d → M) : M :=
  ∏ i, ∏ j ∈ Finset.Ioi i, f i j

theorem strictPairProduct_mul
    {d : ℕ} {M : Type*} [CommMonoid M]
    (f g : Fin d → Fin d → M) :
    strictPairProduct (fun i j ↦ f i j * g i j) =
      strictPairProduct f * strictPairProduct g := by
  unfold strictPairProduct
  simp_rw [Finset.prod_mul_distrib]

/-- Every entry appears in exactly `d-1` unordered pairs. -/
theorem strictPairProduct_entry_mul
    {d : ℕ} {M : Type*} [CommMonoid M] (z : Fin d → M) :
    strictPairProduct (fun i j ↦ z i * z j) =
      ∏ i, z i ^ (d - 1) := by
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
    (fun _i j : Fin d ↦ z j)
  unfold strictPairProduct
  rw [h]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_const]
  congr 1
  rw [Finset.card_compl]
  simp

/-- One centered scale factor cancels the `d-1` pair phases attached to
the same exponent. -/
theorem centeredScale_pow_mul_pairPhase
    (d A : ℕ) (hd : 0 < d) (theta : ℝ) :
    centeredAlphabetScale d theta ^ A *
        Complex.exp (Complex.I * (A : ℂ) * (theta : ℂ)) ^ (d - 1) = 1 := by
  unfold centeredAlphabetScale
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  rw [show
      (A : ℂ) * (Complex.I * ((1 : ℤ) - d : ℂ) * (theta : ℂ)) +
          ((d - 1 : ℕ) : ℂ) *
            (Complex.I * (A : ℂ) * (theta : ℂ)) = 0 by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring]
  exact Complex.exp_zero

/-- The total diagonal scale and pair phase cancel for every exponent
vector. -/
theorem centeredScaleProduct_mul_pairPhaseProduct
    {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℕ) (theta : ℝ) :
    (∏ i, centeredAlphabetScale d theta ^ alpha i) *
        strictPairProduct (fun i j ↦
          Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ))) = 1 := by
  have hphase : strictPairProduct (fun i j ↦
      Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
        (theta : ℂ))) =
      ∏ i, Complex.exp (Complex.I * (alpha i : ℂ) *
        (theta : ℂ)) ^ (d - 1) := by
    have hpoint : ∀ i j : Fin d,
        Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ)) =
          Complex.exp (Complex.I * (alpha i : ℂ) * (theta : ℂ)) *
            Complex.exp (Complex.I * (alpha j : ℂ) * (theta : ℂ)) := by
      intro i j
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hpoint]
    exact strictPairProduct_entry_mul _
  rw [hphase, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  exact centeredScale_pow_mul_pairPhase d (alpha i) hd theta

/-- Vandermonde determinant of decreasing quantum exponents, separated into
the common constant, phase, and sine products. -/
theorem quantumVandermonde_eq_constant_phase_sine
    {d : ℕ} (theta : ℝ) (alpha : Fin d → ℕ)
    (hstrict : ∀ {i j : Fin d}, i < j → alpha j < alpha i) :
    (Matrix.vandermonde fun i : Fin d ↦
        centeredAlphabetRatio theta ^ alpha i).det =
      strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
        strictPairProduct (fun i j ↦
          Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ))) *
        strictPairProduct (fun i j ↦
          (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ)) := by
  rw [Matrix.det_vandermonde]
  change strictPairProduct (fun i j ↦
      centeredAlphabetRatio theta ^ alpha j -
        centeredAlphabetRatio theta ^ alpha i) = _
  have hpoint : ∀ {i j : Fin d}, i < j →
      centeredAlphabetRatio theta ^ alpha j -
          centeredAlphabetRatio theta ^ alpha i =
        ((-2 : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ)) *
            (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ)) := by
    intro i j hij
    simpa [mul_assoc] using centeredAlphabetRatio_pow_sub theta
      (show alpha j ≤ alpha i from (hstrict hij).le)
  have hrewrite : strictPairProduct (fun i j ↦
      centeredAlphabetRatio theta ^ alpha j -
        centeredAlphabetRatio theta ^ alpha i) =
      strictPairProduct (fun i j ↦
      ((-2 : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
          (theta : ℂ)) *
          (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ))) := by
    unfold strictPairProduct
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    exact hpoint (Finset.mem_Ioi.mp hj)
  rw [hrewrite]
  calc
    strictPairProduct (fun i j ↦
        ((-2 : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ)) *
            (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ))) =
      strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
        strictPairProduct (fun i j ↦
          Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ)) *
          (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ)) :=
        strictPairProduct_mul _ _
    _ = strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
        (strictPairProduct (fun i j ↦
          Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
            (theta : ℂ))) *
        strictPairProduct (fun i j ↦
          (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ))) := by
      apply congrArg (fun z : ℂ ↦
        strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) * z)
      exact strictPairProduct_mul _ _
    _ = _ := by ring

/-- After centering, the complete geometric alternant is the common pair
constant times the Weyl sine numerator. -/
theorem quantumGeometricAlternant_eq_constant_sine
    {d : ℕ} (hd : 0 < d) (theta : ℝ) (alpha : Fin d → ℕ)
    (hstrict : ∀ {i j : Fin d}, i < j → alpha j < alpha i) :
    (Matrix.of fun i j : Fin d ↦
      (centeredAlphabetScale d theta * centeredAlphabetRatio theta ^ j.val) ^
        alpha i).det =
      strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
        strictPairProduct (fun i j ↦
          (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ)) := by
  rw [det_geometricAlternant,
    quantumVandermonde_eq_constant_phase_sine theta alpha hstrict]
  have hphase := centeredScaleProduct_mul_pairPhaseProduct hd alpha theta
  calc
    (∏ i, centeredAlphabetScale d theta ^ alpha i) *
        (strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
          strictPairProduct (fun i j ↦
            Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
              (theta : ℂ))) *
          strictPairProduct (fun i j ↦
            (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ))) =
      strictPairProduct (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I) *
        ((∏ i, centeredAlphabetScale d theta ^ alpha i) *
          strictPairProduct (fun i j ↦
            Complex.exp (Complex.I * ((alpha i + alpha j : ℕ) : ℂ) *
              (theta : ℂ))) *
          strictPairProduct (fun i j ↦
            (Real.sin ((alpha i - alpha j : ℕ) * theta) : ℂ))) := by ring
    _ = _ := by rw [hphase, one_mul]

/-- The Weyl alternant quotient, before specializing the variables to the
root-of-unity alphabet. -/
theorem aeval_schurPoly_eq_alternant_div
    {N : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [Field S] [Algebra R S]
    (x : Fin N → S) (nu : Fin N → ℕ)
    (hnu : AlgebraicCombinatorics.IsNPartition nu)
    (hden : (Matrix.of fun i j : Fin N ↦
      x j ^ AlgebraicCombinatorics.rho N i).det ≠ 0) :
    MvPolynomial.aeval x
        (schurPoly (R := R) nu) =
      (Matrix.of fun i j : Fin N ↦
          x j ^ (nu i + AlgebraicCombinatorics.rho N i)).det /
        (Matrix.of fun i j : Fin N ↦
          x j ^ AlgebraicCombinatorics.rho N i).det := by
  have hpoly := AlgebraicCombinatorics.schurPoly_eq_alternant_div
    (R := R) nu hnu
  have heval := congrArg (MvPolynomial.aeval x) hpoly
  rw [map_mul, aeval_alternant, aeval_alternant] at heval
  apply (eq_div_iff hden).2
  simpa [Pi.add_apply, mul_comm] using heval.symm

/-- Formula (24): Schur evaluation at the centered quantum alphabet is the
Weyl sine product. -/
theorem quantumSchurValue_eq_coe_weylSineProduct
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {nu : Fin d → ℕ} (hnu : IsPartitionVector nu) :
    quantumSchurValue r d nu = (weylSineProduct r d nu : ℂ) := by
  let rho : Fin d → ℕ := AlgebraicCombinatorics.rho d
  let alpha : Fin d → ℕ := fun i ↦ nu i + rho i
  have hnu' : AlgebraicCombinatorics.IsNPartition nu := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact hnu i j hij
  have hstrictAlpha : ∀ {i j : Fin d}, i < j → alpha j < alpha i := by
    intro i j hij
    have hnule : nu j ≤ nu i := hnu i j hij
    have hrholt : rho j < rho i := AlgebraicCombinatorics.rho_strictAnti hij
    dsimp only [alpha]
    omega
  have hstrictRho : ∀ {i j : Fin d}, i < j → rho j < rho i := by
    intro i j hij
    exact AlgebraicCombinatorics.rho_strictAnti hij
  have halphaIndex : ∀ {i j : Fin d}, i < j →
      alpha i - alpha j = (nu i - nu j) + (j.val - i.val) := by
    intro i j hij
    have hnule : nu j ≤ nu i := hnu i j hij
    simp only [alpha, rho, AlgebraicCombinatorics.rho_apply]
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  have hrhoIndex : ∀ {i j : Fin d}, i < j →
      rho i - rho j = j.val - i.val := by
    intro i j hij
    simp only [rho, AlgebraicCombinatorics.rho_apply]
    have hiBound := i.isLt
    have hjBound := j.isLt
    omega
  let common : ℂ := strictPairProduct
    (fun _i _j : Fin d ↦ (-2 : ℂ) * Complex.I)
  let sineNum : ℂ := strictPairProduct (fun i j ↦
    (Real.sin ((alpha i - alpha j : ℕ) * quantumTheta r d) : ℂ))
  let sineDen : ℂ := strictPairProduct (fun i j ↦
    (Real.sin ((rho i - rho j : ℕ) * quantumTheta r d) : ℂ))
  have hnumDet :
      (Matrix.of fun i j : Fin d ↦ quantumAlphabetY r d j ^ alpha i).det =
        common * sineNum := by
    have h := quantumGeometricAlternant_eq_constant_sine hd
      (quantumTheta r d) alpha hstrictAlpha
    have hmatrix : (Matrix.of fun i j : Fin d ↦
        quantumAlphabetY r d j ^ alpha i) =
        Matrix.of fun i j : Fin d ↦
          (centeredAlphabetScale d (quantumTheta r d) *
            centeredAlphabetRatio (quantumTheta r d) ^ j.val) ^ alpha i := by
      ext i j
      change centeredAlphabetRoot d (quantumTheta r d) j ^ alpha i = _
      rw [centeredAlphabetRoot_eq_scale_mul_ratio_pow]
      rfl
    rw [hmatrix]
    simpa only [common, sineNum] using h
  have hdenDet :
      (Matrix.of fun i j : Fin d ↦ quantumAlphabetY r d j ^ rho i).det =
        common * sineDen := by
    have h := quantumGeometricAlternant_eq_constant_sine hd
      (quantumTheta r d) rho hstrictRho
    have hmatrix : (Matrix.of fun i j : Fin d ↦
        quantumAlphabetY r d j ^ rho i) =
        Matrix.of fun i j : Fin d ↦
          (centeredAlphabetScale d (quantumTheta r d) *
            centeredAlphabetRatio (quantumTheta r d) ^ j.val) ^ rho i := by
      ext i j
      change centeredAlphabetRoot d (quantumTheta r d) j ^ rho i = _
      rw [centeredAlphabetRoot_eq_scale_mul_ratio_pow]
      rfl
    rw [hmatrix]
    simpa only [common, sineDen] using h
  have hcommon : common ≠ 0 := by
    dsimp only [common, strictPairProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hsineDen : sineDen ≠ 0 := by
    dsimp only [sineDen, strictPairProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hgap : 0 < rho i - rho j :=
      Nat.sub_pos_of_lt (hstrictRho hij)
    have hgapN : rho i - rho j < d + r := by
      rw [hrhoIndex hij]
      have hjBound := j.isLt
      omega
    exact_mod_cast (quantum_sin_pos_of_index hr hd hgap hgapN).ne'
  have hweyl : (weylSineProduct r d nu : ℂ) = sineNum / sineDen := by
    unfold weylSineProduct
    dsimp only [sineNum, sineDen, strictPairProduct]
    push_cast
    simp_rw [Finset.prod_div_distrib]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      rw [halphaIndex (Finset.mem_Ioi.mp hj)]
      push_cast
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      rw [hrhoIndex (Finset.mem_Ioi.mp hj)]
  unfold quantumSchurValue
  rw [aeval_schurPoly_eq_alternant_div
    (x := quantumAlphabetY r d) (nu := nu) hnu'
    (quantumAlphabetY_rhoAlternant_ne_zero hr hd)]
  change (Matrix.of fun i j : Fin d ↦
      quantumAlphabetY r d j ^ alpha i).det /
      (Matrix.of fun i j : Fin d ↦
        quantumAlphabetY r d j ^ rho i).det = _
  rw [hnumDet, hdenDet, hweyl]
  field_simp [hcommon, hsineDen]

/-- Strict positivity of the quantum Schur specialization in the level-`r`
alcove. -/
theorem quantumSchurValue_eq_coe_pos
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {nu : Fin d → ℕ} (hnu : IsPartitionVector nu)
    (hbound : ∀ i, nu i ≤ r) :
    ∃ x : ℝ, 0 < x ∧ quantumSchurValue r d nu = (x : ℂ) := by
  refine ⟨weylSineProduct r d nu,
    weylSineProduct_pos hr hd hnu hbound, ?_⟩
  exact quantumSchurValue_eq_coe_weylSineProduct hr hd hnu

/-- Nonnegativity at the adjacent boundary `nu₁ ≤ r+1`. -/
theorem quantumSchurValue_eq_coe_nonneg
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {nu : Fin d → ℕ} (hnu : IsPartitionVector nu)
    (hbound : ∀ i, nu i ≤ r + 1) :
    ∃ x : ℝ, 0 ≤ x ∧ quantumSchurValue r d nu = (x : ℂ) := by
  refine ⟨weylSineProduct r d nu,
    weylSineProduct_nonneg hr hd hnu hbound, ?_⟩
  exact quantumSchurValue_eq_coe_weylSineProduct hr hd hnu

/-- Strict positivity of a quantum skew Schur specialization when the
outer width is at most `r`. -/
theorem quantumSkewSchurValue_eq_coe_pos
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {lam mu : Fin d → ℕ}
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (hwidth : lam ⟨0, hd⟩ ≤ r) :
    ∃ x : ℝ, 0 < x ∧ quantumSkewSchurValue r d lam mu = (x : ℂ) := by
  let termReal : {T : Tableau lam mu // IsYamanouchi 0 T} → ℝ := fun T ↦
    Classical.choose (quantumSchurValue_eq_coe_pos hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))
  have htermPos : ∀ T, 0 < termReal T := by
    intro T
    exact (Classical.choose_spec (quantumSchurValue_eq_coe_pos hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))).1
  let x : ℝ := ∑ T, termReal T
  have hx : 0 < x := by
    dsimp only [x]
    apply Finset.sum_pos'
    · intro T hT
      exact (htermPos T).le
    · obtain ⟨T⟩ := nonempty_zeroYamanouchi lam mu hlam hmu
      exact ⟨T, Finset.mem_univ T, htermPos T⟩
  refine ⟨x, hx, ?_⟩
  rw [quantumSkewSchurValue_eq_sum lam mu hlam hmu]
  have htermEq : ∀ T, quantumSchurValue r d (contentTableau T.val) =
      (termReal T : ℂ) := by
    intro T
    exact (Classical.choose_spec (quantumSchurValue_eq_coe_pos hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))).2
  simp_rw [htermEq]
  exact_mod_cast rfl

/-- Nonnegativity of a quantum skew Schur specialization at outer width
`r+1`. -/
theorem quantumSkewSchurValue_eq_coe_nonneg
    {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {lam mu : Fin d → ℕ}
    (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hmu : AlgebraicCombinatorics.IsNPartition mu)
    (hwidth : lam ⟨0, hd⟩ ≤ r + 1) :
    ∃ x : ℝ, 0 ≤ x ∧ quantumSkewSchurValue r d lam mu = (x : ℂ) := by
  let termReal : {T : Tableau lam mu // IsYamanouchi 0 T} → ℝ := fun T ↦
    Classical.choose (quantumSchurValue_eq_coe_nonneg hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r + 1 by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))
  let x : ℝ := ∑ T, termReal T
  have hx : 0 ≤ x := by
    dsimp only [x]
    apply Finset.sum_nonneg
    intro T hT
    exact (Classical.choose_spec (quantumSchurValue_eq_coe_nonneg hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r + 1 by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))).1
  refine ⟨x, hx, ?_⟩
  rw [quantumSkewSchurValue_eq_sum lam mu hlam hmu]
  have htermEq : ∀ T, quantumSchurValue r d (contentTableau T.val) =
      (termReal T : ℂ) := by
    intro T
    exact (Classical.choose_spec (quantumSchurValue_eq_coe_nonneg hr hd
      (show IsPartitionVector (contentTableau T.val) by
        intro i j hij
        exact T.prop.isNPartition_content_of_zero i j hij.le)
      (show ∀ i, contentTableau T.val i ≤ r + 1 by
        intro i
        have hpart := T.prop.isNPartition_content_of_zero
          (⟨0, hd⟩ : Fin d) i (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        exact hpart.trans (contentTableau_zero_le_firstPart hd hlam T.val
          T.prop.isSemistandard |>.trans hwidth)))).2
  simp_rw [htermEq]
  exact_mod_cast rfl

end

end FurtherToeplitzPositroids
