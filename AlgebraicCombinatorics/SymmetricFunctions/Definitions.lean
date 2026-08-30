/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Definitions and Examples of Symmetric Polynomials

This file formalizes the definitions and basic properties of symmetric polynomials,
following Section "Definitions and examples of symmetric polynomials" (sec.sf.sp) of the source.

## Main definitions

* We use Mathlib's `MvPolynomial.IsSymmetric` for the notion of symmetric polynomials.
* `MvPolynomial.symmetricSubalgebra σ R` is the ring of symmetric polynomials.
* `MvPolynomial.esymm σ R n` is the n-th elementary symmetric polynomial.
* `MvPolynomial.hsymm σ R n` is the n-th complete homogeneous symmetric polynomial.
* `MvPolynomial.psum σ R n` is the n-th power sum.

## Main results

* The symmetric group acts on polynomials by permuting variables (Proposition prop.sf.SN-acts)
* The action is by K-algebra automorphisms (Proposition prop.sf.SN-acts-by-alg-auts)
* The set of symmetric polynomials forms a K-subalgebra (Theorem thm.sf.S-subalg)
* For n > N, the n-th elementary symmetric polynomial is zero (Proposition prop.sf.en=0)
* Newton-Girard formulas relating e_n, h_n, and p_n (Theorem thm.sf.NG)
* Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)
* A polynomial is symmetric iff it is invariant under simple transpositions (Lemma lem.sf.simples-enough)

## References

* Source: SymmetricFunctions/Definitions.tex, sec.sf.sp

## Implementation notes

Mathlib already provides extensive support for symmetric polynomials via `MvPolynomial.IsSymmetric`
and related definitions. This file connects the textbook presentation to Mathlib's API
and provides additional lemmas following the source material.

The symmetric group action on polynomials is given by `MvPolynomial.rename` in Mathlib.
For a permutation σ : Equiv.Perm (Fin N), the action σ · f is `MvPolynomial.rename σ f`.
-/

open scoped Polynomial
open MvPolynomial Finset

namespace AlgebraicCombinatorics

namespace SymmetricPolynomials

variable {K : Type*} [CommRing K]
variable {N : ℕ}

/-!
## Convention (Convention conv.sf.KN)

We fix a commutative ring K and a natural number N throughout.
The polynomial ring P = K[x₁, x₂, ..., x_N] is `MvPolynomial (Fin N) K` in Mathlib.
-/

/-- The polynomial ring in N variables over K.
    This corresponds to 𝒫 in the source (Definition def.sf.PS (a)).
    Label: def.sf.PS -/
abbrev P (K : Type*) [CommRing K] (N : ℕ) : Type _ := MvPolynomial (Fin N) K

/-!
## The Symmetric Group Action (Definition def.sf.PS (b))

The symmetric group S_N acts on P by permuting variables:
  σ · f = f[x_{σ(1)}, x_{σ(2)}, ..., x_{σ(N)}]

In Mathlib, this is given by `MvPolynomial.rename σ f` where σ : Equiv.Perm (Fin N).
-/

/-- The action of a permutation on a polynomial by renaming variables.
    This is σ · f = f[x_{σ(1)}, ..., x_{σ(N)}] in the source.
    Label: def.sf.PS -/
noncomputable def permAction (σ : Equiv.Perm (Fin N)) (f : P K N) : P K N :=
  rename σ f

/-- Notation: σ • f for the permutation action -/
scoped notation:70 σ " •ₚ " f:70 => permAction σ f

/-!
## Proposition prop.sf.SN-acts: The action is a well-defined group action

(a) id · f = f for every f ∈ P
(b) (στ) · f = σ · (τ · f) for every σ, τ ∈ S_N and f ∈ P
-/

/-- The identity permutation acts trivially (Proposition prop.sf.SN-acts (a)).
    Label: prop.sf.SN-acts -/
theorem permAction_id (f : P K N) : (1 : Equiv.Perm (Fin N)) •ₚ f = f := by
  simp only [permAction, Equiv.Perm.coe_one, rename_id]
  rfl

/-- Composition of permutation actions (Proposition prop.sf.SN-acts (b)).
    Label: prop.sf.SN-acts -/
theorem permAction_mul (σ τ : Equiv.Perm (Fin N)) (f : P K N) :
    (σ * τ) •ₚ f = σ •ₚ (τ •ₚ f) := by
  simp only [permAction, rename_rename]
  rfl

/-- The symmetric group action on polynomials is a well-defined MulAction.
    This formalizes Proposition prop.sf.SN-acts in the standard Mathlib form:
    - `one_smul` corresponds to part (a): id · f = f
    - `mul_smul` corresponds to part (b): (στ) · f = σ · (τ · f)
    Label: prop.sf.SN-acts -/
noncomputable instance permMulAction : MulAction (Equiv.Perm (Fin N)) (P K N) where
  smul := permAction
  one_smul := permAction_id
  mul_smul σ τ f := by
    show permAction (σ * τ) f = permAction σ (permAction τ f)
    exact permAction_mul σ τ f

/-- The Mathlib smul action agrees with our permAction notation.
    Label: prop.sf.SN-acts -/
@[simp]
theorem smul_eq_permAction (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ • f = σ •ₚ f := rfl

/-!
## Definition of Symmetric Polynomials (Definition def.sf.PS (c)(d))

A polynomial f ∈ P is symmetric if σ · f = f for all σ ∈ S_N.
The set S of all symmetric polynomials is `symmetricSubalgebra (Fin N) K` in Mathlib.
-/

/-- A polynomial is symmetric if it is invariant under all permutations.
    This is Definition def.sf.PS (c) in the source.
    Label: def.sf.PS -/
def IsSymm (f : P K N) : Prop := f.IsSymmetric

/-- The ring of symmetric polynomials in N variables over K.

    This is the K-subalgebra S of P consisting of all symmetric polynomials,
    i.e., polynomials f such that σ · f = f for all permutations σ ∈ S_N.

    The terminology "ring of symmetric polynomials" comes from the fact that
    this subalgebra is closed under addition, multiplication, and scalar
    multiplication by elements of K (Theorem thm.sf.S-subalg).

    Label: def.sf.ring-of-symm -/
abbrev S (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  symmetricSubalgebra (Fin N) K

/-- Alternative name: the ring of symmetric polynomials.
    This is the standard terminology for the subalgebra S.
    Label: def.sf.ring-of-symm -/
abbrev ringOfSymmetricPolynomials (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  S K N

/-- The ring of symmetric polynomials is indeed a ring (a K-subalgebra of P).
    This follows from Mathlib's `symmetricSubalgebra` being a `Subalgebra`.
    Label: def.sf.ring-of-symm -/
noncomputable example : Ring (S K N) := inferInstance

/-- The ring of symmetric polynomials is a commutative ring.
    Label: def.sf.ring-of-symm -/
noncomputable example : CommRing (S K N) := inferInstance

/-- The ring of symmetric polynomials is a K-algebra.
    Label: def.sf.ring-of-symm -/
noncomputable example : Algebra K (S K N) := inferInstance

/-!
## Additional API for Definition def.sf.PS

These lemmas provide useful characterizations of the definitions.
-/

/-- The definition of IsSymm unfolds to: f is symmetric iff rename σ f = f for all σ.
    Label: def.sf.PS -/
theorem isSymm_def (f : P K N) : IsSymm f ↔ ∀ σ : Equiv.Perm (Fin N), rename σ f = f := Iff.rfl

/-- Membership in S is equivalent to being symmetric.
    Label: def.sf.PS -/
theorem mem_S_iff (f : P K N) : f ∈ S K N ↔ IsSymm f := mem_symmetricSubalgebra f

/-- The permutation action definition: σ •ₚ f = rename σ f.
    Label: def.sf.PS -/
theorem permAction_eq_rename (σ : Equiv.Perm (Fin N)) (f : P K N) : σ •ₚ f = rename σ f := rfl

/-- A polynomial is symmetric iff the permutation action fixes it.
    Label: def.sf.PS -/
theorem isSymm_iff_permAction (f : P K N) : IsSymm f ↔ ∀ σ : Equiv.Perm (Fin N), σ •ₚ f = f := by
  simp only [IsSymm, MvPolynomial.IsSymmetric, permAction_eq_rename]

/-- Example: The sum ∑ xᵢ is symmetric (Example exa.sf.PS1 (a)).
    Label: exa.sf.PS1 -/
theorem isSymm_sum_X : IsSymm (∑ i : Fin N, X i : P K N) := by
  intro σ
  simp only [map_sum, rename_X]
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- The polynomial ring P K N is a commutative K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isCommRing' : CommRing (P K N) := inferInstance

/-- The polynomial ring P K N is a K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isAlgebra' : Algebra K (P K N) := inferInstance

/-!
## Proposition prop.sf.SN-acts-by-alg-auts: The action is by K-algebra automorphisms

For each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism of P.
-/

/-- The permutation action preserves addition.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_add (σ : Equiv.Perm (Fin N)) (f g : P K N) :
    σ •ₚ (f + g) = σ •ₚ f + σ •ₚ g := by
  simp only [permAction, map_add]

/-- The permutation action preserves multiplication.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_mul' (σ : Equiv.Perm (Fin N)) (f g : P K N) :
    σ •ₚ (f * g) = (σ •ₚ f) * (σ •ₚ g) := by
  simp only [permAction, map_mul]

/-- The permutation action preserves scaling.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_smul (σ : Equiv.Perm (Fin N)) (c : K) (f : P K N) :
    σ •ₚ (c • f) = c • (σ •ₚ f) := by
  simp only [permAction, map_smul]

/-- The permutation action is invertible with inverse σ⁻¹.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_inv (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ⁻¹ •ₚ (σ •ₚ f) = f := by
  simp only [permAction, rename_rename, Equiv.Perm.inv_def, Equiv.symm_comp_self, rename_id]
  rfl

/-- The K-algebra automorphism of P induced by a permutation σ.
    This is the main object of Proposition prop.sf.SN-acts-by-alg-auts:
    for each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphism (σ : Equiv.Perm (Fin N)) : P K N ≃ₐ[K] P K N :=
  renameEquiv K σ

/-- The permutation action equals the automorphism applied to the polynomial.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_eq_permAutomorphism (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ •ₚ f = permAutomorphism σ f := rfl

/-- The permutation automorphism preserves zero.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_zero (σ : Equiv.Perm (Fin N)) :
    permAutomorphism σ (0 : P K N) = 0 :=
  map_zero (permAutomorphism σ)

/-- The permutation automorphism preserves one.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_one (σ : Equiv.Perm (Fin N)) :
    permAutomorphism σ (1 : P K N) = 1 :=
  map_one (permAutomorphism σ)

/-- The permutation automorphism preserves constants.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_C (σ : Equiv.Perm (Fin N)) (c : K) :
    permAutomorphism σ (C c : P K N) = C c :=
  rename_C σ c

/-- The identity permutation gives the identity automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_id :
    permAutomorphism (K := K) (N := N) (1 : Equiv.Perm (Fin N)) = AlgEquiv.refl :=
  renameEquiv_refl K

/-- Composition of permutation automorphisms: (σ * τ) acts as τ then σ.
    Note: In AlgEquiv, f * g = g.trans f (apply g first, then f).
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_mul_perm (σ τ : Equiv.Perm (Fin N)) :
    permAutomorphism (K := K) (σ * τ) = permAutomorphism σ * permAutomorphism τ := by
  ext f
  unfold permAutomorphism
  simp only [renameEquiv_apply, AlgEquiv.mul_apply, rename_rename]
  rfl

/-- The inverse automorphism is given by the inverse permutation.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_symm (σ : Equiv.Perm (Fin N)) :
    (permAutomorphism (K := K) σ).symm = permAutomorphism σ⁻¹ :=
  renameEquiv_symm K σ

/-- The permutation automorphism is bijective.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_bijective (σ : Equiv.Perm (Fin N)) :
    Function.Bijective (permAutomorphism (K := K) σ) :=
  AlgEquiv.bijective (permAutomorphism σ)

/-- The map from S_N to Aut_K(P) is a group homomorphism.
    This is the full content of Proposition prop.sf.SN-acts-by-alg-auts:
    S_N acts on P by K-algebra automorphisms.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphismHom :
    Equiv.Perm (Fin N) →* (P K N ≃ₐ[K] P K N) where
  toFun σ := permAutomorphism σ
  map_one' := permAutomorphism_id
  map_mul' σ τ := permAutomorphism_mul_perm σ τ

/-!
## Theorem thm.sf.S-subalg: S is a K-subalgebra of P

The set of symmetric polynomials is closed under addition, multiplication, and scaling,
and contains 0 and 1.

From the source (AlgebraicCombinatorics/tex/SymmetricFunctions/Definitions.tex, Theorem thm.sf.S-subalg):

> The subset S is a K-subalgebra of P.

A K-subalgebra of P must satisfy:
1. S contains 0 and 1
2. S is closed under addition
3. S is closed under multiplication
4. S is closed under scalar multiplication by elements of K

This section proves all these properties both in terms of `IsSymm` (the predicate)
and `∈ S K N` (membership in the subalgebra).
-/

/-- **Theorem thm.sf.S-subalg**: The symmetric polynomials form a K-subalgebra of P.

    This is the main theorem stating that the set S of symmetric polynomials is
    a K-subalgebra of the polynomial ring P = K[x₁, x₂, ..., x_N].

    A K-subalgebra satisfies:
    - (a) S contains 0 and 1 (see `S_zero_mem`, `S_one_mem`)
    - (b) S is closed under addition (see `S_add_mem`)
    - (c) S is closed under multiplication (see `S_mul_mem`)
    - (d) S is closed under scalar multiplication by K (see `S_smul_mem`)

    The definition `S K N := symmetricSubalgebra (Fin N) K` directly provides
    the `Subalgebra K (P K N)` structure, which bundles all these properties.

    Label: thm.sf.S-subalg -/
def S_subalgebra : Subalgebra K (P K N) := S K N

/-!
### Part (a): S contains 0 and 1
-/

/-- Zero is in S (Theorem thm.sf.S-subalg, part (a)).
    Label: thm.sf.S-subalg -/
theorem S_zero_mem : (0 : P K N) ∈ S K N := Subalgebra.zero_mem _

/-- One is in S (Theorem thm.sf.S-subalg, part (a)).
    Label: thm.sf.S-subalg -/
theorem S_one_mem : (1 : P K N) ∈ S K N := Subalgebra.one_mem _

/-- Zero is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_zero : IsSymm (0 : P K N) := MvPolynomial.IsSymmetric.zero

/-- One is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_one : IsSymm (1 : P K N) := MvPolynomial.IsSymmetric.one

/-- Constants are in S (Theorem thm.sf.S-subalg, part (a) generalized).
    Label: thm.sf.S-subalg -/
theorem S_C_mem (c : K) : (C c : P K N) ∈ S K N := Subalgebra.algebraMap_mem _ c

/-- Constants are symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_C (c : K) : IsSymm (C c : P K N) := MvPolynomial.IsSymmetric.C c

/-!
### Part (b): S is closed under addition
-/

/-- S is closed under addition (Theorem thm.sf.S-subalg, part (b)).
    Label: thm.sf.S-subalg -/
theorem S_add_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f + g ∈ S K N :=
  Subalgebra.add_mem _ hf hg

/-- Sum of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_add {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f + g) :=
  MvPolynomial.IsSymmetric.add hf hg

/-!
### Part (c): S is closed under multiplication
-/

/-- S is closed under multiplication (Theorem thm.sf.S-subalg, part (c)).
    Label: thm.sf.S-subalg -/
theorem S_mul_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f * g ∈ S K N :=
  Subalgebra.mul_mem _ hf hg

/-- Product of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_mul {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f * g) :=
  MvPolynomial.IsSymmetric.mul hf hg

/-!
### Part (d): S is closed under scalar multiplication
-/

/-- S is closed under scalar multiplication (Theorem thm.sf.S-subalg, part (d)).
    Label: thm.sf.S-subalg -/
theorem S_smul_mem (c : K) {f : P K N} (hf : f ∈ S K N) : c • f ∈ S K N :=
  Subalgebra.smul_mem _ hf c

/-- Scalar multiple of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_smul (c : K) {f : P K N} (hf : IsSymm f) : IsSymm (c • f) :=
  MvPolynomial.IsSymmetric.smul c hf

/-!
### Additional closure properties (consequences of being a K-subalgebra)

These properties follow automatically from S being a K-subalgebra.
-/

/-- S is closed under negation.
    Label: thm.sf.S-subalg -/
theorem S_neg_mem {f : P K N} (hf : f ∈ S K N) : -f ∈ S K N :=
  Subalgebra.neg_mem _ hf

/-- Negation of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_neg {f : P K N} (hf : IsSymm f) : IsSymm (-f) :=
  MvPolynomial.IsSymmetric.neg hf

/-- S is closed under subtraction.
    Label: thm.sf.S-subalg -/
theorem S_sub_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f - g ∈ S K N :=
  Subalgebra.sub_mem _ hf hg

/-- Difference of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_sub {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f - g) :=
  MvPolynomial.IsSymmetric.sub hf hg

/-- S is closed under powers.
    Label: thm.sf.S-subalg -/
theorem S_pow_mem {f : P K N} (hf : f ∈ S K N) (n : ℕ) : f ^ n ∈ S K N :=
  Subalgebra.pow_mem _ hf n

/-- Power of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_pow {f : P K N} (hf : IsSymm f) (n : ℕ) : IsSymm (f ^ n) := by
  intro σ
  rw [map_pow]
  rw [hf σ]

/-- S is closed under finite sums.
    Label: thm.sf.S-subalg -/
theorem S_sum_mem {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, f i ∈ S K N) : ∑ i ∈ s, f i ∈ S K N :=
  Subalgebra.sum_mem _ hf

/-- Finite sum of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_sum {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, IsSymm (f i)) : IsSymm (∑ i ∈ s, f i) := by
  intro σ
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi σ)

/-- S is closed under finite products.
    Label: thm.sf.S-subalg -/
theorem S_prod_mem {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, f i ∈ S K N) : ∏ i ∈ s, f i ∈ S K N :=
  Subalgebra.prod_mem _ hf

/-- Finite product of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_prod {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, IsSymm (f i)) : IsSymm (∏ i ∈ s, f i) := by
  intro σ
  simp only [map_prod]
  exact Finset.prod_congr rfl (fun i hi => hf i hi σ)

/-!
## Definition of Monomials (Definition def.sf.monomial)

(a) A monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N} with a_i ∈ ℕ
(b) The degree of a monomial is a₁ + a₂ + ⋯ + a_N
(c) A monomial is squarefree if all a_i ∈ {0, 1}
(d) A monomial is primal if at most one a_i > 0
-/

/-- A monomial represented by its exponent vector.
    In the textbook, a monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N}.
    We represent it by the exponent vector (a₁, a₂, ..., a_N) ∈ ℕ^N.
    Label: def.sf.monomial -/
abbrev Monomial (N : ℕ) := Fin N →₀ ℕ

/-- Convert a monomial (exponent vector) to the corresponding polynomial x₁^{a₁} ⋯ x_N^{a_N}.
    Label: def.sf.monomial -/
noncomputable def Monomial.toPoly (m : Monomial N) : P K N :=
  monomial m 1

/-- The degree of a monomial is the sum of its exponents.
    Label: def.sf.monomial -/
def Monomial.degree (m : Monomial N) : ℕ := m.sum (fun _ a => a)

/-- Alternative characterization: degree equals the support sum.
    Label: def.sf.monomial -/
theorem Monomial.degree_eq_support_sum (m : Monomial N) :
    m.degree = m.support.sum m := by
  simp only [degree, Finsupp.sum]

/-- A monomial is squarefree if all exponents are 0 or 1.
    Label: def.sf.monomial -/
def Monomial.IsSquarefree (m : Monomial N) : Prop := ∀ i, m i ≤ 1

/-- A monomial is primal if at most one exponent is positive.
    This means the monomial is either 1 or a power of a single variable.
    Label: def.sf.monomial -/
def Monomial.IsPrimal (m : Monomial N) : Prop := m.support.card ≤ 1

/-- The degree of a monomial equals the total degree of its polynomial representation
    (when K is nontrivial).
    Label: def.sf.monomial -/
theorem Monomial.degree_eq_totalDegree [Nontrivial K] (m : Monomial N) :
    m.degree = (m.toPoly : P K N).totalDegree := by
  unfold degree toPoly
  rw [totalDegree_monomial _ (one_ne_zero)]

/-- The set of all monomials of a given degree n.
    Label: def.sf.monomial -/
def monomialsOfDegree (N n : ℕ) : Set (Monomial N) :=
  {m | m.degree = n}

/-- The set of all squarefree monomials of a given degree n.
    Label: def.sf.monomial -/
def squarefreeMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsSquarefree ∧ m.degree = n}

/-- The set of all primal monomials of a given degree n.
    Label: def.sf.monomial -/
def primalMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsPrimal ∧ m.degree = n}

/-- The zero monomial (all exponents zero) represents 1.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.toPoly_zero : (0 : Monomial N).toPoly = (1 : P K N) := by
  simp only [toPoly, monomial_zero']
  rfl

/-- The degree of the zero monomial is 0.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_zero : (0 : Monomial N).degree = 0 := by
  simp only [degree, Finsupp.sum_zero_index]

/-- The zero monomial is squarefree.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_zero : (0 : Monomial N).IsSquarefree := by
  intro i
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.zero_le]

/-- The zero monomial is primal.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_zero : (0 : Monomial N).IsPrimal := by
  simp only [IsPrimal, Finsupp.support_zero, card_empty, Nat.zero_le]

/-- A single variable x_i corresponds to the monomial with exponent 1 at position i.
    Label: def.sf.monomial -/
noncomputable def Monomial.single (i : Fin N) : Monomial N := Finsupp.single i 1

/-- The polynomial corresponding to Monomial.single i is X i.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.toPoly_single (i : Fin N) :
    (Monomial.single i).toPoly = (X i : P K N) := by
  simp only [single, toPoly, MvPolynomial.X]

/-- The degree of a single variable monomial is 1.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_single (i : Fin N) : (Monomial.single i).degree = 1 := by
  simp only [single, degree, Finsupp.sum_single_index]

/-- A single variable monomial is squarefree.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_single (i : Fin N) : (Monomial.single i).IsSquarefree := by
  intro j
  simp only [single, Finsupp.single_apply]
  split_ifs <;> omega

/-- A single variable monomial is primal.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_single (i : Fin N) : (Monomial.single i).IsPrimal := by
  unfold IsPrimal single
  rw [Finsupp.support_single_ne_zero _ (one_ne_zero), card_singleton]

/-- Multiplication of monomials corresponds to addition of exponent vectors.
    Label: def.sf.monomial -/
theorem Monomial.toPoly_add (m₁ m₂ : Monomial N) :
    (m₁ + m₂).toPoly = (m₁.toPoly : P K N) * m₂.toPoly := by
  simp only [toPoly, monomial_mul, one_mul]

/-- The degree of a product of monomials is the sum of degrees.
    Label: def.sf.monomial -/
theorem Monomial.degree_add (m₁ m₂ : Monomial N) :
    (m₁ + m₂).degree = m₁.degree + m₂.degree := by
  simp only [degree]
  rw [Finsupp.sum_add_index']
  · intro _; rfl
  · intro _ _ _; ring

/-- A squarefree monomial has degree at most N.
    Label: def.sf.monomial -/
theorem Monomial.degree_le_of_isSquarefree (m : Monomial N) (hm : m.IsSquarefree) :
    m.degree ≤ N := by
  calc m.degree = m.support.sum m := m.degree_eq_support_sum
    _ ≤ m.support.sum (fun _ => 1) := Finset.sum_le_sum (fun i _ => hm i)
    _ = m.support.card := by simp
    _ ≤ Fintype.card (Fin N) := Finset.card_le_card (Finset.subset_univ _)
    _ = N := Fintype.card_fin N

/-- A primal monomial has support of size at most 1.
    Label: def.sf.monomial -/
theorem Monomial.support_card_le_one_of_isPrimal (m : Monomial N) (hm : m.IsPrimal) :
    m.support.card ≤ 1 := hm

/-- Characterization: a monomial is primal iff it's 0 or a power of a single variable.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_iff (m : Monomial N) :
    m.IsPrimal ↔ m = 0 ∨ ∃ i k, m = Finsupp.single i k ∧ 0 < k := by
  constructor
  · intro hm
    cases' Nat.lt_or_eq_of_le hm with h h
    · -- support is empty
      left
      simp only [Nat.lt_one_iff, Finset.card_eq_zero] at h
      exact Finsupp.support_eq_empty.mp h
    · -- support has exactly one element
      right
      rw [Finset.card_eq_one] at h
      obtain ⟨i, hi⟩ := h
      refine ⟨i, m i, ?_, ?_⟩
      · ext j
        simp only [Finsupp.single_apply]
        split_ifs with hji
        · rw [hji]
        · have : j ∉ m.support := by rw [hi]; simp only [mem_singleton]; exact fun h => hji h.symm
          simp only [Finsupp.mem_support_iff, not_not] at this
          exact this
      · have : i ∈ m.support := by rw [hi]; simp
        simp only [Finsupp.mem_support_iff] at this
        omega
  · intro h
    cases h with
    | inl h => rw [h]; exact Monomial.isPrimal_zero
    | inr h =>
      obtain ⟨i, k, rfl, hk⟩ := h
      unfold IsPrimal
      rw [Finsupp.support_single_ne_zero _ (Nat.pos_iff_ne_zero.mp hk), card_singleton]

/-- The monomial corresponding to a subset S ⊆ [N] is ∏_{i ∈ S} x_i.
    This is the squarefree monomial with support S.
    Label: def.sf.monomial -/
noncomputable def Monomial.ofFinset (s : Finset (Fin N)) : Monomial N :=
  s.sum (Finsupp.single · 1)

/-- The polynomial corresponding to Monomial.ofFinset s is ∏_{i ∈ s} X i.
    Label: def.sf.monomial -/
theorem Monomial.toPoly_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).toPoly = (∏ i ∈ s, X i : P K N) := by
  unfold ofFinset toPoly
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, monomial_zero']
    rfl
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem, Finset.prod_insert h_not_mem]
    show monomial (Finsupp.single a 1 + ∑ x ∈ s', Finsupp.single x 1) 1 = X a * ∏ x ∈ s', X x
    have eq1 : monomial (Finsupp.single a 1 + ∑ x ∈ s', Finsupp.single x 1) (1 : K) =
               monomial (Finsupp.single a 1) 1 * monomial (∑ x ∈ s', Finsupp.single x 1) 1 := by
      rw [monomial_mul, one_mul]
    rw [eq1, ih]
    rfl

/-- Monomial.ofFinset gives a squarefree monomial.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).IsSquarefree := by
  intro i
  simp only [ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with h
    · -- i = a (the inserted element)
      subst h
      have : (Finset.sum s' (fun x => Finsupp.single x 1)) a = 0 := by
        simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [ite_eq_right_iff, one_ne_zero]
        intro hja
        subst hja
        exact h_not_mem hj
      omega
    · -- i ≠ a
      have : Finsupp.single a 1 i = 0 := by simp [h]
      omega

/-- The degree of Monomial.ofFinset s is the cardinality of s.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).degree = s.card := by
  simp only [degree, ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index]
    rw [Finset.card_insert_of_notMem h_not_mem]
    omega

/-- The support of Monomial.ofFinset s equals s.
    Label: def.sf.monomial -/
theorem Monomial.support_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).support = s := by
  ext i
  simp only [Finsupp.mem_support_iff, ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem, Finset.mem_insert]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    constructor
    · intro h
      by_contra hni
      push_neg at hni
      have h1 : (if a = i then 1 else 0) = 0 := by simp only [ite_eq_right_iff, one_ne_zero]; exact fun h => (hni.1 h.symm).elim
      have h2 : (Finset.sum s' (fun x => Finsupp.single x 1)) i = 0 := by
        simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [ite_eq_right_iff, one_ne_zero]
        intro hji
        rw [hji] at hj
        exact hni.2 hj
      omega
    · intro h
      cases h with
      | inl h => simp [h]
      | inr h =>
        have : (Finset.sum s' (fun x => Finsupp.single x 1)) i ≠ 0 := by
          rw [ih]
          exact h
        omega

/-!
## Elementary Symmetric Polynomials (Definition def.sf.ehp (a))

e_n = sum of all squarefree monomials of degree n
    = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.esymm (Fin N) K n`.
-/

/-- The n-th elementary symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev e (n : ℕ) : P K N := esymm (Fin N) K n

/-- Elementary symmetric polynomials are symmetric.
    Label: def.sf.ehp -/
theorem e_isSymm (n : ℕ) : IsSymm (e (K := K) (N := N) n) := esymm_isSymmetric (Fin N) K n

/-!
## Complete Homogeneous Symmetric Polynomials (Definition def.sf.ehp (b))

h_n = sum of all monomials of degree n
    = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.hsymm (Fin N) K n`.
-/

section WithDecidableEq

variable [DecidableEq (Fin N)]

/-- The n-th complete homogeneous symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev h (n : ℕ) : P K N := hsymm (Fin N) K n

/-- Complete homogeneous symmetric polynomials are symmetric.
    Label: def.sf.ehp -/
theorem h_isSymm (n : ℕ) : IsSymm (h (K := K) (N := N) n) := hsymm_isSymmetric (Fin N) K n

/-- h_0 = 1 (Example exa.sf.ehp.1 (e)).
    Label: exa.sf.ehp.1 -/
theorem h_zero : h (K := K) (N := N) 0 = 1 := hsymm_zero (Fin N) K

/-- h_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem h_one : h (K := K) (N := N) 1 = ∑ i, X i := hsymm_one (Fin N) K

end WithDecidableEq

/-!
## Power Sums (Definition def.sf.ehp (c))

p_n = x₁^n + x₂^n + ... + x_N^n  (for n > 0)
p_0 = 1
p_n = 0  (for n < 0)

In Mathlib, this is `MvPolynomial.psum (Fin N) K n`.
Note: Mathlib's definition has p_0 = N (the number of variables), not 1.
-/

/-- The n-th power sum symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev p (n : ℕ) : P K N := psum (Fin N) K n

/-- Power sums are symmetric.
    Label: def.sf.ehp -/
theorem p_isSymm (n : ℕ) : IsSymm (p (K := K) (N := N) n) := psum_isSymmetric (Fin N) K n

/-!
## Basic Values (Example exa.sf.ehp.1)

(d) e_1 = h_1 = p_1 = x_1 + x_2 + ... + x_N
(e) e_0 = h_0 = 1, p_0 = N
(f) e_n = h_n = p_n = 0 for n < 0 (vacuously true for ℕ)
-/

/-- e_0 = 1 (Example exa.sf.ehp.1 (e)).
    Label: exa.sf.ehp.1 -/
theorem e_zero : e (K := K) (N := N) 0 = 1 := esymm_zero (Fin N) K

/-- p_0 = N (number of variables).
    Note: The source defines p_0 = 1, but Mathlib defines p_0 = N.
    Label: exa.sf.ehp.1 -/
theorem p_zero : p (K := K) (N := N) 0 = Fintype.card (Fin N) := psum_zero (Fin N) K

/-- e_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem e_one : e (K := K) (N := N) 1 = ∑ i, X i := esymm_one (Fin N) K

/-- p_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem p_one : p (K := K) (N := N) 1 = ∑ i, X i := psum_one (Fin N) K

/-!
## Integer-indexed versions (Definition def.sf.ehp)

The source defines e_n, h_n, p_n for all integers n ∈ ℤ.
For negative n, they are all 0. This section provides integer-indexed versions
that match the textbook definitions exactly.
-/

/-- Integer-indexed elementary symmetric polynomial.
    For n ∈ ℤ: e_n = esymm n if n ≥ 0, e_n = 0 if n < 0.
    This matches Definition def.sf.ehp (a) in the source.
    Label: def.sf.ehp -/
noncomputable def eZ (n : ℤ) : P K N :=
  if 0 ≤ n then e n.toNat else 0

/-- Integer-indexed complete homogeneous symmetric polynomial.
    For n ∈ ℤ: h_n = hsymm n if n ≥ 0, h_n = 0 if n < 0.
    This matches Definition def.sf.ehp (b) in the source.
    Label: def.sf.ehp -/
noncomputable def hZ [DecidableEq (Fin N)] (n : ℤ) : P K N :=
  if 0 ≤ n then h n.toNat else 0

/-- Integer-indexed power sum (textbook convention).
    For n ∈ ℤ: p'_n = psum n if n > 0, p'_0 = 1, p'_n = 0 if n < 0.
    This matches Definition def.sf.ehp (c) in the source.

    Note: Mathlib's psum has p_0 = N (number of variables), but the textbook
    defines p_0 = 1. We follow the textbook convention here.
    Label: def.sf.ehp -/
noncomputable def pZ (n : ℤ) : P K N :=
  if n > 0 then p n.toNat
  else if n = 0 then 1
  else 0

/-- e_n = 0 for negative n (Definition def.sf.ehp (a)).
    Label: def.sf.ehp -/
theorem eZ_neg {n : ℤ} (hn : n < 0) : eZ (K := K) (N := N) n = 0 := by
  simp only [eZ, not_le.mpr hn, ↓reduceIte]

/-- eZ agrees with e for non-negative integers.
    Label: def.sf.ehp -/
theorem eZ_of_nonneg {n : ℤ} (hn : 0 ≤ n) : eZ (K := K) (N := N) n = e n.toNat := by
  simp only [eZ, hn, ↓reduceIte]

/-- eZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem eZ_isSymmetric (n : ℤ) : (eZ (K := K) (N := N) n).IsSymmetric := by
  by_cases hn : 0 ≤ n
  · rw [eZ_of_nonneg hn]
    exact esymm_isSymmetric (Fin N) K n.toNat
  · rw [eZ_neg (not_le.mp hn)]
    exact IsSymmetric.zero

/-- h_n = 0 for negative n (Definition def.sf.ehp (b)).
    Label: def.sf.ehp -/
theorem hZ_neg [DecidableEq (Fin N)] {n : ℤ} (hn : n < 0) : hZ (K := K) (N := N) n = 0 := by
  simp only [hZ, not_le.mpr hn, ↓reduceIte]

/-- hZ agrees with h for non-negative integers.
    Label: def.sf.ehp -/
theorem hZ_of_nonneg [DecidableEq (Fin N)] {n : ℤ} (hn : 0 ≤ n) :
    hZ (K := K) (N := N) n = h n.toNat := by
  simp only [hZ, hn, ↓reduceIte]

/-- hZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem hZ_isSymmetric [DecidableEq (Fin N)] (n : ℤ) : (hZ (K := K) (N := N) n).IsSymmetric := by
  by_cases hn : 0 ≤ n
  · rw [hZ_of_nonneg hn]
    exact hsymm_isSymmetric (Fin N) K n.toNat
  · rw [hZ_neg (not_le.mp hn)]
    exact IsSymmetric.zero

/-- p'_n = 0 for negative n (Definition def.sf.ehp (c)).
    Label: def.sf.ehp -/
theorem pZ_neg {n : ℤ} (hn : n < 0) : pZ (K := K) (N := N) n = 0 := by
  simp only [pZ, not_lt.mpr (le_of_lt hn), ↓reduceIte, ne_of_lt hn]

/-- p'_0 = 1 (Definition def.sf.ehp (c)).
    Label: def.sf.ehp -/
theorem pZ_zero : pZ (K := K) (N := N) 0 = 1 := by
  simp only [pZ, lt_irrefl, ↓reduceIte]

/-- pZ agrees with psum for positive integers.
    Label: def.sf.ehp -/
theorem pZ_of_pos {n : ℤ} (hn : 0 < n) : pZ (K := K) (N := N) n = p n.toNat := by
  simp only [pZ, hn, ↓reduceIte]

/-- pZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem pZ_isSymmetric (n : ℤ) : (pZ (K := K) (N := N) n).IsSymmetric := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [pZ_neg hn]
    exact IsSymmetric.zero
  · rw [hn, pZ_zero]
    exact IsSymmetric.one
  · rw [pZ_of_pos hn]
    exact psum_isSymmetric (Fin N) K n.toNat

/-!
## Alternative characterizations (Definition def.sf.ehp)

The defining formulas for e_n, h_n, p_n as sums over tuples.
-/

/-- e_n is the sum over all n-element subsets of [N] of the product of variables.
    This is the defining formula in Definition def.sf.ehp (a):
    e_n = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}
    Label: def.sf.ehp -/
theorem e_eq_sum_prod_subsets (n : ℕ) :
    e (K := K) (N := N) n = ∑ s ∈ powersetCard n (univ : Finset (Fin N)), ∏ i ∈ s, X i := by
  rfl

section WithDecidableEq'

variable [DecidableEq (Fin N)]

/-- h_n is the sum over all symmetric n-tuples (multisets) of [N] of the product of variables.
    This is the defining formula in Definition def.sf.ehp (b):
    h_n = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}
    Label: def.sf.ehp -/
theorem h_eq_sum_prod_sym (n : ℕ) :
    h (K := K) (N := N) n = ∑ s : Sym (Fin N) n, (s.1.map X).prod := by
  rfl

end WithDecidableEq'

/-- p_n is the sum of n-th powers of all variables.
    This is the defining formula in Definition def.sf.ehp (c):
    p_n = x₁^n + x₂^n + ... + x_N^n
    Label: def.sf.ehp -/
theorem p_eq_sum_pow (n : ℕ) :
    p (K := K) (N := N) n = ∑ i : Fin N, X i ^ n := by
  rfl

/-!
## Proposition prop.sf.en=0: e_n = 0 for n > N

For n > N, there are no n distinct elements in [N], so e_n = 0.
-/

/-- e_n = 0 for n > N (Proposition prop.sf.en=0).
    Label: prop.sf.en=0 -/
theorem e_eq_zero_of_gt {n : ℕ} (hn : N < n) : e (K := K) (N := N) n = 0 := by
  simp only [e, esymm]
  apply Finset.sum_eq_zero
  intro s hs
  rw [mem_powersetCard] at hs
  have : #s ≤ Fintype.card (Fin N) := card_le_card hs.1
  simp only [Fintype.card_fin] at this
  omega

/-!
## Adding a Variable Recurrence

The elementary symmetric polynomial e_n(x₁,...,x_N,y) satisfies the recurrence:
  e_n(x₁,...,x_N,y) = e_n(x₁,...,x_N) + y * e_{n-1}(x₁,...,x_N)

This is fundamental for inductive proofs about symmetric polynomials.
-/

/-- Helper lemma: the image of a preimage under castSucc equals the original set
    when the set doesn't contain Fin.last N. -/
private lemma image_preimage_eq_of_not_mem_last {a : Finset (Fin (N + 1))} (hlast : Fin.last N ∉ a) :
    (a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc = a := by
  ext x; simp only [mem_image, mem_preimage]
  constructor
  · intro ⟨y, hy, hyx⟩; rwa [← hyx]
  · intro hx
    have hne : x ≠ Fin.last N := fun h => hlast (h ▸ hx)
    exact ⟨x.castPred hne, by simp [Fin.castSucc_castPred]; exact hx, Fin.castSucc_castPred x hne⟩

/-- Helper lemma: the image of a preimage of an erased set under castSucc equals the erased set. -/
private lemma image_preimage_erase_eq {a : Finset (Fin (N + 1))} :
    ((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc = a.erase (Fin.last N) := by
  ext x; simp only [mem_image, mem_preimage, mem_erase, ne_eq]
  constructor
  · intro ⟨y, hy, hyx⟩; rwa [← hyx]
  · intro ⟨hne, hx⟩
    refine ⟨x.castPred hne, ?_, Fin.castSucc_castPred x hne⟩
    simp only [Fin.castSucc_castPred]
    exact ⟨hne, hx⟩

/-- Adding a variable: e_{n+1}(x₁,...,x_N,y) = e_{n+1}(x₁,...,x_N) + y * e_n(x₁,...,x_N).
    This is the recurrence for computing elementary symmetric polynomials.
    Label: def.sf.ehp -/
theorem esymm_succ_add_var' (n : ℕ) :
    esymm (Fin (N + 1)) K (n + 1) = 
    rename Fin.castSucc (esymm (Fin N) K (n + 1)) + 
    X (Fin.last N) * rename Fin.castSucc (esymm (Fin N) K n) := by
  simp only [esymm, map_sum, map_prod, rename_X]
  have h_partition : (powersetCard (n + 1) (univ : Finset (Fin (N + 1)))) = 
      (powersetCard (n + 1) univ).filter (Fin.last N ∉ ·) ∪ 
      (powersetCard (n + 1) univ).filter (Fin.last N ∈ ·) := by
    ext s; simp only [mem_union, mem_filter]; tauto
  rw [h_partition, sum_union]
  · congr 1
    · -- First sum: subsets not containing Fin.last N
      refine Finset.sum_bij' 
        (fun a _ => a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
        (fun a _ => a.image Fin.castSucc)
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        obtain ⟨hcard, hlast⟩ := ha
        calc #(a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn) 
            = #((a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc) := by
                rw [card_image_of_injective _ (Fin.castSucc_injective N)]
            _ = #a := by rw [image_preimage_eq_of_not_mem_last hlast]
            _ = n + 1 := hcard
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_image] at ha ⊢
        constructor
        · rw [card_image_of_injective _ (Fin.castSucc_injective N)]; exact ha
        · intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        exact image_preimage_eq_of_not_mem_last ha.2
      · intro a _; ext x
        simp only [mem_preimage, mem_image, Fin.castSucc_inj]
        exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        conv_lhs => rw [← image_preimage_eq_of_not_mem_last ha.2, prod_image (Fin.castSucc_injective N).injOn]
    · -- Second sum: subsets containing Fin.last N
      rw [mul_sum]
      refine Finset.sum_bij' 
        (fun a _ => (a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
        (fun a _ => insert (Fin.last N) (a.image Fin.castSucc))
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        obtain ⟨hcard, hlast⟩ := ha
        have h_erase_card : #(a.erase (Fin.last N)) = n := by rw [card_erase_of_mem hlast]; omega
        calc #((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
            = #(((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc) := by
                rw [card_image_of_injective _ (Fin.castSucc_injective N)]
            _ = #(a.erase (Fin.last N)) := by rw [image_preimage_erase_eq]
            _ = n := h_erase_card
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        constructor
        · rw [card_insert_of_notMem]
          · rw [card_image_of_injective _ (Fin.castSucc_injective N)]; omega
          · simp only [mem_image]; intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
        · exact mem_insert_self _ _
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        obtain ⟨_, hlast⟩ := ha
        ext x; simp only [mem_insert, mem_image, mem_preimage, mem_erase, ne_eq]
        constructor
        · intro h
          rcases h with rfl | ⟨y, hy, hyx⟩
          · exact hlast
          · rw [← hyx]; exact hy.2
        · intro hx
          by_cases hne : x = Fin.last N
          · left; exact hne
          · right
            refine ⟨x.castPred hne, ?_, Fin.castSucc_castPred x hne⟩
            simp only [Fin.castSucc_castPred]
            exact ⟨hne, hx⟩
      · intro a _
        have h_erase : (insert (Fin.last N) (a.image Fin.castSucc)).erase (Fin.last N) = a.image Fin.castSucc := by
          apply erase_insert
          simp only [mem_image]; intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
        simp only [h_erase]
        ext x; simp only [mem_preimage, mem_image, Fin.castSucc_inj]
        constructor
        · intro ⟨y, hy, hyx⟩; rw [← hyx]; exact hy
        · intro hx; exact ⟨x, hx, rfl⟩
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        obtain ⟨_, hlast⟩ := ha
        conv_lhs => rw [← insert_erase hlast, prod_insert (notMem_erase _ _)]
        congr 1
        conv_lhs => rw [← image_preimage_erase_eq, prod_image (Fin.castSucc_injective N).injOn]
  · simp only [disjoint_filter]; intro s _ hs; simp [hs]

/-- Adding a variable: e_n(x₁,...,x_N,y) = e_n(x₁,...,x_N) + y * e_{n-1}(x₁,...,x_N).
    This is the recurrence for computing elementary symmetric polynomials.
    For n = 0, the second term vanishes since e_{-1} = 0 by convention (but Nat subtraction
    gives e_0 instead, so we use a conditional).
    Label: def.sf.ehp -/
theorem esymm_succ_add_var (n : ℕ) :
    esymm (Fin (N + 1)) K n = 
    rename Fin.castSucc (esymm (Fin N) K n) + 
    if n = 0 then 0 else X (Fin.last N) * rename Fin.castSucc (esymm (Fin N) K (n - 1)) := by
  cases n with
  | zero => simp only [esymm_zero, map_one, ↓reduceIte, add_zero]
  | succ n => simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]; exact esymm_succ_add_var' n

/-!
## Newton-Girard Formulas (Theorem thm.sf.NG)

For any positive integer n:
(eq.thm.sf.NG.eh) ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
(eq.thm.sf.NG.ep) ∑_{j=1}^n (-1)^{j-1} e_{n-j} p_j = n · e_n
(eq.thm.sf.NG.hp) ∑_{j=1}^n h_{n-j} p_j = n · h_n

These are implemented in Mathlib as `MvPolynomial.mul_esymm_eq_sum` and related theorems.
-/

/-- Newton-Girard formula: recurrence for elementary symmetric polynomials.
    k * e_k = (-1)^{k+1} * ∑_{a ∈ antidiagonal k, a.1 < k} (-1)^{a.1} * e_{a.1} * p_{a.2}
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.ep).
    Label: thm.sf.NG -/
theorem newtonGirard_esymm (k : ℕ) :
    (k : P K N) * e k = (-1 : P K N) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1 : P K N) ^ a.1 * e a.1 * p a.2 :=
  mul_esymm_eq_sum (Fin N) K k

/-- Newton-Girard formula: recurrence for power sums.
    p_k = (-1)^{k+1} * k * e_k - ∑_{a ∈ antidiagonal k, 0 < a.1 < k} (-1)^{a.1} * e_{a.1} * p_{a.2}
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.ep).
    Label: thm.sf.NG -/
theorem newtonGirard_psum (k : ℕ) (hk : 0 < k) :
    p (K := K) (N := N) k = (-1 : P K N) ^ (k + 1) * (k : P K N) * e k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k, (-1 : P K N) ^ a.fst * e a.1 * p a.2 :=
  psum_eq_mul_esymm_sub_sum (Fin N) K k hk

section WithDecidableEq'

variable [DecidableEq (Fin N)]

omit [DecidableEq (Fin N)] in
/-- Coefficient of (1 - X * C(x_i)) in power series.
    Helper lemma for Newton-Girard formula.
    Note: This lemma doesn't actually use DecidableEq (Fin N). -/
private lemma coeff_one_sub_X_mul_C (i : Fin N) (a : ℕ) :
    PowerSeries.coeff a (1 - PowerSeries.X * PowerSeries.C (X i : P K N)) =
    if a = 0 then 1 else if a = 1 then -(X i) else 0 := by
  simp only [map_sub, PowerSeries.coeff_one]
  cases a with
  | zero => simp
  | succ a =>
    simp only [if_neg (Nat.succ_ne_zero a)]
    cases a with
    | zero =>
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_X, PowerSeries.coeff_C]
      rw [show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by decide]
      simp only [Finset.sum_pair (by decide : (0, 1) ≠ (1, 0))]
      simp
    | succ a =>
      simp only [if_neg (by omega : a + 1 + 1 ≠ 1)]
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_X, PowerSeries.coeff_C]
      simp only [zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro ⟨k, l⟩ hkl
      simp only [Finset.mem_antidiagonal] at hkl
      by_cases hk1 : k = 1
      · subst hk1
        simp only [if_true, one_mul]
        have hl : l = a + 1 := by omega
        simp only [if_neg (by omega : l ≠ 0)]
      · simp only [if_neg hk1, zero_mul]

omit [DecidableEq (Fin N)] in
/-- Geometric series identity: (1 - t·x) * (∑_{k≥0} t^k x^k) = 1.
    This is the key lemma for the generating function proof of Newton-Girard. -/
lemma geom_series_mul_one_sub (i : Fin N) :
    (1 - PowerSeries.X * PowerSeries.C (X i : P K N)) *
    PowerSeries.mk (fun k => (X i : P K N) ^ k) = 1 := by
  ext n
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_one, PowerSeries.coeff_mk]
  cases n with
  | zero =>
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero, mul_one]
    simp [coeff_one_sub_X_mul_C]
  | succ n =>
    simp only [if_neg (Nat.succ_ne_zero n)]
    simp_rw [coeff_one_sub_X_mul_C]
    have h0 : (0, n + 1) ∈ Finset.antidiagonal (n + 1) := by simp [Finset.mem_antidiagonal]
    have h1 : (1, n) ∈ Finset.antidiagonal (n + 1) := by simp [Finset.mem_antidiagonal]; omega
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (n + 1)) (fun x => x.1 = 0)]
    have hfilt0 : Finset.filter (fun x => x.1 = 0) (Finset.antidiagonal (n + 1)) = {(0, n + 1)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.ext_iff]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
      · intro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
    rw [hfilt0, Finset.sum_singleton]
    simp only [if_true, one_mul]
    rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.filter (fun x => ¬x.1 = 0) (Finset.antidiagonal (n + 1))) (fun x => x.1 = 1)]
    have hfilt1 : Finset.filter (fun x => x.1 = 1)
        (Finset.filter (fun x => ¬x.1 = 0) (Finset.antidiagonal (n + 1))) = {(1, n)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.ext_iff]
      constructor
      · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, by omega⟩
      · intro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1⟩
    rw [hfilt1, Finset.sum_singleton]
    simp only [if_neg (by decide : (1 : ℕ) ≠ 0), if_true, neg_mul]
    have hrest : ∑ x ∈ Finset.filter (fun x => ¬x.1 = 1)
        (Finset.filter (fun x => ¬x.1 = 0) (Finset.antidiagonal (n + 1))),
        (if x.1 = 0 then 1 else if x.1 = 1 then -(X i : P K N) else 0) * (X i) ^ x.2 = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hx
      simp [hx.1.2, hx.2]
    rw [hrest, add_zero]
    ring_nf

omit [DecidableEq (Fin N)] in
/-- Product of geometric series equals 1 when multiplied by ∏(1 - t·x_i).
    This is the generating function identity E(t) * H(t) = 1. -/
lemma prod_geom_series_mul_prod_one_sub :
    (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) *
    (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp only [geom_series_mul_one_sub, Finset.prod_const_one]

omit [DecidableEq (Fin N)] in
/-- Helper: (-1)^j as a polynomial equals C((-1)^j).
    Used in coefficient extraction for Newton-Girard formula. -/
private lemma neg_one_pow_poly_eq_C (j : ℕ) :
    ((-1 : Polynomial (P K N)) ^ j) = Polynomial.C ((-1 : P K N) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_1]

omit [DecidableEq (Fin N)] in
/-- E(t) as PowerSeries equals E(t) as Polynomial coerced.
    This connects the polynomial generating function to power series. -/
private lemma E_powerseries_eq_poly_coe :
    (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N) : PowerSeries (P K N))) =
    ((∏ i : Fin N, ((1 - Polynomial.X * Polynomial.C (X i)) : Polynomial (P K N))) : PowerSeries (P K N)) := by
  simp_rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]

/-- Helper for esymm_genfunc: product of negations. -/
private lemma prod_neg_eq' {α R : Type*} [DecidableEq α] [CommRing R] (s : Finset α) (f : α → R) :
    ∏ i ∈ s, (-f i) = (-1 : R) ^ #s * ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp [prod_empty, pow_zero]
  | insert x s ha ih =>
    simp only [prod_insert ha, card_insert_eq_ite, if_neg ha, pow_succ]
    rw [ih]
    ring

/-- Generating function for elementary symmetric polynomials (Proposition prop.sf.e-h-FPS (a)).
    ∏_{i=1}^N (1 - t·x_i) = ∑_{n=0}^N (-1)^n t^n e_n
    This is placed here so it can be used in newtonGirard_eh.
    Label: prop.sf.e-h-FPS -/
theorem esymm_genfunc :
    ∏ i : Fin N, (1 - Polynomial.X * Polynomial.C (X i : P K N)) =
    ∑ n ∈ range (N + 1),
      (-1 : Polynomial (P K N)) ^ n * Polynomial.X ^ n * Polynomial.C (e (K := K) (N := N) n) := by
  -- Rewrite using prod_one_add with f i = -X * C(x_i)
  conv_lhs =>
    arg 2
    ext i
    rw [show (1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i) =
            1 + (-((Polynomial.X : Polynomial (P K N)) *
              Polynomial.C (X i : P K N))) by ring]
  rw [prod_one_add]
  -- Now we have: ∑ t ∈ powerset univ, ∏ i ∈ t, (-(X * C(x_i)))
  -- Use powerset_card_biUnion to group by cardinality
  rw [powerset_card_biUnion, sum_biUnion]
  · -- Now: ∑ k ∈ range (card univ + 1), ∑ t ∈ powersetCard k univ, ∏ i ∈ t, (-(X * C(x_i)))
    rw [show #(univ : Finset (Fin N)) = N by simp]
    apply sum_congr rfl
    intro k hk
    -- For each k, simplify the product
    have h1 : ∀ t ∈ powersetCard k (univ : Finset (Fin N)),
        ∏ i ∈ t, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
        (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (∏ i ∈ t, X i) := by
      intro t ht
      rw [mem_powersetCard] at ht
      rw [prod_neg_eq', ht.2]
      rw [prod_mul_distrib]
      rw [prod_const, ht.2]
      rw [map_prod]
      ring
    rw [sum_congr rfl h1]
    -- Factor out the constant terms
    simp_rw [← mul_sum]
    congr 1
    rw [← map_sum]
    -- Now we need: ∑ t ∈ powersetCard k univ, ∏ i ∈ t, x_i = e_k
    simp only [e, esymm]
  · -- Show the powersetCard sets are pairwise disjoint
    exact (pairwise_disjoint_powersetCard (univ : Finset (Fin N))).set_pairwise _

/-- Helper: product of powers equals multiset product.
    For s : Sym (Fin N) n, ∏ i, X_i^(count i s) = (s.1.map X).prod -/
private lemma prod_pow_count_eq_map_prod (n : ℕ) (s : Sym (Fin N) n) :
    ∏ i : Fin N, (X i : P K N) ^ (s : Multiset (Fin N)).count i = (s.1.map X).prod := by
  rw [prod_multiset_map_count]
  symm
  apply prod_subset
  · exact fun i _ => mem_univ i
  · intro i _ hi
    rw [Multiset.mem_toFinset] at hi
    rw [Multiset.count_eq_zero.mpr hi, pow_zero]

/-- Newton-Girard formula relating e and h: ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0 for n > 0.
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.eh).

    The proof uses the generating function identity:
    E(t) * H(t) = 1, where E(t) = ∏_i (1 - t·x_i) and H(t) = ∑_n t^n h_n.

    Since E(t) = ∑_n (-1)^n t^n e_n, the coefficient of t^n in E(t) * H(t) is:
    ∑_{j=0}^n (-1)^j e_j h_{n-j}

    For n > 0, this coefficient must be 0 (since E(t) * H(t) = 1).

    Label: thm.sf.NG -/
theorem newtonGirard_eh (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (n - j) = 0 := by
  -- The proof follows from the generating function identity E(t) * H(t) = 1.
  -- We have shown prod_geom_series_mul_prod_one_sub, which establishes this identity.
  -- The coefficient extraction argument shows that for n > 0:
  -- ∑_{j=0}^n (-1)^j e_j h_{n-j} = coeff n (E(t) * H(t)) = coeff n 1 = 0

  -- Helper: coefficient of t^j in E(t) = ∏_i (1 - t·x_i) is (-1)^j * e_j for j ≤ N, 0 otherwise
  have coeff_E : ∀ j : ℕ,
      PowerSeries.coeff j (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) =
      if j ≤ N then (-1 : P K N) ^ j * e (K := K) (N := N) j else 0 := by
    intro j
    -- Step 1: Convert PowerSeries product to Polynomial product
    let E_ps := ∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))
    let E_poly := ∏ i : Fin N, ((1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i))
    have h_eq : E_ps = (E_poly : PowerSeries (P K N)) := by
      simp only [E_ps, E_poly]
      conv_lhs =>
        arg 2
        ext i
        rw [← Polynomial.coe_one, ← Polynomial.coe_X, ← Polynomial.coe_C (X i),
            ← Polynomial.coe_mul, ← Polynomial.coe_sub]
      simp only [← Polynomial.coeToPowerSeries.ringHom_apply]
      rw [map_prod]
    change PowerSeries.coeff j E_ps = _
    rw [h_eq, Polynomial.coeff_coe]
    -- Step 2: Prove E_poly = ∑ k, (-1)^k * X^k * C(e_k) inline
    -- This is the content of esymm_genfunc
    have h_genfunc : E_poly = ∑ k ∈ range (N + 1),
        (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (e (K := K) (N := N) k) := by
      simp only [E_poly]
      -- Rewrite using prod_one_add with f i = -X * C(x_i)
      conv_lhs =>
        arg 2
        ext i
        rw [show (1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i) =
                1 + (-((Polynomial.X : Polynomial (P K N)) *
                  Polynomial.C (X i : P K N))) by ring]
      rw [prod_one_add]
      -- Use powerset_card_biUnion to group by cardinality
      rw [powerset_card_biUnion, sum_biUnion]
      · rw [show #(univ : Finset (Fin N)) = N by simp]
        apply sum_congr rfl
        intro k _
        have h1 : ∀ t ∈ powersetCard k (univ : Finset (Fin N)),
            ∏ i ∈ t, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
            (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (∏ i ∈ t, X i) := by
          intro t ht
          rw [mem_powersetCard] at ht
          have hprod_neg : ∀ (s : Finset (Fin N)), ∏ i ∈ s, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
              (-1 : Polynomial (P K N)) ^ #s * ∏ i ∈ s, (Polynomial.X * Polynomial.C (X i)) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp [prod_empty, pow_zero]
            | insert x s' ha ih =>
              simp only [prod_insert ha, card_insert_eq_ite, if_neg ha, pow_succ]
              rw [ih]
              ring
          rw [hprod_neg t, ht.2]
          rw [prod_mul_distrib]
          rw [prod_const, ht.2]
          rw [map_prod]
          ring
        rw [sum_congr rfl h1]
        simp_rw [← mul_sum]
        congr 1
        rw [← map_sum]
        simp only [e, esymm]
      · exact (pairwise_disjoint_powersetCard (univ : Finset (Fin N))).set_pairwise _
    show E_poly.coeff j = _
    rw [h_genfunc]
    -- Step 3: Extract coefficient from the sum
    rw [Polynomial.finset_sum_coeff]
    simp_rw [neg_one_pow_poly_eq_C]
    -- Step 4: Rearrange and extract coefficients
    conv_lhs =>
      arg 2
      ext n
      rw [show Polynomial.C ((-1 : P K N) ^ n) * Polynomial.X ^ n * Polynomial.C (e (K := K) (N := N) n) =
              Polynomial.X ^ n * Polynomial.C ((-1 : P K N) ^ n * e (K := K) (N := N) n) by
        rw [mul_comm (Polynomial.C _) (Polynomial.X ^ n), mul_assoc, ← Polynomial.C_mul]]
    simp only [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
    -- Step 5: Split based on whether j ≤ N
    split_ifs with h
    · -- j ≤ N: exactly one term contributes (n = j)
      rw [Finset.sum_eq_single j]
      · simp only [le_refl, if_true, Nat.sub_self, if_true]
      · intro k hk hkj
        simp only [Finset.mem_range] at hk
        by_cases hle : k ≤ j
        · simp only [hle, if_true]
          have hne : j - k ≠ 0 := by omega
          simp [hne]
        · simp [hle]
      · intro hj
        simp only [Finset.mem_range] at hj
        omega
    · -- j > N: no terms contribute
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      by_cases hle : k ≤ j
      · simp only [hle, if_true]
        by_cases hkj : k = j
        · subst hkj; omega
        · have hne : j - k ≠ 0 := by omega
          simp [hne]
      · simp [hle]


  -- Helper: coefficient of t^n in H_raw(t) = ∏_i (∑_k t^k x_i^k) is h_n
  have coeff_H : ∀ m : ℕ,
      PowerSeries.coeff m (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k)) =
      h (K := K) (N := N) m := by
    intro m
    -- Use the multinomial expansion via PowerSeries.coeff_prod
    rw [PowerSeries.coeff_prod]
    simp only [PowerSeries.coeff_mk]
    simp only [h, hsymm]
    -- Now: ∑ f ∈ finsuppAntidiag univ m, ∏ i, (X i)^(f i) = ∑ s : Sym (Fin N) m, (s.1.map X).prod
    -- Use Finset.sum_bij' with the bijection via Sym.equivNatSum
    refine Finset.sum_bij'
      -- Forward: f ↦ (Sym.equivNatSum).symm f
      (fun f hf => (Sym.equivNatSum (Fin N) m).symm ⟨f, by
        rw [Finset.mem_finsuppAntidiag'] at hf
        exact hf.1⟩)
      -- Backward: s ↦ (Sym.equivNatSum s).1
      (fun s _ => (Sym.equivNatSum (Fin N) m s).1)
      -- Forward lands in Finset.univ
      (fun f hf => Finset.mem_univ _)
      -- Backward lands in finsuppAntidiag
      (fun s _ => by
        rw [Finset.mem_finsuppAntidiag']
        constructor
        · exact (Sym.equivNatSum (Fin N) m s).2
        · exact Finset.subset_univ _)
      -- Round-trip 1
      (fun f hf => by simp)
      -- Round-trip 2
      (fun s hs => by simp)
      -- Values match
      (fun f hf => by
        have hf' : f.sum (fun _ => id) = m := by
          rw [Finset.mem_finsuppAntidiag'] at hf
          exact hf.1
        let s := (Sym.equivNatSum (Fin N) m).symm ⟨f, hf'⟩
        -- Show f i = (s : Multiset).count i
        have heq : ∀ i, f i = (s : Multiset (Fin N)).count i := by
          intro i
          simp only [s]
          rw [Sym.coe_equivNatSum_symm_apply]
          exact (Finsupp.count_toMultiset f i).symm
        simp_rw [heq]
        -- Use prod_pow_count_eq_map_prod
        exact prod_pow_count_eq_map_prod m s)

  -- Extract coefficient n from E * H = 1
  have h_prod := prod_geom_series_mul_prod_one_sub (K := K) (N := N)
  have h_coeff : PowerSeries.coeff n
      ((∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) *
       (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k))) =
      PowerSeries.coeff n (1 : PowerSeries (P K N)) := by rw [h_prod]
  simp only [PowerSeries.coeff_one, if_neg (ne_of_gt hn)] at h_coeff

  -- Use convolution formula
  rw [PowerSeries.coeff_mul] at h_coeff

  -- Substitute coefficient identities
  conv at h_coeff =>
    lhs
    arg 2
    ext p
    rw [coeff_E p.1, coeff_H p.2]

  -- Simplify: for j > N, e_j = 0, so we can drop the condition
  have h_simp : ∀ p ∈ Finset.antidiagonal n,
      (if p.1 ≤ N then (-1 : P K N) ^ p.1 * e (K := K) (N := N) p.1 else 0) * h (K := K) (N := N) p.2 =
      (-1 : P K N) ^ p.1 * e (K := K) (N := N) p.1 * h (K := K) (N := N) p.2 := by
    intro p _
    split_ifs with hle
    · ring
    · push_neg at hle
      have he0 : e (K := K) (N := N) p.1 = 0 := e_eq_zero_of_gt hle
      simp [he0]
  rw [Finset.sum_congr rfl h_simp] at h_coeff

  -- Convert antidiagonal sum to range sum
  have h_eq : ∑ j ∈ range (n + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (K := K) (N := N) (n - j) =
      ∑ x ∈ Finset.antidiagonal n, (-1 : P K N) ^ x.1 * e (K := K) (N := N) x.1 * h (K := K) (N := N) x.2 := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (-1 : P K N) ^ i * e (K := K) (N := N) i * h (K := K) (N := N) j)]
  rw [h_eq, h_coeff]

end WithDecidableEq'

end SymmetricPolynomials

end AlgebraicCombinatorics
