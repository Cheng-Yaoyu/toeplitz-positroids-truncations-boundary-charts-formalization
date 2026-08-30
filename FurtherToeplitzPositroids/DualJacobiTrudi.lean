import AlgebraicCombinatorics.Determinants.LGVCore
import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson

/-!
# The dual Jacobi--Trudi lattice model

This module builds the elementary-symmetric-function path model used in
equation (23).  East steps select distinct time levels, so a one-path weight
sum is an elementary symmetric polynomial.  The weighted LGV theorem then
turns determinants of these entries into nonintersecting path sums.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Finset Matrix MvPolynomial

noncomputable section

/-- The weight sum of paths with `n` east steps through `d` time levels is
the squarefree-monomial expansion of the elementary symmetric polynomial. -/
theorem pathWeightSum_elementary {K : Type*} [CommRing K]
    (d n : ℕ) (a : ℤ) (x : Fin d → K) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d x)
        (a, -a) (a + n, (d : ℤ) - a - n) =
      ∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin d)),
        ∏ i ∈ S, x i := by
  unfold LGV.pathWeightSum
  rw [← Finset.sum_attach]
  change (∑ p : (LGV.pathsFromTo LGV.integerLattice
      LGV.integerLattice_pathFinite
      (a, -a) (a + n, (d : ℤ) - a - n)),
        LGV.pathWeight (LGV.elementaryLatticeWeight d x) p.val) = _
  conv_rhs => rw [← Finset.sum_attach]
  change _ = ∑ S : (Finset.powersetCard n
      (Finset.univ : Finset (Fin d))), ∏ i ∈ S.val, x i
  let e := LGV.shiftedPathsEquivPowersetCard d n a
  apply Fintype.sum_equiv e
  intro p
  have hp := p.property
  simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq] at hp
  have hlen := LGV.shifted_path_length d n a p.val hp.1 hp.2
  rw [LGV.pathWeight_elementary_eq_prod_eastSteps d x p.val
    (by rw [hp.1]; simp) hlen]
  rw [← LGV.shiftedPathsEquivPowersetCard_apply_val d n a p hlen]

/-- Polynomial form of the preceding path enumeration. -/
theorem pathWeightSum_esymm {R : Type*} [CommRing R]
    (d n : ℕ) (a : ℤ) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        (a, -a) (a + n, (d : ℤ) - a - n) =
      MvPolynomial.esymm (Fin d) R n := by
  rw [pathWeightSum_elementary]
  rfl

/-- The integer-index extension of `e_n`, with negative indices set to zero. -/
noncomputable def elementarySymmetricExt (R : Type*) [CommRing R]
    (d : ℕ) (n : ℤ) : MvPolynomial (Fin d) R :=
  if 0 ≤ n then MvPolynomial.esymm (Fin d) R n.toNat else 0

/-- Entry formula for arbitrary integral horizontal displacement. -/
theorem pathWeightSum_esymmExt {R : Type*} [CommRing R]
    (d : ℕ) (a b : ℤ) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        (a, -a) (b, (d : ℤ) - b) =
      elementarySymmetricExt R d (b - a) := by
  unfold elementarySymmetricExt
  split_ifs with hnonneg
  · let n := (b - a).toNat
    have hba : b = a + n := by omega
    calc
      LGV.pathWeightSum LGV.integerLattice_pathFinite
          (LGV.elementaryLatticeWeight d X)
          (a, -a) (b, (d : ℤ) - b) =
          LGV.pathWeightSum LGV.integerLattice_pathFinite
            (LGV.elementaryLatticeWeight d X) (a, -a)
              (a + n, (d : ℤ) - a - n) := by
            congr 2 <;> omega
      _ = MvPolynomial.esymm (Fin d) R n :=
        pathWeightSum_esymm d n a
      _ = MvPolynomial.esymm (Fin d) R (b - a).toNat := rfl
  · have hba : b < a := by omega
    have hempty : LGV.pathsFromTo LGV.integerLattice
        LGV.integerLattice_pathFinite
        (a, -a) (b, (d : ℤ) - b) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hend : p.start = (a, -a) ∧
          p.finish = (b, (d : ℤ) - b) := by
        simpa only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq] using hp
      have hpos : 0 < p.vertices.length :=
        List.length_pos_of_ne_nil p.nonempty
      have hmono :=
        (LGV.integerLattice_path_vertices_bounded p 0 hpos).2.1
      have hzero : p.vertices.get ⟨0, hpos⟩ = p.start := by
        simp [LGV.SimpleDigraph.Path.start, List.head_eq_getElem]
      rw [hzero, hend.1, hend.2] at hmono
      omega
    unfold LGV.pathWeightSum
    simp [hempty]

/-! ## The dual Jacobi--Trudi path matrix -/

/-- Source vertices associated with the inner transpose partition. -/
def dualJacobiTrudiSources {k : ℕ} (muT : Fin k → ℕ) :
    LGV.kVertex (ℤ × ℤ) k := fun i =>
  let a := (muT i : ℤ) - i.val
  (a, -a)

/-- Target vertices associated with the outer transpose partition. -/
def dualJacobiTrudiTargets (d : ℕ) {k : ℕ} (lamt : Fin k → ℕ) :
    LGV.kVertex (ℤ × ℤ) k := fun i =>
  let b := (lamt i : ℤ) - i.val
  (b, (d : ℤ) - b)

/-- The elementary Jacobi--Trudi matrix, with negative indices extended by
zero. -/
noncomputable def dualJacobiTrudiMatrixE (R : Type*) [CommRing R]
    (d : ℕ) {k : ℕ} (lamt muT : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin d) R) :=
  Matrix.of fun i j => elementarySymmetricExt R d
    ((lamt i : ℤ) - (muT j : ℤ) - i.val + j.val)

theorem dualJacobiTrudiSources_xDecreasing {k : ℕ}
    {muT : Fin k → ℕ} (hmuT : Antitone muT) :
    LGV.xDecreasing (dualJacobiTrudiSources muT) := by
  intro i j hij
  simp only [dualJacobiTrudiSources, LGV.xCoord]
  have hm := hmuT hij
  push_cast
  omega

theorem dualJacobiTrudiSources_yIncreasing {k : ℕ}
    {muT : Fin k → ℕ} (hmuT : Antitone muT) :
    LGV.yIncreasing (dualJacobiTrudiSources muT) := by
  intro i j hij
  simp only [dualJacobiTrudiSources, LGV.yCoord]
  have hm := hmuT hij
  push_cast
  omega

theorem dualJacobiTrudiTargets_xDecreasing (d : ℕ) {k : ℕ}
    {lamt : Fin k → ℕ} (hlamt : Antitone lamt) :
    LGV.xDecreasing (dualJacobiTrudiTargets d lamt) := by
  intro i j hij
  simp only [dualJacobiTrudiTargets, LGV.xCoord]
  have hm := hlamt hij
  push_cast
  omega

theorem dualJacobiTrudiTargets_yIncreasing (d : ℕ) {k : ℕ}
    {lamt : Fin k → ℕ} (hlamt : Antitone lamt) :
    LGV.yIncreasing (dualJacobiTrudiTargets d lamt) := by
  intro i j hij
  simp only [dualJacobiTrudiTargets, LGV.yCoord]
  have hm := hlamt hij
  push_cast
  omega

/-- The LGV path-weight matrix is the transpose of the elementary
Jacobi--Trudi matrix. -/
theorem pathWeightMatrix_eq_dualJacobiTrudiMatrixE_transpose
    {R : Type*} [CommRing R] (d : ℕ) {k : ℕ}
    (lamt muT : Fin k → ℕ) :
    LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt) =
      (dualJacobiTrudiMatrixE R d lamt muT)ᵀ := by
  ext i j
  simp only [LGV.pathWeightMatrix, Matrix.of_apply, Matrix.transpose_apply,
    dualJacobiTrudiSources, dualJacobiTrudiTargets,
    dualJacobiTrudiMatrixE]
  rw [pathWeightSum_esymmExt]
  congr 2
  push_cast
  ring

/-- Weighted LGV form of the dual Jacobi--Trudi determinant. -/
theorem det_dualJacobiTrudiMatrixE_eq_nipatWeightSum
    {R : Type*} [CommRing R] (d : ℕ) {k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT) :
    (dualJacobiTrudiMatrixE R d lamt muT).det =
      LGV.nipatWeightSum LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt)
        (Equiv.refl (Fin k)) := by
  rw [← Matrix.det_transpose,
    ← pathWeightMatrix_eq_dualJacobiTrudiMatrixE_transpose d lamt muT]
  exact LGV.lgv_nonpermutable _ _ _
    (dualJacobiTrudiSources_xDecreasing hmuT)
    (dualJacobiTrudiSources_yIncreasing hmuT)
    (dualJacobiTrudiTargets_xDecreasing d hlamt)
    (dualJacobiTrudiTargets_yIncreasing d hlamt)

end

end FurtherToeplitzPositroids
