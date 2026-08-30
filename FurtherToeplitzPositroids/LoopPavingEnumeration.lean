import FurtherToeplitzPositroids.LatticePathFamilies

/-!
# Enumeration with fixed loop boundaries

This module formalizes Corollary 6.3 as a finite-set count.
-/

namespace FurtherToeplitzPositroids

noncomputable section

/-- The last element of a nonempty finite ordinal. -/
def lastLoopIndex (N : ℕ) (hN : 0 < N) : Fin N :=
  ⟨N - 1, by omega⟩

/-- Admissible consecutive-minor zero sets for fixed protected endpoints. -/
def admissibleLoopZeroSets (N : ℕ) (hN : 0 < N)
    (protectLeft protectRight : Bool) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powerset.filter fun Z ↦
    Z ≠ Finset.univ ∧
      (protectLeft = true → (⟨0, hN⟩ : Fin N) ∉ Z) ∧
      (protectRight = true → lastLoopIndex N hN ∉ Z)

theorem admissibleLoopZeroSets_none
    {N : ℕ} (hN : 0 < N) :
    admissibleLoopZeroSets N hN false false =
      (Finset.univ : Finset (Fin N)).powerset.erase Finset.univ := by
  ext Z
  simp [admissibleLoopZeroSets]

theorem admissibleLoopZeroSets_left
    {N : ℕ} (hN : 0 < N) :
    admissibleLoopZeroSets N hN true false =
      ((Finset.univ : Finset (Fin N)).erase ⟨0, hN⟩).powerset := by
  ext Z
  have hiff :
      (Z ≠ (Finset.univ : Finset (Fin N)) ∧ (⟨0, hN⟩ : Fin N) ∉ Z) ↔
        (⟨0, hN⟩ : Fin N) ∉ Z := by
    constructor
    · exact And.right
    · intro hzero
      refine ⟨?_, hzero⟩
      intro hZ
      subst Z
      exact hzero (Finset.mem_univ _)
  simpa [admissibleLoopZeroSets, Finset.subset_erase] using hiff

theorem admissibleLoopZeroSets_right
    {N : ℕ} (hN : 0 < N) :
    admissibleLoopZeroSets N hN false true =
      ((Finset.univ : Finset (Fin N)).erase (lastLoopIndex N hN)).powerset := by
  ext Z
  have hiff :
      (Z ≠ (Finset.univ : Finset (Fin N)) ∧ lastLoopIndex N hN ∉ Z) ↔
        lastLoopIndex N hN ∉ Z := by
    constructor
    · exact And.right
    · intro hlast
      refine ⟨?_, hlast⟩
      intro hZ
      subst Z
      exact hlast (Finset.mem_univ _)
  simpa [admissibleLoopZeroSets, Finset.subset_erase] using hiff

theorem admissibleLoopZeroSets_both
    {N : ℕ} (hN : 0 < N) :
    admissibleLoopZeroSets N hN true true =
      (((Finset.univ : Finset (Fin N)).erase ⟨0, hN⟩).erase
        (lastLoopIndex N hN)).powerset := by
  ext Z
  have hproper :
      (⟨0, hN⟩ : Fin N) ∉ Z → lastLoopIndex N hN ∉ Z →
        Z ≠ (Finset.univ : Finset (Fin N)) := by
    intro hzero _ hZ
    subst Z
    exact hzero (Finset.mem_univ _)
  simpa [admissibleLoopZeroSets, Finset.subset_erase] using hproper

/-- Corollary 6.3, no protected loop boundary. -/
theorem card_admissibleLoopZeroSets_none
    {N : ℕ} (hN : 0 < N) :
    (admissibleLoopZeroSets N hN false false).card = 2 ^ N - 1 := by
  rw [admissibleLoopZeroSets_none hN, Finset.card_erase_of_mem]
  · rw [Finset.card_powerset]
    simp
  · simp

/-- Corollary 6.3, exactly one protected loop boundary. -/
theorem card_admissibleLoopZeroSets_left
    {N : ℕ} (hN : 0 < N) :
    (admissibleLoopZeroSets N hN true false).card = 2 ^ (N - 1) := by
  rw [admissibleLoopZeroSets_left hN, Finset.card_powerset,
    Finset.card_erase_of_mem]
  · simp
  · simp

theorem card_admissibleLoopZeroSets_right
    {N : ℕ} (hN : 0 < N) :
    (admissibleLoopZeroSets N hN false true).card = 2 ^ (N - 1) := by
  rw [admissibleLoopZeroSets_right hN, Finset.card_powerset,
    Finset.card_erase_of_mem]
  · simp
  · simp

/-- Corollary 6.3, two distinct protected endpoints. -/
theorem card_admissibleLoopZeroSets_both_of_two_le
    {N : ℕ} (hN : 2 ≤ N) :
    (admissibleLoopZeroSets N (by omega) true true).card = 2 ^ (N - 2) := by
  rw [admissibleLoopZeroSets_both (by omega), Finset.card_powerset,
    Finset.card_erase_of_mem, Finset.card_erase_of_mem]
  · simp [Nat.sub_sub]
  · simp
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hEq
    have hval := congrArg Fin.val hEq
    simp [lastLoopIndex] at hval
    omega

/-- Corollary 6.3, coincident protected endpoints when `N=1`. -/
theorem card_admissibleLoopZeroSets_both_one :
    (admissibleLoopZeroSets 1 (by omega) true true).card = 1 := by
  rw [admissibleLoopZeroSets_both (by omega), Finset.card_powerset]
  norm_num [lastLoopIndex]

end

end FurtherToeplitzPositroids
