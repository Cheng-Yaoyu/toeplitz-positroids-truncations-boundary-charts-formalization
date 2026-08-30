import FurtherToeplitzPositroids.QuantumJacobian

/-!
# Local realization from an invertible boundary chart

This module isolates the analytic and positive-completion argument in
Theorem 5.6.  The root-of-unity work is reduced to constructing a chart with
the fields below.
-/

namespace FurtherToeplitzPositroids

open Filter Set Topology
open PavingToeplitzPositroids ToeplitzPositroids

noncomputable section

/-- A local consecutive-minor chart with the exact matrix hypotheses needed
by Lemma 2.1. -/
structure BoundaryLocalChart (p n N : ℕ) (hpn : p + 1 < n) where
  matrix : (Fin N → ℝ) → Matrix (Fin (p + 2)) (Fin n) ℝ
  phi : (Fin N → ℝ) → (Fin N → ℝ)
  base : Fin N → ℝ
  derivativeEquiv : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)
  hasStrictFDerivAt : HasStrictFDerivAt phi
    derivativeEquiv.toContinuousLinearMap base
  phi_base : phi base = 0
  sourceNeighborhood : Set (Fin N → ℝ)
  sourceNeighborhood_mem : sourceNeighborhood ∈ 𝓝 base
  lower_tn : ∀ x ∈ sourceNeighborhood, TNUpTo (matrix x) (p + 1)
  codimensionOne_independent : ∀ x ∈ sourceNeighborhood,
    ∀ cols : Fin (p + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (p + 1) ↦ (matrix x).col (cols j))
  consecutive_nonneg : ∀ x ∈ sourceNeighborhood,
    ∀ delta : Fin N → ℝ, phi x = delta →
      (∀ i, 0 ≤ delta i) →
      ∀ t : Fin (n - (p + 1)),
        0 ≤ matrixConsecutiveMinor hpn (matrix x) t
  stableProperty : (Fin N → ℝ) → Prop
  stable_on_neighborhood : ∀ x ∈ sourceNeighborhood, stableProperty x

/-- Theorem 5.6, abstract chart form.  Every sufficiently small nonnegative
target is realized by a totally nonnegative matrix while all strict support
properties encoded by `stableProperty` persist. -/
theorem BoundaryLocalChart.exists_local_realization
    {p n N : ℕ} {hpn : p + 1 < n}
    (C : BoundaryLocalChart p n N hpn) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin N → ℝ,
        (∀ i, 0 ≤ delta i ∧ delta i < eta) →
          ∃ x ∈ C.sourceNeighborhood,
            C.phi x = delta ∧
              TotallyNonnegative (C.matrix x) ∧ C.stableProperty x := by
  obtain ⟨eta, heta, hbox⟩ :=
    exists_local_preimage_nonnegative_box_zero C.hasStrictFDerivAt
      C.phi_base C.sourceNeighborhood_mem
  refine ⟨eta, heta, fun delta hdelta ↦ ?_⟩
  obtain ⟨x, hx, hphi⟩ := hbox delta hdelta
  have hconsecutive : ∀ t : Fin (n - (p + 1)),
      0 ≤ matrixConsecutiveMinor hpn (C.matrix x) t :=
    C.consecutive_nonneg x hx delta hphi (fun i ↦ (hdelta i).1)
  have htn : TotallyNonnegative (C.matrix x) :=
    positive_completion_totallyNonnegative hpn (C.lower_tn x hx)
      (C.codimensionOne_independent x hx) hconsecutive
  exact ⟨x, hx, hphi, htn, C.stable_on_neighborhood x hx⟩

end

end FurtherToeplitzPositroids
