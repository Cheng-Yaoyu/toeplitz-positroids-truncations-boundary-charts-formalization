import PavingToeplitzPositroids

/-!
# Common infrastructure for Paper C

This module reexports the checked Paper A and Paper B developments used by the
formalization of Paper C.
-/

namespace FurtherToeplitzPositroids

/-- The `i`-th value of an increasing finite selection is at least `i`. -/
theorem orderEmbedding_fin_val_lower_bound
    {r n : ℕ} (K : Fin r ↪o Fin n) (i : Fin r) :
    i.val ≤ (K i).val := by
  have aux : ∀ q : ℕ, ∀ j : Fin r, j.val = q → q ≤ (K j).val := by
    intro q
    induction q with
    | zero => intro j hj; omega
    | succ q ih =>
        intro j hj
        let pred : Fin r := ⟨q, by omega⟩
        have hpred : pred < j := by
          apply Fin.mk_lt_mk.mpr
          dsimp only [pred]
          omega
        have hstep := K.strictMono hpred
        have ihpred := ih pred rfl
        omega
  exact aux i.val i rfl

end FurtherToeplitzPositroids
