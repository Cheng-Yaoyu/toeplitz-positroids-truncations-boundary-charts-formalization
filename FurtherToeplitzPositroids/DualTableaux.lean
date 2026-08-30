import FurtherToeplitzPositroids.DualJacobiTrudi

/-!
# Nonintersecting elementary paths and column tableaux

This module develops the remaining combinatorial bridge in the dual
Jacobi--Trudi identity.  A path indexed by a column records the strictly
increasing entries in that column; nonintersection encodes weak increase
along rows.
-/

namespace FurtherToeplitzPositroids

open scoped BigOperators
open Finset Matrix MvPolynomial AlgebraicCombinatorics

noncomputable section

/-- The zero-based column presentation of a skew diagram. -/
def columnSkewDiagram {d k : ℕ} (lamt muT : Fin k → ℕ) :
    Set (Fin d × Fin k) :=
  {c | muT c.2 ≤ c.1.val ∧ c.1.val < lamt c.2}

/-- A filling of a skew diagram presented by its column heights. -/
def ColumnTableau (d : ℕ) {k : ℕ} (lamt muT : Fin k → ℕ) :=
  {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT} → Fin d

noncomputable instance columnSkewDiagramFintype {d k : ℕ}
    (lamt muT : Fin k → ℕ) :
    Fintype {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT} :=
  Fintype.ofFinite _

noncomputable instance columnTableauFintype {d k : ℕ}
    (lamt muT : Fin k → ℕ) : Fintype (ColumnTableau d lamt muT) := by
  letI := columnSkewDiagramFintype (d := d) lamt muT
  unfold ColumnTableau
  exact Fintype.ofFinite _

/-- Semistandardness in column coordinates: weak along rows and strict down
columns. -/
def IsColumnSemistandard {d k : ℕ} {lamt muT : Fin k → ℕ}
    (T : ColumnTableau d lamt muT) : Prop :=
  (∀ c₁ c₂, c₁.val.1 = c₂.val.1 →
      c₁.val.2 < c₂.val.2 → T c₁ ≤ T c₂) ∧
    (∀ c₁ c₂, c₁.val.2 = c₂.val.2 →
      c₁.val.1 < c₂.val.1 → T c₁ < T c₂)

/-- Semistandard fillings of the column presentation. -/
abbrev ColumnSSYT (d : ℕ) {k : ℕ} (lamt muT : Fin k → ℕ) :=
  {T : ColumnTableau d lamt muT // IsColumnSemistandard T}

noncomputable instance columnSSYTFintype {d k : ℕ}
    (lamt muT : Fin k → ℕ) : Fintype (ColumnSSYT d lamt muT) :=
  Fintype.ofFinite _

/-- The number of indices weakly below a given `Fin` index. -/
theorem card_filter_fin_le {n : ℕ} (i : Fin n) :
    (Finset.univ.filter fun r : Fin n => r ≤ i).card = i.val + 1 := by
  have heq : (Finset.univ.filter fun r : Fin n => r ≤ i) =
      Finset.Iic i := by
    ext r
    simp
  rw [heq, Fin.card_Iic]

/-- The box-membership equivalence for transpose partitions. -/
theorem transpose_box_equiv {d k : ℕ}
    {lam : Fin d → ℕ} {lamt : Fin k → ℕ}
    (hlam : Antitone lam) (hlamt : Antitone lamt)
    (htranspose : NPartition.IsTranspose lam lamt)
    (i : Fin d) (j : Fin k) :
    j.val + 1 ≤ lam i ↔ i.val + 1 ≤ lamt j := by
  constructor
  · intro hbox
    rw [htranspose.1 j]
    have hsubset : (Finset.univ.filter fun r : Fin d => r ≤ i) ⊆
        (Finset.univ.filter fun r : Fin d => j.val + 1 ≤ lam r) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hbox.trans (hlam hr)
    calc
      i.val + 1 = (Finset.univ.filter fun r : Fin d => r ≤ i).card :=
        (card_filter_fin_le i).symm
      _ ≤ (Finset.univ.filter fun r : Fin d =>
          j.val + 1 ≤ lam r).card := Finset.card_le_card hsubset
  · intro hbox
    rw [htranspose.2 i]
    have hsubset : (Finset.univ.filter fun c : Fin k => c ≤ j) ⊆
        (Finset.univ.filter fun c : Fin k => i.val + 1 ≤ lamt c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hbox.trans (hlamt hc)
    calc
      j.val + 1 = (Finset.univ.filter fun c : Fin k => c ≤ j).card :=
        (card_filter_fin_le j).symm
      _ ≤ (Finset.univ.filter fun c : Fin k =>
          i.val + 1 ≤ lamt c).card := Finset.card_le_card hsubset

/-- Membership in the column presentation is equivalent to membership in
the usual one-based skew Young diagram. -/
theorem mem_columnSkewDiagram_iff_mem_skewYoungDiagram
    {d k : ℕ} {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (r : Fin d) (c : Fin k) :
    (r, c) ∈ columnSkewDiagram lamt muT ↔
      (r, c.val + 1) ∈ skewYoungDiagram lam mu := by
  change (muT c ≤ r.val ∧ r.val < lamt c) ↔
    (mu r < c.val + 1 ∧ c.val + 1 ≤ lam r)
  have hLam := transpose_box_equiv hlam hlamt htransLam r c
  have hMu := transpose_box_equiv hmu hmuT htransMu r c
  omega

/-- Equivalence between zero-based column cells and the one-based cells used
by the Littlewood--Richardson tableau API. -/
def columnCellEquivSkew {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) :
    {z : Fin d × Fin k // z ∈ columnSkewDiagram lamt muT} ≃
      {z : Fin d × ℕ // z ∈ skewYoungDiagram lam mu} where
  toFun z := ⟨(z.val.1, z.val.2.val + 1),
    (mem_columnSkewDiagram_iff_mem_skewYoungDiagram
      hlam hmu hlamt hmuT htransLam htransMu z.val.1 z.val.2).mp
      z.property⟩
  invFun z :=
    let c : Fin k := ⟨z.val.2 - 1, by
      have hz := z.property
      change mu z.val.1 < z.val.2 ∧ z.val.2 ≤ lam z.val.1 at hz
      have hw := hwidth z.val.1
      omega⟩
    ⟨(z.val.1, c),
      (mem_columnSkewDiagram_iff_mem_skewYoungDiagram
        hlam hmu hlamt hmuT htransLam htransMu z.val.1 c).mpr (by
        have hz := z.property
        change mu z.val.1 < z.val.2 ∧ z.val.2 ≤ lam z.val.1 at hz
        change mu z.val.1 < c.val + 1 ∧ c.val + 1 ≤ lam z.val.1
        dsimp only [c]
        omega)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hz := z.property
      change mu z.val.1 < z.val.2 ∧ z.val.2 ≤ lam z.val.1 at hz
      simp
      omega

/-- Reindex column tableaux as ordinary skew tableaux. -/
def columnTableauEquivTableau {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) :
    ColumnTableau d lamt muT ≃ Tableau lam mu :=
  Equiv.arrowCongr
    (columnCellEquivSkew hlam hmu hlamt hmuT htransLam htransMu hwidth)
    (Equiv.refl (Fin d))

@[simp] theorem columnTableauEquivTableau_apply {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) (T : ColumnTableau d lamt muT)
    (z : {z : Fin d × ℕ // z ∈ skewYoungDiagram lam mu}) :
    columnTableauEquivTableau hlam hmu hlamt hmuT htransLam htransMu
        hwidth T z =
      T ((columnCellEquivSkew hlam hmu hlamt hmuT htransLam htransMu
        hwidth).symm z) := rfl

@[simp] theorem columnTableauEquivTableau_symm_apply {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) (T : Tableau lam mu)
    (z : {z : Fin d × Fin k // z ∈ columnSkewDiagram lamt muT}) :
    (columnTableauEquivTableau hlam hmu hlamt hmuT htransLam htransMu
        hwidth).symm T z =
      T (columnCellEquivSkew hlam hmu hlamt hmuT htransLam htransMu
        hwidth z) := rfl

/-- The cell reindexing preserves semistandardness. -/
theorem columnTableauEquivTableau_isSemistandard_iff {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) (T : ColumnTableau d lamt muT) :
    IsColumnSemistandard T ↔
      IsSemistandard (columnTableauEquivTableau hlam hmu hlamt hmuT
        htransLam htransMu hwidth T) := by
  let e := columnCellEquivSkew hlam hmu hlamt hmuT htransLam htransMu
    hwidth
  let E := columnTableauEquivTableau hlam hmu hlamt hmuT htransLam
    htransMu hwidth
  constructor
  · intro hT
    constructor
    · intro z₁ z₂ hrow hcol
      let c₁ := e.symm z₁
      let c₂ := e.symm z₂
      have he₁ := e.apply_symm_apply z₁
      have he₂ := e.apply_symm_apply z₂
      have hrow₁ : c₁.val.1 = z₁.val.1 := by
        have h := congrArg (fun z => z.val.1) he₁
        simpa only [e, columnCellEquivSkew] using h
      have hrow₂ : c₂.val.1 = z₂.val.1 := by
        have h := congrArg (fun z => z.val.1) he₂
        simpa only [e, columnCellEquivSkew] using h
      have hcol₁ : c₁.val.2.val + 1 = z₁.val.2 := by
        have h := congrArg (fun z => z.val.2) he₁
        simpa only [e, columnCellEquivSkew] using h
      have hcol₂ : c₂.val.2.val + 1 = z₂.val.2 := by
        have h := congrArg (fun z => z.val.2) he₂
        simpa only [e, columnCellEquivSkew] using h
      rw [columnTableauEquivTableau_apply,
        columnTableauEquivTableau_apply]
      apply hT.1 c₁ c₂
      · omega
      · apply Fin.mk_lt_mk.mpr
        omega
    · intro z₁ z₂ hcol hrow
      let c₁ := e.symm z₁
      let c₂ := e.symm z₂
      have he₁ := e.apply_symm_apply z₁
      have he₂ := e.apply_symm_apply z₂
      have hrow₁ : c₁.val.1 = z₁.val.1 := by
        have h := congrArg (fun z => z.val.1) he₁
        simpa only [e, columnCellEquivSkew] using h
      have hrow₂ : c₂.val.1 = z₂.val.1 := by
        have h := congrArg (fun z => z.val.1) he₂
        simpa only [e, columnCellEquivSkew] using h
      have hcol₁ : c₁.val.2.val + 1 = z₁.val.2 := by
        have h := congrArg (fun z => z.val.2) he₁
        simpa only [e, columnCellEquivSkew] using h
      have hcol₂ : c₂.val.2.val + 1 = z₂.val.2 := by
        have h := congrArg (fun z => z.val.2) he₂
        simpa only [e, columnCellEquivSkew] using h
      rw [columnTableauEquivTableau_apply,
        columnTableauEquivTableau_apply]
      apply hT.2 c₁ c₂
      · apply Fin.ext
        omega
      · apply Fin.mk_lt_mk.mpr
        omega
  · intro hT
    constructor
    · intro c₁ c₂ hrow hcol
      have hh := hT.1 (e c₁) (e c₂) hrow (by
        change c₁.val.2.val + 1 < c₂.val.2.val + 1
        exact Nat.add_lt_add_right (Fin.mk_lt_mk.mp hcol) 1)
      simpa only [E, e, columnTableauEquivTableau_apply,
        Equiv.symm_apply_apply] using hh
    · intro c₁ c₂ hcol hrow
      have hh := hT.2 (e c₁) (e c₂) (by
        change c₁.val.2.val + 1 = c₂.val.2.val + 1
        exact congrArg (fun z : Fin k => z.val + 1) hcol) hrow
      simpa only [E, e, columnTableauEquivTableau_apply,
        Equiv.symm_apply_apply] using hh

/-- Restriction of the cell reindexing to semistandard tableaux. -/
noncomputable def columnSSYTEquivSemistandardTableau {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k) :
    ColumnSSYT d lamt muT ≃
      {T : Tableau lam mu // IsSemistandard T} := by
  let E := columnTableauEquivTableau hlam hmu hlamt hmuT htransLam
    htransMu hwidth
  refine
    { toFun := fun T => ⟨E T.val,
        (columnTableauEquivTableau_isSemistandard_iff hlam hmu hlamt hmuT
          htransLam htransMu hwidth T.val).mp T.property⟩
      invFun := fun T => ⟨E.symm T.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (columnTableauEquivTableau_isSemistandard_iff
      hlam hmu hlamt hmuT htransLam htransMu hwidth (E.symm T.val)).mpr
    simpa only [E, Equiv.apply_symm_apply] using T.property
  · intro T
    apply Subtype.ext
    exact E.symm_apply_apply T.val
  · intro T
    apply Subtype.ext
    exact E.apply_symm_apply T.val

/-- The canonical semistandard column filling records the vertical rank of
each cell inside its skew column. -/
def canonicalColumnTableau {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hheight : ∀ c, lamt c - muT c ≤ d) :
    ColumnTableau d lamt muT := fun cell =>
  ⟨cell.val.1.val - muT cell.val.2, by
    have hc := cell.property
    change muT cell.val.2 ≤ cell.val.1.val ∧
      cell.val.1.val < lamt cell.val.2 at hc
    have hh := hheight cell.val.2
    omega⟩

theorem canonicalColumnTableau_isSemistandard
    {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hmuT : Antitone muT)
    (hheight : ∀ c, lamt c - muT c ≤ d) :
    IsColumnSemistandard (canonicalColumnTableau hheight) := by
  constructor
  · intro c₁ c₂ hrow hcol
    apply Fin.mk_le_mk.mpr
    have hm := hmuT hcol.le
    have hr := congrArg Fin.val hrow
    omega
  · intro c₁ c₂ hcol hrow
    apply Fin.mk_lt_mk.mpr
    change c₁.val.1.val - muT c₁.val.2 <
      c₂.val.1.val - muT c₂.val.2
    have hc := congrArg Fin.val hcol
    have hmu := congrArg muT hcol
    have hr := Fin.mk_lt_mk.mp hrow
    have hc₁ := c₁.property.1
    omega

/-- A skew shape whose columns have height at most `d` admits a
semistandard tableau using only the first `d` letters. -/
theorem exists_initial_semistandard_tableau_of_columnHeight
    {d s q : ℕ}
    {lam mu : Fin (d + s) → ℕ} {lamt muT : Fin q → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ q)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hcolumnHeight : ∀ c, lamt c - muT c ≤ d) :
    ∃ T : {T : Tableau lam mu // IsSemistandard T},
      ∀ z, (T.val z).val < d := by
  have hheightN : ∀ c, lamt c - muT c ≤ d + s := by
    intro c
    exact (hcolumnHeight c).trans (Nat.le_add_right d s)
  let C : ColumnTableau (d + s) lamt muT :=
    canonicalColumnTableau hheightN
  have hC : IsColumnSemistandard C :=
    canonicalColumnTableau_isSemistandard hmuT hheightN
  let e := columnSSYTEquivSemistandardTableau hlam hmu hlamt hmuT
    htransLam htransMu hwidth
  let T : {T : Tableau lam mu // IsSemistandard T} := e ⟨C, hC⟩
  refine ⟨T, ?_⟩
  intro z
  let c := (columnCellEquivSkew hlam hmu hlamt hmuT htransLam
    htransMu hwidth).symm z
  have hvalue : T.val z = C c := by
    rfl
  rw [hvalue]
  change c.val.1.val - muT c.val.2 < d
  have hc := c.property
  change muT c.val.2 ≤ c.val.1.val ∧
    c.val.1.val < lamt c.val.2 at hc
  have hh := hcolumnHeight c.val.2
  omega

/-- Two paths with the same shifted endpoints and the same east-step times
are equal. -/
theorem shiftedPath_eq_of_eastSteps (d n : ℕ) (a : ℤ)
    (p q : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hpStart : p.start = (a, -a))
    (hpFinish : p.finish = (a + n, (d : ℤ) - a - n))
    (hqStart : q.start = (a, -a))
    (hqFinish : q.finish = (a + n, (d : ℤ) - a - n))
    (hsteps : LGV.pathEastSteps d p
        (LGV.shifted_path_length d n a p hpStart hpFinish) =
      LGV.pathEastSteps d q
        (LGV.shifted_path_length d n a q hqStart hqFinish)) :
    p = q := by
  let ps : LGV.pathsFromTo LGV.integerLattice
      LGV.integerLattice_pathFinite
      (a, -a) (a + n, (d : ℤ) - a - n) :=
    ⟨p, by
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      exact ⟨hpStart, hpFinish⟩⟩
  let qs : LGV.pathsFromTo LGV.integerLattice
      LGV.integerLattice_pathFinite
      (a, -a) (a + n, (d : ℤ) - a - n) :=
    ⟨q, by
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      exact ⟨hqStart, hqFinish⟩⟩
  have hpApply := LGV.shiftedPathsEquivPowersetCard_apply_val d n a ps
    (LGV.shifted_path_length d n a p hpStart hpFinish)
  have hqApply := LGV.shiftedPathsEquivPowersetCard_apply_val d n a qs
    (LGV.shifted_path_length d n a q hqStart hqFinish)
  have heq : LGV.shiftedPathsEquivPowersetCard d n a ps =
      LGV.shiftedPathsEquivPowersetCard d n a qs := by
    apply Subtype.ext
    rw [hpApply, hqApply]
    exact hsteps
  have hpq := (LGV.shiftedPathsEquivPowersetCard d n a).injective heq
  exact congrArg Subtype.val hpq

/-- Exactly the entries preceding the `j`-th element of a sorted finset are
strictly smaller than that element. -/
theorem card_filter_val_lt_orderEmbOfFin {d n : ℕ}
    (S : Finset (Fin d)) (hcard : S.card = n) (j : Fin n) :
    (S.filter (fun z => z.val < (S.orderEmbOfFin hcard j).val)).card =
      j.val := by
  let f := S.orderEmbOfFin hcard
  have heq : S.filter (fun z => z.val < (f j).val) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => i < j)).image f := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro ⟨hzS, hzlt⟩
      have hzrange : z ∈ Set.range f := by
        rw [Finset.range_orderEmbOfFin]
        exact hzS
      obtain ⟨i, rfl⟩ := hzrange
      exact ⟨i, f.lt_iff_lt.mp hzlt, rfl⟩
    · rintro ⟨i, hij, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S hcard i,
        Fin.mk_lt_mk.mp (f.strictMono hij)⟩
  rw [heq, Finset.card_image_of_injective _ f.injective]
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun i => i < j) =
      Finset.Iio j := by
    ext i
    simp
  rw [hfilter, Fin.card_Iio]

/-- Including the `j`-th sorted element raises the preceding count to
`j+1`. -/
theorem card_filter_val_lt_succ_orderEmbOfFin {d n : ℕ}
    (S : Finset (Fin d)) (hcard : S.card = n) (j : Fin n) :
    (S.filter (fun z => z.val < (S.orderEmbOfFin hcard j).val + 1)).card =
      j.val + 1 := by
  have heq : S.filter (fun z => z.val <
        (S.orderEmbOfFin hcard j).val + 1) =
      insert (S.orderEmbOfFin hcard j)
        (S.filter (fun z => z.val < (S.orderEmbOfFin hcard j).val)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro ⟨hzS, hz⟩
      by_cases heq : z = S.orderEmbOfFin hcard j
      · exact Or.inl heq
      · exact Or.inr ⟨hzS, by
          apply Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hz)
          exact fun h => heq (Fin.ext h)⟩
    · rintro (rfl | ⟨hzS, hz⟩)
      · exact ⟨Finset.orderEmbOfFin_mem S hcard j,
          Nat.lt_succ_self _⟩
      · exact ⟨hzS, Nat.lt_succ_of_lt hz⟩
  rw [heq, Finset.card_insert_of_notMem]
  · rw [card_filter_val_lt_orderEmbOfFin]
  · simp

/-- The first sorted element not counted below a threshold is at least that
threshold. -/
theorem le_orderEmbOfFin_of_card_filter_val_lt {d n t : ℕ}
    (S : Finset (Fin d)) (hcard : S.card = n) (q : Fin n)
    (hcount : (S.filter (fun z => z.val < t)).card = q.val) :
    t ≤ (S.orderEmbOfFin hcard q).val := by
  by_contra hlt
  push_neg at hlt
  have hsubset : S.filter (fun z => z.val <
        (S.orderEmbOfFin hcard q).val + 1) ⊆
      S.filter (fun z => z.val < t) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, by omega⟩
  have hc := Finset.card_le_card hsubset
  rw [card_filter_val_lt_succ_orderEmbOfFin S hcard q, hcount] at hc
  omega

/-- Every sorted position strictly before the threshold count has value below
the threshold. -/
theorem orderEmbOfFin_lt_of_lt_card_filter_val {d n t : ℕ}
    (S : Finset (Fin d)) (hcard : S.card = n) (q : Fin n)
    (hq : q.val < (S.filter (fun z => z.val < t)).card) :
    (S.orderEmbOfFin hcard q).val < t := by
  by_contra hle
  push_neg at hle
  have hsubset : S.filter (fun z => z.val < t) ⊆
      S.filter (fun z => z.val < (S.orderEmbOfFin hcard q).val) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, by omega⟩
  have hc := Finset.card_le_card hsubset
  rw [card_filter_val_lt_orderEmbOfFin S hcard q] at hc
  omega

/-- Every component path in the dual Jacobi--Trudi family has one vertex at
each of the `d+1` time levels. -/
theorem dualPathTuple_path_length {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (c : Fin k) :
    (pt.paths c).vertices.length = d + 1 := by
  have h := LGV.integerLattice_path_length_eq (pt.paths c)
  rw [pt.starts c, pt.finishes c] at h
  simp only [dualJacobiTrudiSources, dualJacobiTrudiTargets] at h
  omega

/-- The east-step set in column `c` has the number of elements prescribed by
the skew column height. -/
theorem dualPathTuple_eastSteps_card {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (c : Fin k) :
    (LGV.pathEastSteps d (pt.paths c)
      (dualPathTuple_path_length pt c)).card = lamt c - muT c := by
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  have hc := hcontained c
  have htarget : ((lamt c : ℤ) - c.val,
        (d : ℤ) - ((lamt c : ℤ) - c.val)) =
      (a + n, (d : ℤ) - a - n) := by
    dsimp only [a, n]
    ext <;> push_cast <;> omega
  let p : LGV.pathsFromTo LGV.integerLattice
      LGV.integerLattice_pathFinite
      (a, -a) (a + n, (d : ℤ) - a - n) :=
    ⟨pt.paths c, by
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      constructor
      · simpa only [a, dualJacobiTrudiSources] using pt.starts c
      · rw [← htarget]
        simpa only [dualJacobiTrudiTargets] using pt.finishes c⟩
  have hp := (LGV.shiftedPathsEquivPowersetCard d n a p).property
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hp
  have happly := LGV.shiftedPathsEquivPowersetCard_apply_val d n a p
    (dualPathTuple_path_length pt c)
  rw [happly] at hp
  exact hp.trans (by rfl)

/-- Read the increasing list of east-step times in each path as the entries
of the corresponding skew-diagram column. -/
noncomputable def pathTupleToColumnTableau {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt)) :
    ColumnTableau d lamt muT := fun cell =>
  let c := cell.val.2
  let S := LGV.pathEastSteps d (pt.paths c)
    (dualPathTuple_path_length pt c)
  let hcard : S.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained pt c
  let rank : Fin (lamt c - muT c) :=
    ⟨cell.val.1.val - muT c, by
      have hc := cell.property
      change muT c ≤ cell.val.1.val ∧
        cell.val.1.val < lamt c at hc
      omega⟩
  S.orderEmbOfFin hcard rank

/-- Entries read from a single path are strictly increasing down their
column. -/
theorem pathTupleToColumnTableau_columnStrict {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (c₁ c₂ : {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT})
    (hcol : c₁.val.2 = c₂.val.2) (hrow : c₁.val.1 < c₂.val.1) :
    pathTupleToColumnTableau hcontained pt c₁ <
      pathTupleToColumnTableau hcontained pt c₂ := by
  rcases c₁ with ⟨⟨r₁, c₁⟩, hc₁⟩
  rcases c₂ with ⟨⟨r₂, c₂⟩, hc₂⟩
  simp only at hcol
  subst c₂
  simp only [pathTupleToColumnTableau]
  apply (Finset.orderEmbOfFin _ _).strictMono
  apply Fin.mk_lt_mk.mpr
  exact Nat.sub_lt_sub_right
    (show muT c₁ ≤ r₁.val by exact hc₁.1)
    (Fin.mk_lt_mk.mp hrow)

/-- Immediately after the east step encoding a cell, the path has the
shape-determined horizontal coordinate `row-column+1`. -/
theorem dualPathTuple_x_after_cell {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (cell : {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT}) :
    let t := (pathTupleToColumnTableau hcontained pt cell).val + 1
    ((pt.paths cell.val.2).vertices.get ⟨t, by
      have ht := (pathTupleToColumnTableau hcontained pt cell).isLt
      rw [dualPathTuple_path_length pt cell.val.2]
      omega⟩).1 =
      (cell.val.1.val : ℤ) - cell.val.2.val + 1 := by
  let c := cell.val.2
  let S := LGV.pathEastSteps d (pt.paths c)
    (dualPathTuple_path_length pt c)
  let hcard : S.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained pt c
  let rank : Fin (lamt c - muT c) :=
    ⟨cell.val.1.val - muT c, by
      have hc := cell.property
      change muT c ≤ cell.val.1.val ∧
        cell.val.1.val < lamt c at hc
      omega⟩
  have hentry : pathTupleToColumnTableau hcontained pt cell =
      S.orderEmbOfFin hcard rank := rfl
  have hstart : (pt.paths c).start.1 + (pt.paths c).start.2 = 0 := by
    rw [pt.starts c]
    simp [dualJacobiTrudiSources]
  have hx := LGV.path_x_coord_eq_start_add_card_eastSteps d
    (pt.paths c) hstart (dualPathTuple_path_length pt c)
    ((pathTupleToColumnTableau hcontained pt cell).val + 1) (by
      rw [dualPathTuple_path_length pt c]
      exact Nat.succ_lt_succ
        (pathTupleToColumnTableau hcontained pt cell).isLt)
  have hcount := card_filter_val_lt_succ_orderEmbOfFin S hcard rank
  rw [hentry] at hx
  change ((S.filter (fun i => i.val <
    (S.orderEmbOfFin hcard rank).val + 1)).card) = rank.val + 1 at hcount
  rw [hcount] at hx
  rw [pt.starts c] at hx
  simp only [dualJacobiTrudiSources] at hx
  have hcval : c.val = cell.val.2.val := rfl
  have hmuEq : muT c = muT cell.val.2 := rfl
  have hcell := cell.property
  change muT cell.val.2 ≤ cell.val.1.val ∧
    cell.val.1.val < lamt cell.val.2 at hcell
  have hcast : ((cell.val.1.val - muT cell.val.2 : ℕ) : ℤ) =
      (cell.val.1.val : ℤ) - muT cell.val.2 := by
    rw [Nat.cast_sub hcell.1]
  dsimp only
  convert hx using 1 <;>
    dsimp only [c, S, rank] at * <;>
    simp only [hentry, Fin.val_cast] at * <;>
    push_cast at * <;>
    omega

/-- Before the east step encoding a cell, the path lies weakly to the left
of the coordinate immediately preceding that cell. -/
theorem dualPathTuple_x_before_cell {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (cell : {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT})
    (t : ℕ) (ht : t ≤ (pathTupleToColumnTableau hcontained pt cell).val) :
    ((pt.paths cell.val.2).vertices.get ⟨t, by
      rw [dualPathTuple_path_length pt cell.val.2]
      have he := (pathTupleToColumnTableau hcontained pt cell).isLt
      omega⟩).1 ≤
      (cell.val.1.val : ℤ) - cell.val.2.val := by
  let c := cell.val.2
  let S := LGV.pathEastSteps d (pt.paths c)
    (dualPathTuple_path_length pt c)
  let hcard : S.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained pt c
  let rank : Fin (lamt c - muT c) :=
    ⟨cell.val.1.val - muT c, by
      have hc := cell.property
      change muT c ≤ cell.val.1.val ∧
        cell.val.1.val < lamt c at hc
      omega⟩
  have hentry : pathTupleToColumnTableau hcontained pt cell =
      S.orderEmbOfFin hcard rank := rfl
  have hstart : (pt.paths c).start.1 + (pt.paths c).start.2 = 0 := by
    rw [pt.starts c]
    simp [dualJacobiTrudiSources]
  have hx := LGV.path_x_coord_eq_start_add_card_eastSteps d
    (pt.paths c) hstart (dualPathTuple_path_length pt c) t (by
      rw [dualPathTuple_path_length pt c]
      have he := (pathTupleToColumnTableau hcontained pt cell).isLt
      omega)
  have hsubset : (S.filter (fun i => i.val < t)) ⊆
      S.filter (fun i => i.val < (S.orderEmbOfFin hcard rank).val) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rw [← hentry]
    omega
  have hcount := Finset.card_le_card hsubset
  rw [card_filter_val_lt_orderEmbOfFin S hcard rank] at hcount
  rw [pt.starts c] at hx
  simp only [dualJacobiTrudiSources] at hx
  dsimp only [c, S, rank] at hx hcount ⊢
  push_cast at hx
  have hcell := cell.property
  change muT cell.val.2 ≤ cell.val.1.val ∧
    cell.val.1.val < lamt cell.val.2 at hcell
  have hcountZ :
      (((LGV.pathEastSteps d (pt.paths cell.val.2)
          (dualPathTuple_path_length pt cell.val.2)).filter
        (fun i => i.val < t)).card : ℤ) ≤
        (cell.val.1.val : ℤ) - muT cell.val.2 := by
    rw [← Nat.cast_sub hcell.1]
    exact_mod_cast hcount
  omega

/-- Nonintersection forces weak increase across two adjacent occupied cells
in the same row. -/
theorem pathTupleToColumnTableau_rowWeak_adjacent {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (hnipat : pt.isNonIntersecting)
    (left right : {c : Fin d × Fin k //
      c ∈ columnSkewDiagram lamt muT})
    (hrow : left.val.1 = right.val.1)
    (hadj : right.val.2.val = left.val.2.val + 1) :
    pathTupleToColumnTableau hcontained pt left ≤
      pathTupleToColumnTableau hcontained pt right := by
  have hcolLt : left.val.2 < right.val.2 := by
    apply Fin.mk_lt_mk.mpr
    rw [hadj]
    exact Nat.lt_succ_self _
  have hcolLe : left.val.2 ≤ right.val.2 := hcolLt.le
  by_contra hle
  push_neg at hle
  have hentry : pathTupleToColumnTableau hcontained pt right <
      pathTupleToColumnTableau hcontained pt left := hle
  let t := (pathTupleToColumnTableau hcontained pt right).val + 1
  have htLeft : t ≤
      (pathTupleToColumnTableau hcontained pt left).val := by
    dsimp only [t]
    exact Fin.mk_lt_mk.mp hentry
  have htD : t < d + 1 := by
    dsimp only [t]
    exact Nat.succ_lt_succ
      (pathTupleToColumnTableau hcontained pt right).isLt
  have htLeftPath : t < (pt.paths left.val.2).vertices.length := by
    rw [dualPathTuple_path_length pt left.val.2]
    exact htD
  have htRightPath : t < (pt.paths right.val.2).vertices.length := by
    rw [dualPathTuple_path_length pt right.val.2]
    exact htD
  have hxLeft := dualPathTuple_x_before_cell hcontained pt left t htLeft
  have hxRight := dualPathTuple_x_after_cell hcontained pt right
  dsimp only at hxRight
  have hxEnd :
      ((pt.paths left.val.2).vertices.get ⟨t, htLeftPath⟩).1 ≤
        ((pt.paths right.val.2).vertices.get ⟨t, htRightPath⟩).1 := by
    rw [hxRight]
    rw [hrow] at hxLeft
    push_cast
    omega
  let pLeft := (pt.paths left.val.2).subpath 0 t (Nat.zero_le t)
    htLeftPath
  let pRight := (pt.paths right.val.2).subpath 0 t (Nat.zero_le t)
    htRightPath
  have hpLeftStart : pLeft.start = (pt.paths left.val.2).start := by
    rw [show pLeft.start =
        (pt.paths left.val.2).vertices.get ⟨0,
          Nat.lt_of_le_of_lt (Nat.zero_le t) htLeftPath⟩ by
      exact LGV.SimpleDigraph.Path.subpath_start _ _ _ _ _]
    simp [LGV.SimpleDigraph.Path.start, List.head_eq_getElem]
  have hpRightStart : pRight.start = (pt.paths right.val.2).start := by
    rw [show pRight.start =
        (pt.paths right.val.2).vertices.get ⟨0,
          Nat.lt_of_le_of_lt (Nat.zero_le t) htRightPath⟩ by
      exact LGV.SimpleDigraph.Path.subpath_start _ _ _ _ _]
    simp [LGV.SimpleDigraph.Path.start, List.head_eq_getElem]
  have hpLeftFinish : pLeft.finish =
      (pt.paths left.val.2).vertices.get ⟨t, htLeftPath⟩ :=
    LGV.SimpleDigraph.Path.subpath_finish _ _ _ _ _
  have hpRightFinish : pRight.finish =
      (pt.paths right.val.2).vertices.get ⟨t, htRightPath⟩ :=
    LGV.SimpleDigraph.Path.subpath_finish _ _ _ _ _
  have hsourceX : (pt.paths right.val.2).start.1 ≤
      (pt.paths left.val.2).start.1 := by
    rw [pt.starts left.val.2, pt.starts right.val.2]
    simp only [dualJacobiTrudiSources]
    have hm := hmuT hcolLe
    push_cast
    omega
  have hsourceY : (pt.paths left.val.2).start.2 ≤
      (pt.paths right.val.2).start.2 := by
    rw [pt.starts left.val.2, pt.starts right.val.2]
    simp only [dualJacobiTrudiSources]
    have hm := hmuT hcolLe
    push_cast
    omega
  have hsumLeft := LGV.integerLattice_path_vertex_sum
    (pt.paths left.val.2) t htLeftPath
  have hsumRight := LGV.integerLattice_path_vertex_sum
    (pt.paths right.val.2) t htRightPath
  have hstartSumLeft : (pt.paths left.val.2).start.1 +
      (pt.paths left.val.2).start.2 = 0 := by
    rw [pt.starts left.val.2]
    simp [dualJacobiTrudiSources]
  have hstartSumRight : (pt.paths right.val.2).start.1 +
      (pt.paths right.val.2).start.2 = 0 := by
    rw [pt.starts right.val.2]
    simp [dualJacobiTrudiSources]
  rw [hstartSumLeft, zero_add] at hsumLeft
  rw [hstartSumRight, zero_add] at hsumRight
  have hyEnd :
      ((pt.paths right.val.2).vertices.get ⟨t, htRightPath⟩).2 ≤
        ((pt.paths left.val.2).vertices.get ⟨t, htLeftPath⟩).2 := by
    omega
  have hinter : LGV.pathsIntersect pLeft pRight := by
    apply LGV.baby_jordan
      (A := (pt.paths left.val.2).start)
      (A' := (pt.paths right.val.2).start)
      (B := (pt.paths right.val.2).vertices.get ⟨t, htRightPath⟩)
      (B' := (pt.paths left.val.2).vertices.get ⟨t, htLeftPath⟩)
    · exact hsourceX
    · exact hsourceY
    · exact hxEnd
    · exact hyEnd
    · exact hpLeftStart
    · exact hpLeftFinish
    · exact hpRightStart
    · exact hpRightFinish
  obtain ⟨v, hvLeft, hvRight⟩ := hinter
  apply (hnipat left.val.2 right.val.2 (by
    apply Fin.ne_of_val_ne
    omega))
  refine ⟨v, ?_, ?_⟩
  · dsimp only [pLeft, LGV.SimpleDigraph.Path.subpath] at hvLeft
    exact List.mem_of_mem_take hvLeft
  · dsimp only [pRight, LGV.SimpleDigraph.Path.subpath] at hvRight
    exact List.mem_of_mem_take hvRight

/-- The adjacent-column argument extends across the whole occupied interval
of a row. -/
theorem pathTupleToColumnTableau_rowWeak {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (hnipat : pt.isNonIntersecting)
    (left right : {c : Fin d × Fin k //
      c ∈ columnSkewDiagram lamt muT})
    (hrow : left.val.1 = right.val.1)
    (hcol : left.val.2 < right.val.2) :
    pathTupleToColumnTableau hcontained pt left ≤
      pathTupleToColumnTableau hcontained pt right := by
  let gap := right.val.2.val - left.val.2.val
  have hgap : left.val.2.val + gap = right.val.2.val := by
    dsimp only [gap]
    omega
  let colAt : Fin (gap + 1) → Fin k := fun u =>
    ⟨left.val.2.val + u.val, by
      have hu := u.isLt
      have hr := right.val.2.isLt
      omega⟩
  have hleftCol : ∀ u, left.val.2 ≤ colAt u := by
    intro u
    apply Fin.mk_le_mk.mpr
    simp [colAt]
  have hrightCol : ∀ u, colAt u ≤ right.val.2 := by
    intro u
    apply Fin.mk_le_mk.mpr
    change left.val.2.val + u.val ≤ right.val.2.val
    have hu := u.isLt
    omega
  let cellAt : Fin (gap + 1) →
      {c : Fin d × Fin k // c ∈ columnSkewDiagram lamt muT} :=
    fun u => ⟨(left.val.1, colAt u), by
      change muT (colAt u) ≤ left.val.1.val ∧
        left.val.1.val < lamt (colAt u)
      constructor
      · exact (hmuT (hleftCol u)).trans left.property.1
      · have hl := hlamt (hrightCol u)
        rw [hrow]
        exact right.property.2.trans_le hl⟩
  let f : Fin (gap + 1) → Fin d := fun u =>
    pathTupleToColumnTableau hcontained pt (cellAt u)
  have hf : Monotone f := by
    rw [Fin.monotone_iff_le_succ]
    intro u
    apply pathTupleToColumnTableau_rowWeak_adjacent hmuT hcontained pt
      hnipat (cellAt u.castSucc) (cellAt u.succ)
    · rfl
    · simp [cellAt, colAt, Nat.add_assoc]
  let first : Fin (gap + 1) := ⟨0, Nat.zero_lt_succ gap⟩
  let last : Fin (gap + 1) := ⟨gap, Nat.lt_succ_self gap⟩
  have hfirstLast : first ≤ last := by
    apply Fin.mk_le_mk.mpr
    exact Nat.zero_le _
  have hmono := hf hfirstLast
  change pathTupleToColumnTableau hcontained pt (cellAt first) ≤
    pathTupleToColumnTableau hcontained pt (cellAt last) at hmono
  have hcellFirst : cellAt first = left := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [cellAt, colAt, first]
  have hcellLast : cellAt last = right := by
    apply Subtype.ext
    apply Prod.ext
    · simpa [cellAt] using hrow
    · apply Fin.ext
      simpa [cellAt, colAt, last] using hgap
  rwa [hcellFirst, hcellLast] at hmono

/-- A nonintersecting elementary path tuple produces a semistandard column
tableau. -/
theorem pathTupleToColumnTableau_isSemistandard {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (hnipat : pt.isNonIntersecting) :
    IsColumnSemistandard (pathTupleToColumnTableau hcontained pt) := by
  constructor
  · intro c₁ c₂ hrow hcol
    exact pathTupleToColumnTableau_rowWeak hlamt hmuT hcontained pt
      hnipat c₁ c₂ hrow hcol
  · intro c₁ c₂ hcol hrow
    exact pathTupleToColumnTableau_columnStrict hcontained pt c₁ c₂
      hcol hrow

/-! ## From column tableaux back to paths -/

/-- The cell of rank `q` in column `c`, counted from the top of the skew
column. -/
def columnCell {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (c : Fin k) (q : Fin (lamt c - muT c)) :
    {z : Fin d × Fin k // z ∈ columnSkewDiagram lamt muT} :=
  ⟨(⟨muT c + q.val, by
      have hq := q.isLt
      have hh := hheight c
      omega⟩, c), by
    change muT c ≤ muT c + q.val ∧ muT c + q.val < lamt c
    constructor
    · omega
    · have hq := q.isLt
      have hc := hcontained c
      omega⟩

/-- Enumerating each column by its vertical rank enumerates every column
cell exactly once. -/
def columnRankEquivCell {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d) :
    (Σ c : Fin k, Fin (lamt c - muT c)) ≃
      {z : Fin d × Fin k // z ∈ columnSkewDiagram lamt muT} where
  toFun z := columnCell hcontained hheight z.1 z.2
  invFun z := ⟨z.val.2, ⟨z.val.1.val - muT z.val.2, by
    have hz := z.property
    change muT z.val.2 ≤ z.val.1.val ∧
      z.val.1.val < lamt z.val.2 at hz
    omega⟩⟩
  left_inv z := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      simp only [columnCell]
      have hc := hcontained z.1
      omega
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp only [columnCell]
      have hz := z.property
      change muT z.val.2 ≤ z.val.1.val ∧
        z.val.1.val < lamt z.val.2 at hz
      omega
    · rfl

/-- The entries occurring in a column of a column tableau. -/
noncomputable def columnEntrySet {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (c : Fin k) : Finset (Fin d) :=
  Finset.univ.image fun q : Fin (lamt c - muT c) =>
    T (columnCell hcontained hheight c q)

theorem columnEntrySet_card {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) :
    (columnEntrySet hcontained hheight T c).card = lamt c - muT c := by
  unfold columnEntrySet
  rw [Finset.card_image_of_injective]
  · simp
  · intro q₁ q₂ heq
    by_contra hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · have hs := hT.2 (columnCell hcontained hheight c q₁)
          (columnCell hcontained hheight c q₂) rfl (by
            apply Fin.mk_lt_mk.mpr
            exact Nat.add_lt_add_left hlt (muT c))
      exact (ne_of_lt hs) heq
    · have hs := hT.2 (columnCell hcontained hheight c q₂)
          (columnCell hcontained hheight c q₁) rfl (by
            apply Fin.mk_lt_mk.mpr
            exact Nat.add_lt_add_left hgt (muT c))
      exact (ne_of_gt hs) heq

/-- Sorting the entries of a strictly increasing tableau column recovers the
entry at each column rank. -/
theorem columnEntrySet_orderEmbOfFin {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) (q : Fin (lamt c - muT c)) :
    ((columnEntrySet hcontained hheight T c).orderEmbOfFin
      (columnEntrySet_card hcontained hheight T hT c) q) =
      T (columnCell hcontained hheight c q) := by
  let f : Fin (lamt c - muT c) →o Fin d :=
    { toFun := fun q => T (columnCell hcontained hheight c q)
      monotone' := by
        intro q₁ q₂ hq
        rcases hq.eq_or_lt with rfl | hlt
        · rfl
        · exact (hT.2 (columnCell hcontained hheight c q₁)
            (columnCell hcontained hheight c q₂) rfl (by
              apply Fin.mk_lt_mk.mpr
              exact Nat.add_lt_add_left hlt (muT c))).le }
  have hfStrict : StrictMono f := by
    intro q₁ q₂ hq
    exact hT.2 (columnCell hcontained hheight c q₁)
      (columnCell hcontained hheight c q₂) rfl (by
        apply Fin.mk_lt_mk.mpr
        exact Nat.add_lt_add_left hq (muT c))
  let fe : Fin (lamt c - muT c) ↪o Fin d :=
    { toFun := f
      inj' := hfStrict.injective
      map_rel_iff' := hfStrict.le_iff_le }
  have hfe : fe = (columnEntrySet hcontained hheight T c).orderEmbOfFin
      (columnEntrySet_card hcontained hheight T hT c) := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    unfold columnEntrySet
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ i, rfl⟩
  have happly := congrArg (fun g : Fin (lamt c - muT c) ↪o Fin d => g q) hfe
  exact happly.symm

/-- The lattice path encoded by one strictly increasing tableau column. -/
noncomputable def columnTableauPath {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) : LGV.SimpleDigraph.Path LGV.integerLattice :=
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  let S := columnEntrySet hcontained hheight T c
  let hcard : S.card = n := columnEntrySet_card hcontained hheight T hT c
  ((LGV.shiftedPathsEquivPowersetCard d n a).symm
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hcard⟩⟩).val

theorem columnTableauPath_start {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) :
    (columnTableauPath hcontained hheight T hT c).start =
      dualJacobiTrudiSources muT c := by
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  let S := columnEntrySet hcontained hheight T c
  let hcard : S.card = n := columnEntrySet_card hcontained hheight T hT c
  let p := (LGV.shiftedPathsEquivPowersetCard d n a).symm
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hcard⟩⟩
  have hp := p.property
  simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq] at hp
  change p.val.start = _
  rw [hp.1]
  rfl

theorem columnTableauPath_finish {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) :
    (columnTableauPath hcontained hheight T hT c).finish =
      dualJacobiTrudiTargets d lamt c := by
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  let S := columnEntrySet hcontained hheight T c
  let hcard : S.card = n := columnEntrySet_card hcontained hheight T hT c
  let p := (LGV.shiftedPathsEquivPowersetCard d n a).symm
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hcard⟩⟩
  have hp := p.property
  simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq] at hp
  change p.val.finish = _
  rw [hp.2]
  simp only [dualJacobiTrudiTargets]
  dsimp only [a, n]
  have hc := hcontained c
  ext <;> push_cast <;> omega

/-- The path constructed from a column has exactly the tableau entries as
its east-step times. -/
theorem columnTableauPath_eastSteps {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) :
    LGV.pathEastSteps d (columnTableauPath hcontained hheight T hT c)
        (by
          have h := LGV.integerLattice_path_length_eq
            (columnTableauPath hcontained hheight T hT c)
          rw [columnTableauPath_start, columnTableauPath_finish] at h
          simp only [dualJacobiTrudiSources,
            dualJacobiTrudiTargets] at h
          omega) =
      columnEntrySet hcontained hheight T c := by
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  let S := columnEntrySet hcontained hheight T c
  let hcard : S.card = n := columnEntrySet_card hcontained hheight T hT c
  let s : Finset.powersetCard n (Finset.univ : Finset (Fin d)) :=
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hcard⟩⟩
  let p := (LGV.shiftedPathsEquivPowersetCard d n a).symm s
  have hlen : p.val.vertices.length = d + 1 := by
    have hp := p.property
    simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at hp
    exact LGV.shifted_path_length d n a p.val hp.1 hp.2
  have happly := LGV.shiftedPathsEquivPowersetCard_apply_val d n a p hlen
  have hinv := (LGV.shiftedPathsEquivPowersetCard d n a).apply_symm_apply s
  have hval := congrArg Subtype.val hinv
  rw [hval] at happly
  exact happly.symm

/-- Assemble the paths encoded by all tableau columns. -/
noncomputable def columnTableauToPathTuple {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T) :
    LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt) where
  paths := columnTableauPath hcontained hheight T hT
  starts := columnTableauPath_start hcontained hheight T hT
  finishes := columnTableauPath_finish hcontained hheight T hT

/-- Reading the paths built from a semistandard column tableau recovers the
original filling. -/
theorem pathTupleToColumnTableau_columnTableauToPathTuple {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T) :
    pathTupleToColumnTableau hcontained
      (columnTableauToPathTuple hcontained hheight T hT) = T := by
  funext cell
  let c := cell.val.2
  let q : Fin (lamt c - muT c) :=
    ⟨cell.val.1.val - muT c, by
      have hc := cell.property
      change muT c ≤ cell.val.1.val ∧
        cell.val.1.val < lamt c at hc
      omega⟩
  have hcell : columnCell hcontained hheight c q = cell := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp only [columnCell, q, c]
      have hc := cell.property
      change muT cell.val.2 ≤ cell.val.1.val ∧
        cell.val.1.val < lamt cell.val.2 at hc
      omega
    · rfl
  let P := columnTableauToPathTuple hcontained hheight T hT
  let Spath := LGV.pathEastSteps d (P.paths c)
    (dualPathTuple_path_length P c)
  let hpathCard : Spath.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained P c
  have hset : Spath = columnEntrySet hcontained hheight T c := by
    exact columnTableauPath_eastSteps hcontained hheight T hT c
  have hemb : Spath.orderEmbOfFin hpathCard =
      (columnEntrySet hcontained hheight T c).orderEmbOfFin
        (columnEntrySet_card hcontained hheight T hT c) := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    rw [← hset]
    exact Finset.orderEmbOfFin_mem Spath hpathCard i
  change Spath.orderEmbOfFin hpathCard q = T cell
  rw [hemb]
  rw [columnEntrySet_orderEmbOfFin hcontained hheight T hT c q]
  rw [hcell]

/-- Prefix counts in adjacent tableau columns interlace.  This is the
counting form of weak row increase used to prove path nonintersection. -/
theorem columnEntrySet_prefix_interlaces_adjacent {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (cLeft cRight : Fin k)
    (hadj : cRight.val = cLeft.val + 1) (t : ℕ) :
    muT cRight +
        ((columnEntrySet hcontained hheight T cRight).filter
          (fun z => z.val < t)).card ≤
      muT cLeft +
        ((columnEntrySet hcontained hheight T cLeft).filter
          (fun z => z.val < t)).card := by
  let SLeft := columnEntrySet hcontained hheight T cLeft
  let SRight := columnEntrySet hcontained hheight T cRight
  let qLeft := (SLeft.filter (fun z => z.val < t)).card
  let qRight := (SRight.filter (fun z => z.val < t)).card
  have hcolLt : cLeft < cRight := by
    apply Fin.mk_lt_mk.mpr
    rw [hadj]
    exact Nat.lt_succ_self _
  have hmu := hmuT hcolLt.le
  have hlam := hlamt hcolLt.le
  have hqLeftLe : qLeft ≤ lamt cLeft - muT cLeft := by
    calc
      qLeft ≤ SLeft.card := Finset.card_filter_le _ _
      _ = lamt cLeft - muT cLeft :=
        columnEntrySet_card hcontained hheight T hT cLeft
  have hqRightLe : qRight ≤ lamt cRight - muT cRight := by
    calc
      qRight ≤ SRight.card := Finset.card_filter_le _ _
      _ = lamt cRight - muT cRight :=
        columnEntrySet_card hcontained hheight T hT cRight
  by_contra hinterlace
  push_neg at hinterlace
  dsimp only [qLeft, qRight, SLeft, SRight] at *
  have hqLeftLt : qLeft < lamt cLeft - muT cLeft := by
    by_contra hnot
    have heq : qLeft = lamt cLeft - muT cLeft := by
      dsimp only [qLeft, SLeft] at hnot ⊢
      omega
    have hleftSum : muT cLeft + qLeft = lamt cLeft := by
      rw [heq, Nat.add_sub_of_le (hcontained cLeft)]
    have hrightSum : muT cRight + qRight ≤ lamt cRight := by
      calc
        muT cRight + qRight ≤
            muT cRight + (lamt cRight - muT cRight) :=
          Nat.add_le_add_left hqRightLe _
        _ = lamt cRight := Nat.add_sub_of_le (hcontained cRight)
    dsimp only [qLeft, qRight, SLeft, SRight] at hleftSum hrightSum hinterlace ⊢
    omega
  let rNat := muT cLeft + qLeft
  have hrLeft : muT cLeft ≤ rNat ∧ rNat < lamt cLeft := by
    dsimp only [rNat]
    constructor <;> omega
  have hrRight : muT cRight ≤ rNat ∧ rNat < lamt cRight := by
    dsimp only [rNat]
    constructor
    · omega
    · have hrightSum : muT cRight + qRight ≤ lamt cRight := by
        calc
          muT cRight + qRight ≤
              muT cRight + (lamt cRight - muT cRight) :=
            Nat.add_le_add_left hqRightLe _
          _ = lamt cRight := Nat.add_sub_of_le (hcontained cRight)
      dsimp only [qLeft, qRight, SLeft, SRight] at hrightSum hinterlace ⊢
      omega
  have hrD : rNat < d := (hrLeft.2.trans_le (hheight cLeft))
  let r : Fin d := ⟨rNat, hrD⟩
  let leftCell : {z : Fin d × Fin k //
      z ∈ columnSkewDiagram lamt muT} :=
    ⟨(r, cLeft), hrLeft⟩
  let rightCell : {z : Fin d × Fin k //
      z ∈ columnSkewDiagram lamt muT} :=
    ⟨(r, cRight), hrRight⟩
  let leftRank : Fin (lamt cLeft - muT cLeft) :=
    ⟨qLeft, hqLeftLt⟩
  have hrightRankLt : rNat - muT cRight < qRight := by
    dsimp only [rNat, qLeft, qRight, SLeft, SRight] at hinterlace ⊢
    omega
  let rightRank : Fin (lamt cRight - muT cRight) :=
    ⟨rNat - muT cRight, hrightRankLt.trans_le hqRightLe⟩
  have hleftCell : columnCell hcontained hheight cLeft leftRank =
      leftCell := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp only [columnCell, leftRank, leftCell, r, rNat]
    · rfl
  have hrightCell : columnCell hcontained hheight cRight rightRank =
      rightCell := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp only [columnCell, rightRank, rightCell, r]
      have hmuRight : muT cRight ≤ rNat := hrRight.1
      omega
    · rfl
  have hleftEntry : t ≤ T leftCell := by
    rw [← hleftCell]
    rw [← columnEntrySet_orderEmbOfFin hcontained hheight T hT
      cLeft leftRank]
    apply le_orderEmbOfFin_of_card_filter_val_lt SLeft
      (columnEntrySet_card hcontained hheight T hT cLeft)
    rfl
  have hrightEntry : T rightCell < t := by
    rw [← hrightCell]
    rw [← columnEntrySet_orderEmbOfFin hcontained hheight T hT
      cRight rightRank]
    apply orderEmbOfFin_lt_of_lt_card_filter_val SRight
      (columnEntrySet_card hcontained hheight T hT cRight)
    dsimp only [rightRank, qRight]
    exact hrightRankLt
  have hrowWeak : T leftCell ≤ T rightCell := hT.1 leftCell rightCell
    rfl hcolLt
  omega

/-- Prefix-count interlacing across arbitrary ordered columns. -/
theorem columnEntrySet_prefix_interlaces {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (cLeft cRight : Fin k) (hcol : cLeft ≤ cRight) (t : ℕ) :
    muT cRight +
        ((columnEntrySet hcontained hheight T cRight).filter
          (fun z => z.val < t)).card ≤
      muT cLeft +
        ((columnEntrySet hcontained hheight T cLeft).filter
          (fun z => z.val < t)).card := by
  let g : Fin k → ℕ := fun c => muT c +
    ((columnEntrySet hcontained hheight T c).filter
      (fun z => z.val < t)).card
  have hg : Antitone g := by
    cases k with
    | zero =>
        intro c
        exact c.elim0
    | succ k =>
        apply Fin.antitone_iff_succ_le.mpr
        intro c
        exact columnEntrySet_prefix_interlaces_adjacent hlamt hmuT
          hcontained hheight T hT c.castSucc c.succ rfl t
  exact hg hcol

/-- Horizontal-coordinate formula for a path constructed from a tableau
column. -/
theorem columnTableauPath_x_coord {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T)
    (c : Fin k) (t : ℕ)
    (ht : t < (columnTableauPath hcontained hheight T hT c).vertices.length) :
    ((columnTableauPath hcontained hheight T hT c).vertices.get ⟨t, ht⟩).1 =
      (muT c : ℤ) - c.val +
        (((columnEntrySet hcontained hheight T c).filter
          (fun z => z.val < t)).card : ℕ) := by
  let p := columnTableauPath hcontained hheight T hT c
  have hstartSum : p.start.1 + p.start.2 = 0 := by
    rw [columnTableauPath_start]
    simp [dualJacobiTrudiSources]
  have hlen : p.vertices.length = d + 1 := by
    have h := LGV.integerLattice_path_length_eq p
    rw [columnTableauPath_start, columnTableauPath_finish] at h
    simp only [dualJacobiTrudiSources, dualJacobiTrudiTargets] at h
    omega
  have hx := LGV.path_x_coord_eq_start_add_card_eastSteps d p
    hstartSum hlen t ht
  have hset := columnTableauPath_eastSteps hcontained hheight T hT c
  have hbase : LGV.pathEastSteps d p hlen =
      columnEntrySet hcontained hheight T c := by
    simpa only [p] using hset
  have hfilter :
      ((LGV.pathEastSteps d p hlen).filter (fun z => z.val < t)).card =
        ((columnEntrySet hcontained hheight T c).filter
          (fun z => z.val < t)).card := by
    rw [hbase]
  rw [hfilter] at hx
  rw [columnTableauPath_start] at hx
  simp only [dualJacobiTrudiSources] at hx
  exact hx

/-- Paths constructed from a semistandard column tableau are pairwise
nonintersecting. -/
theorem columnTableauToPathTuple_isNonIntersecting {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) (hT : IsColumnSemistandard T) :
    (columnTableauToPathTuple hcontained hheight T hT).isNonIntersecting := by
  intro c₁ c₂ hcne hinter
  wlog hcol : c₁ < c₂ generalizing c₁ c₂
  · have hrev : c₂ < c₁ := lt_of_le_of_ne (not_lt.mp hcol)
      (Ne.symm hcne)
    exact this c₂ c₁ (Ne.symm hcne)
      ⟨hinter.choose, hinter.choose_spec.2, hinter.choose_spec.1⟩ hrev
  obtain ⟨v, hv₁, hv₂⟩ := hinter
  obtain ⟨t₁, ht₁, htv₁⟩ := List.mem_iff_getElem.mp hv₁
  obtain ⟨t₂, ht₂, htv₂⟩ := List.mem_iff_getElem.mp hv₂
  let p₁ := columnTableauPath hcontained hheight T hT c₁
  let p₂ := columnTableauPath hcontained hheight T hT c₂
  change p₁.vertices[t₁] = v at htv₁
  change p₂.vertices[t₂] = v at htv₂
  have hvEq : p₁.vertices.get ⟨t₁, ht₁⟩ =
      p₂.vertices.get ⟨t₂, ht₂⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact htv₁.trans htv₂.symm
  have hsum₁ := LGV.integerLattice_path_vertex_sum p₁ t₁ ht₁
  have hsum₂ := LGV.integerLattice_path_vertex_sum p₂ t₂ ht₂
  have hstart₁ : p₁.start.1 + p₁.start.2 = 0 := by
    rw [columnTableauPath_start]
    simp [dualJacobiTrudiSources]
  have hstart₂ : p₂.start.1 + p₂.start.2 = 0 := by
    rw [columnTableauPath_start]
    simp [dualJacobiTrudiSources]
  rw [hstart₁, zero_add] at hsum₁
  rw [hstart₂, zero_add] at hsum₂
  have htEq : t₁ = t₂ := by
    rw [hvEq] at hsum₁
    omega
  subst t₂
  have hx₁ := columnTableauPath_x_coord hcontained hheight T hT c₁ t₁ ht₁
  have hx₂ := columnTableauPath_x_coord hcontained hheight T hT c₂ t₁ ht₂
  have hinterlace := columnEntrySet_prefix_interlaces hlamt hmuT
    hcontained hheight T hT c₁ c₂ hcol.le t₁
  have hxStrict :
      (p₂.vertices.get ⟨t₁, ht₂⟩).1 <
        (p₁.vertices.get ⟨t₁, ht₁⟩).1 := by
    rw [hx₁, hx₂]
    push_cast
    omega
  rw [hvEq] at hxStrict
  exact (lt_irrefl _ hxStrict)

/-- Forming entry sets after reading a nonintersecting path tuple recovers
the original east-step sets. -/
theorem columnEntrySet_pathTupleToColumnTableau {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (hnipat : pt.isNonIntersecting) (c : Fin k) :
    columnEntrySet hcontained hheight
        (pathTupleToColumnTableau hcontained pt) c =
      LGV.pathEastSteps d (pt.paths c)
        (dualPathTuple_path_length pt c) := by
  let S := LGV.pathEastSteps d (pt.paths c)
    (dualPathTuple_path_length pt c)
  let hcard : S.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained pt c
  have hvalue : ∀ q : Fin (lamt c - muT c),
      pathTupleToColumnTableau hcontained pt
          (columnCell hcontained hheight c q) =
        S.orderEmbOfFin hcard q := by
    intro q
    simp only [pathTupleToColumnTableau]
    congr 1
    apply Fin.ext
    simp only [columnCell]
    have hc := hcontained c
    omega
  unfold columnEntrySet
  simp_rw [hvalue]
  exact Finset.image_orderEmbOfFin_univ S hcard

/-- Reconstructing paths after reading their column tableau returns the
original path tuple. -/
theorem columnTableauToPathTuple_pathTupleToColumnTableau {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt))
    (hnipat : pt.isNonIntersecting) :
    columnTableauToPathTuple hcontained hheight
        (pathTupleToColumnTableau hcontained pt)
        (pathTupleToColumnTableau_isSemistandard hlamt hmuT
          hcontained pt hnipat) = pt := by
  apply LGV.PathTuple.ext
  intro c
  let a : ℤ := (muT c : ℤ) - c.val
  let n : ℕ := lamt c - muT c
  let T := pathTupleToColumnTableau hcontained pt
  let hT := pathTupleToColumnTableau_isSemistandard hlamt hmuT
    hcontained pt hnipat
  change columnTableauPath hcontained hheight T hT c = pt.paths c
  refine shiftedPath_eq_of_eastSteps d n a
    (columnTableauPath hcontained hheight T hT c) (pt.paths c)
    ?_ ?_ ?_ ?_ ?_
  · simpa only [a, dualJacobiTrudiSources] using
      columnTableauPath_start hcontained hheight T hT c
  · rw [columnTableauPath_finish hcontained hheight T hT c]
    simp only [dualJacobiTrudiTargets]
    dsimp only [a, n]
    have hc := hcontained c
    ext <;> push_cast <;> omega
  · simpa only [a, dualJacobiTrudiSources] using pt.starts c
  · rw [pt.finishes c]
    simp only [dualJacobiTrudiTargets]
    dsimp only [a, n]
    have hc := hcontained c
    ext <;> push_cast <;> omega
  · rw [columnTableauPath_eastSteps hcontained hheight T hT c]
    exact columnEntrySet_pathTupleToColumnTableau hlamt hmuT
      hcontained hheight pt hnipat c

/-- Nonintersecting path tuples for the dual Jacobi--Trudi endpoints. -/
abbrev DualNipat (d : ℕ) {k : ℕ} (lamt muT : Fin k → ℕ) :=
  {pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt) //
    pt.isNonIntersecting}

/-- The checked path/tableau bijection underlying the dual Jacobi--Trudi
identity. -/
noncomputable def dualNipatEquivColumnSSYT {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d) :
    DualNipat d lamt muT ≃ ColumnSSYT d lamt muT where
  toFun pt := ⟨pathTupleToColumnTableau hcontained pt.val,
    pathTupleToColumnTableau_isSemistandard hlamt hmuT hcontained
      pt.val pt.property⟩
  invFun T := ⟨columnTableauToPathTuple hcontained hheight T.val T.property,
    columnTableauToPathTuple_isNonIntersecting hlamt hmuT hcontained
      hheight T.val T.property⟩
  left_inv pt := by
    apply Subtype.ext
    exact columnTableauToPathTuple_pathTupleToColumnTableau
      hlamt hmuT hcontained hheight pt.val pt.property
  right_inv T := by
    apply Subtype.ext
    exact pathTupleToColumnTableau_columnTableauToPathTuple
      hcontained hheight T.val T.property

/-! ## Weight preservation -/

/-- Reindex a product over a finset by its increasing enumeration. -/
theorem prod_finset_eq_prod_orderEmbOfFin
    {M α : Type*} [CommMonoid M] [LinearOrder α]
    (S : Finset α) {n : ℕ} (hcard : S.card = n) (f : α → M) :
    ∏ x ∈ S, f x = ∏ q : Fin n, f (S.orderEmbOfFin hcard q) := by
  rw [← Finset.prod_attach]
  change (∏ x : S, f x.val) = _
  symm
  apply Fintype.prod_equiv (S.orderIsoOfFin hcard).toEquiv
  intro q
  rfl

/-- The monomial weight of a column tableau, written as an iterated product
over columns and ranks within columns. -/
noncomputable def columnTableauWeight {R : Type*} [CommRing R]
    {d k : ℕ} {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) : MvPolynomial (Fin d) R :=
  ∏ c : Fin k, ∏ q : Fin (lamt c - muT c),
    MvPolynomial.X (T (columnCell hcontained hheight c q))

/-- The iterated column weight is the product over all column cells. -/
theorem columnTableauWeight_eq_prod_cells
    {R : Type*} [CommRing R] {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) :
    columnTableauWeight (R := R) hcontained hheight T =
      ∏ z : {z : Fin d × Fin k // z ∈ columnSkewDiagram lamt muT},
        MvPolynomial.X (T z) := by
  unfold columnTableauWeight
  calc
    (∏ c : Fin k, ∏ q : Fin (lamt c - muT c),
        MvPolynomial.X (T (columnCell hcontained hheight c q))) =
        ∏ z : (Σ c : Fin k, Fin (lamt c - muT c)),
          MvPolynomial.X (T (columnCell hcontained hheight z.1 z.2)) :=
      (Fintype.prod_sigma (fun z : (Σ c : Fin k,
        Fin (lamt c - muT c)) =>
          MvPolynomial.X (T (columnCell hcontained hheight z.1 z.2)))).symm
    _ = ∏ z : {z : Fin d × Fin k //
        z ∈ columnSkewDiagram lamt muT}, MvPolynomial.X (T z) := by
      apply Fintype.prod_equiv (columnRankEquivCell hcontained hheight)
      intro z
      rfl

/-- Reindexing cells carries the column weight to the product over the usual
skew Young diagram. -/
theorem columnTableauWeight_eq_prod_skewCells
    {R : Type*} [CommRing R] {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) :
    columnTableauWeight (R := R) hcontained hheight T =
      ∏ z : {z : Fin d × ℕ // z ∈ skewYoungDiagram lam mu},
        MvPolynomial.X
          (columnTableauEquivTableau hlam hmu hlamt hmuT htransLam
            htransMu hwidth T z) := by
  rw [columnTableauWeight_eq_prod_cells]
  apply Fintype.prod_equiv
    (columnCellEquivSkew hlam hmu hlamt hmuT htransLam htransMu hwidth)
  intro z
  rw [columnTableauEquivTableau_apply]
  simp

/-- The product of variables over all tableau cells is `x^(content T)`. -/
theorem prod_skewCells_eq_xPow_content
    {R : Type*} [CommRing R] {d : ℕ} {lam mu : Fin d → ℕ}
    (T : Tableau lam mu) :
    (∏ z : {z : Fin d × ℕ // z ∈ skewYoungDiagram lam mu},
        MvPolynomial.X (T z)) =
      (xPow (contentTableau T) : MvPolynomial (Fin d) R) := by
  change (∏ z : {z : Fin d × ℕ // z ∈ skewYoungDiagram lam mu},
      MvPolynomial.X (T z)) =
    ∏ i : Fin d, MvPolynomial.X i ^ contentTableau T i
  rw [← Fintype.prod_fiberwise' T
    (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)]
  apply Finset.prod_congr rfl
  intro i hi
  have hcontent : contentTableau T i =
      Fintype.card {z : {z : Fin d × ℕ //
        z ∈ skewYoungDiagram lam mu} // T z = i} := by
    unfold contentTableau
    rw [Nat.card_eq_fintype_card]
  rw [hcontent]
  simp

/-- Under transpose cell reindexing, the column weight is the usual tableau
monomial. -/
theorem columnTableauWeight_eq_xPow_content
    {R : Type*} [CommRing R] {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (T : ColumnTableau d lamt muT) :
    columnTableauWeight (R := R) hcontained hheight T =
      xPow (contentTableau
        (columnTableauEquivTableau hlam hmu hlamt hmuT htransLam
          htransMu hwidth T)) := by
  rw [columnTableauWeight_eq_prod_skewCells hlam hmu hlamt hmuT
    htransLam htransMu hwidth hcontained hheight T]
  exact prod_skewCells_eq_xPow_content _

/-- The LGV weight of a nonintersecting path tuple is the monomial of its
column tableau. -/
theorem pathTupleWeight_eq_columnTableauWeight
    {R : Type*} [CommRing R] {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d)
    (pt : LGV.PathTuple LGV.integerLattice k
      (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt)) :
    LGV.pathTupleWeight
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)) pt.paths =
      columnTableauWeight hcontained hheight
        (pathTupleToColumnTableau hcontained pt) := by
  unfold LGV.pathTupleWeight columnTableauWeight
  apply Finset.prod_congr rfl
  intro c hc
  let S := LGV.pathEastSteps d (pt.paths c)
    (dualPathTuple_path_length pt c)
  let hcard : S.card = lamt c - muT c :=
    dualPathTuple_eastSteps_card hcontained pt c
  rw [LGV.pathWeight_elementary_eq_prod_eastSteps d
    (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R)
    (pt.paths c) (by
      rw [pt.starts c]
      simp [dualJacobiTrudiSources])
    (dualPathTuple_path_length pt c)]
  rw [prod_finset_eq_prod_orderEmbOfFin S hcard]
  apply Finset.prod_congr rfl
  intro q hq
  congr 1
  simp only [pathTupleToColumnTableau]
  congr 1
  apply Fin.ext
  simp only [columnCell]
  have hcontain := hcontained c
  omega

/-- The LGV nonintersecting-path sum is the generating function of
semistandard column tableaux. -/
theorem nipatWeightSum_eq_sum_columnSSYT
    {R : Type*} [CommRing R] {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d) :
    LGV.nipatWeightSum LGV.integerLattice_pathFinite
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        (dualJacobiTrudiSources muT) (dualJacobiTrudiTargets d lamt)
        (Equiv.refl (Fin k)) =
      ∑ T : ColumnSSYT d lamt muT,
        columnTableauWeight hcontained hheight T.val := by
  let A := dualJacobiTrudiSources muT
  let B := dualJacobiTrudiTargets d lamt
  let pathFinset := LGV.nipatFinset LGV.integerLattice_pathFinite A B
  let ePath : {pt // pt ∈ pathFinset} ≃ DualNipat d lamt muT :=
    { toFun := fun pt => ⟨pt.val, by
        exact (LGV.mem_nipatFinset_iff
          LGV.integerLattice_pathFinite pt.val).mp pt.property⟩
      invFun := fun pt => ⟨pt.val, by
        exact (LGV.mem_nipatFinset_iff
          LGV.integerLattice_pathFinite pt.val).mpr pt.property⟩
      left_inv := by intro pt; rfl
      right_inv := by intro pt; rfl }
  let e := ePath.trans
    (dualNipatEquivColumnSSYT hlamt hmuT hcontained hheight)
  unfold LGV.nipatWeightSum
  rw [← Finset.sum_attach]
  change (∑ pt : {pt // pt ∈ pathFinset},
      LGV.pathTupleWeight
        (LGV.elementaryLatticeWeight d
          (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))
        pt.val.paths) = _
  apply Fintype.sum_equiv e
  intro pt
  exact pathTupleWeight_eq_columnTableauWeight hcontained hheight pt.val

/-- Dual Jacobi--Trudi in the column presentation: the determinant of
elementary symmetric functions is the semistandard-tableau generating
function. -/
theorem det_dualJacobiTrudiMatrixE_eq_sum_columnSSYT
    {R : Type*} [CommRing R] {d k : ℕ}
    {lamt muT : Fin k → ℕ}
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d) :
    (dualJacobiTrudiMatrixE R d lamt muT).det =
      ∑ T : ColumnSSYT d lamt muT,
        columnTableauWeight hcontained hheight T.val := by
  rw [det_dualJacobiTrudiMatrixE_eq_nipatWeightSum d hlamt hmuT]
  exact nipatWeightSum_eq_sum_columnSSYT hlamt hmuT hcontained hheight

/-- Full dual Jacobi--Trudi identity in the Littlewood--Richardson skew Schur
API. -/
theorem det_dualJacobiTrudiMatrixE_eq_skewSchurPoly
    {R : Type*} [CommRing R] {d k : ℕ}
    {lam mu : Fin d → ℕ} {lamt muT : Fin k → ℕ}
    (hlam : Antitone lam) (hmu : Antitone mu)
    (hlamt : Antitone lamt) (hmuT : Antitone muT)
    (htransLam : NPartition.IsTranspose lam lamt)
    (htransMu : NPartition.IsTranspose mu muT)
    (hwidth : ∀ r, lam r ≤ k)
    (hcontained : ∀ c, muT c ≤ lamt c)
    (hheight : ∀ c, lamt c ≤ d) :
    (dualJacobiTrudiMatrixE R d lamt muT).det =
      (skewSchurPoly lam mu : MvPolynomial (Fin d) R) := by
  rw [det_dualJacobiTrudiMatrixE_eq_sum_columnSSYT
    hlamt hmuT hcontained hheight]
  unfold skewSchurPoly
  let e := columnSSYTEquivSemistandardTableau hlam hmu hlamt hmuT
    htransLam htransMu hwidth
  apply Fintype.sum_equiv e
  intro T
  exact columnTableauWeight_eq_xPow_content hlam hmu hlamt hmuT
    htransLam htransMu hwidth hcontained hheight T.val

end

end FurtherToeplitzPositroids
