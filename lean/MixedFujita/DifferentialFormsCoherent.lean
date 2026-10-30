/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DifferentialFormsDeRham
public import SGA.Foundations.Cohomology.Serre
public import SGA.Foundations.Cohomology.QuasiCoherentLocal
public import SGA.Foundations.Cohomology.Coherent
public import SGA.Foundations.Cohomology.Statements
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Submodule
public import MixedFujita.ClosedEmbeddingSheafExactness

/-!
Coherence of the sheaves `Ω^b_X` (step 10).

Fix an étale chart `c` of an integral scheme `X` over `K`. The rational `b`-forms have the wedge
basis of the chart coordinates (`chartFormsFinBasis`). The forms whose coefficients in this basis are
regular at every point form a subsheaf of modules of the rational forms, the chart lattice
(`chartLatticeSubmodule`), on all of `X`. It is free: the basis forms, as global sections, give
`𝒪_X^r → (rational b-forms)` (`chartLatticeMap`), which is injective on sections and maps onto the
lattice, since `Γ(X, W)` is the intersection of the local rings at the points of `W`; so
`𝒪_X^r ≅ chart lattice` (`chartLatticeIso`, TauCeti's `isIso_liftToSubmodule`).

Over the chart, the lattice is `Ω^b_X` (`regularFormsSections_eq_chartLatticeSections`, check-415),
so `Ω^b_X` restricted to the chart is `𝒪^r` (`differentialFormsOverChartIso`). As quasi-coherence is
local (Mathlib's `IsQuasicoherent.of_coversTop`), `Ω^b_X` is quasi-coherent on a scheme covered by
étale charts (`isQuasicoherent_differentialFormsSheaf`), and since its sections over the affine
charts are finitely generated (check-415), it is coherent (`isCoherent_differentialFormsSheaf`, in
the sense used by the Serre vanishing and finiteness theorems).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u

/-- The number of wedge basis elements of `b`-forms in `n` coordinates. -/
abbrev wedgeRank (n b : ℕ) : ℕ := Fintype.card (Set.powersetCard (Fin n) b)

theorem modules_sections_subsingleton_of_eq_bot {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (hU : U = ⊥) : Subsingleton Γ(M, U) :=
  abelianSheaf_empty_sections_subsingleton ((SheafOfModules.toSheaf _).obj M) hU

/-- A section of `𝒪_X^k` is the sum of its components. -/
theorem unitBiproduct_sections_eq_sum {X : Scheme.{u}} (k : ℕ) (W : X.Opens)
    (x : Γ(CohomologyAux.unitBiproduct X k, W)) :
    x = ∑ j, (biproduct.ι (fun _ : Fin k => CohomologyAux.unitModule X) j).app W
      ((biproduct.π (fun _ : Fin k => CohomologyAux.unitModule X) j).app W x) := by
  let ev : (CohomologyAux.unitBiproduct X k ⟶ CohomologyAux.unitBiproduct X k) →+
      Γ(CohomologyAux.unitBiproduct X k, W) :=
    { toFun := fun φ ↦ φ.app W x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have h := congrArg ev (biproduct.total (f := fun _ : Fin k => CohomologyAux.unitModule X))
  rw [map_sum] at h
  exact h.symm

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The wedge basis of the rational `b`-forms of a chart, indexed by `Fin (wedgeRank n b)`. -/
noncomputable abbrev chartFormsFinBasis (c : EtaleChart K X n) (b : ℕ) :
    Module.Basis (Fin (wedgeRank n b)) X.functionField (RationalForms K X b) :=
  (chartFormsBasis c b).reindex (Fintype.equivFin _)

/-- The rational `b`-forms on `W` whose coefficients in the wedge basis of the chart are regular at
every point of `W`. -/
noncomputable def chartLatticeSections (c : EtaleChart K X n) (b : ℕ) (W : X.Opens) :
    Submodule Γ(X, W) Γ(rationalFormsSheaf K X b, W) where
  carrier := {s | ∀ (x : X) (hx : x ∈ W), haveI : Nonempty W := ⟨⟨x, hx⟩⟩
    ∀ j, (chartFormsFinBasis c b).repr (rationalFormsSectionsEquiv K b W s) j ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by
    intro x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    intro j
    rw [map_zero, map_zero, Finsupp.zero_apply]
    exact Subring.zero_mem _
  add_mem' := by
    intro s t hs ht x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    intro j
    rw [map_add, map_add, Finsupp.add_apply]
    exact Subring.add_mem _ (hs x hx j) (ht x hx j)
  smul_mem' := by
    intro r s hs x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    intro j
    rw [rationalFormsSectionsEquiv_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := W) hx r]
    exact Subring.mul_mem _ ⟨_, rfl⟩ (hs x hx j)

/-- **The chart lattice**, a subsheaf of modules of the rational `b`-forms on all of `X`. -/
noncomputable def chartLatticeSubmodule (c : EtaleChart K X n) (b : ℕ) :
    (rationalFormsSheaf K X b).Submodule where
  obj W := chartLatticeSections c b W.unop
  map {W V} i := fun s hs x hx => by
    have : Nonempty V.unop := ⟨⟨x, hx⟩⟩
    have : Nonempty W.unop := ⟨⟨x, i.unop.le hx⟩⟩
    have h := rationalFormsSectionsEquiv_map K b i.unop s
    change ∀ j, (chartFormsFinBasis c b).repr (rationalFormsSectionsEquiv K b V.unop
      ((rationalFormsSheaf K X b).presheaf.map i.unop.op s)) j ∈ _
    rw [h]
    exact hs x (i.unop.le hx)
  isSheaf {U} s hs := by
    intro x hx
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFormsSheaf K X b).presheaf.map i.op s ∈ chartLatticeSections c b V := hi
    rw [← rationalFormsSectionsEquiv_map K b i s]
    exact hi' x hxV

/-- Over the chart, the chart lattice is `Ω^b_X`. -/
theorem regularFormsSections_eq_chartLatticeSections (c : EtaleChart K X n) (b : ℕ) {W : X.Opens}
    (hW : W ≤ c.U) : regularFormsSections K b W = chartLatticeSections c b W := by
  ext s
  constructor
  · intro hs x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    intro j
    have h := (mem_range_stalkFormsMap_iff c b x (hW hx) _).mp (hs x hx)
    rw [Module.Basis.repr_reindex_apply]
    exact h _
  · intro hs x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    refine (mem_range_stalkFormsMap_iff c b x (hW hx) _).mpr fun t => ?_
    have h := hs x hx (Fintype.equivFin _ t)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at h
    exact h

/-- The basis forms of the chart as global sections of the rational forms. -/
noncomputable def chartBasisSection (c : EtaleChart K X n) (b : ℕ) (j : Fin (wedgeRank n b)) :
    Γ(rationalFormsSheaf K X b, ⊤) :=
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  (rationalFormsSectionsEquiv K b ⊤).symm (chartFormsFinBasis c b j)

/-- `𝒪_X^r → (rational b-forms)`, given by the basis forms of the chart. -/
noncomputable def chartLatticeMap (c : EtaleChart K X n) (b : ℕ) :
    CohomologyAux.unitBiproduct X (wedgeRank n b) ⟶ rationalFormsSheaf K X b :=
  biproduct.desc fun j => CohomologyAux.homOfSection _ (chartBasisSection c b j)

theorem chartLatticeMap_ι_app (c : EtaleChart K X n) (b : ℕ) (j : Fin (wedgeRank n b))
    (W : X.Opens) (r : Γ(X, W)) :
    (chartLatticeMap c b).app W
        ((biproduct.ι (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W r) =
      r • (rationalFormsSheaf K X b).presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        (chartBasisSection c b j) := by
  change (biproduct.ι (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j ≫
    chartLatticeMap c b).app W r = _
  rw [chartLatticeMap, biproduct.ι_desc]
  exact CohomologyAux.homOfSection_app _ _ W r

theorem rationalFormsSectionsEquiv_chartLatticeMap_ι (c : EtaleChart K X n) (b : ℕ)
    (j : Fin (wedgeRank n b)) (W : X.Opens) [Nonempty W] (r : Γ(X, W)) :
    rationalFormsSectionsEquiv K b W ((chartLatticeMap c b).app W
        ((biproduct.ι (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W r)) =
      X.germToFunctionField W r • chartFormsFinBasis c b j := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  rw [chartLatticeMap_ι_app, rationalFormsSectionsEquiv_smul,
    rationalFormsSectionsEquiv_map K b (homOfLE le_top : W ⟶ ⊤), chartBasisSection,
    AddEquiv.apply_symm_apply]

/-- **The value of a section of `𝒪_X^r`** is the combination of the basis forms with its
components as coefficients. -/
theorem rationalFormsSectionsEquiv_chartLatticeMap (c : EtaleChart K X n) (b : ℕ) (W : X.Opens)
    [Nonempty W] (x : Γ(CohomologyAux.unitBiproduct X (wedgeRank n b), W)) :
    rationalFormsSectionsEquiv K b W ((chartLatticeMap c b).app W x) =
      ∑ j, X.germToFunctionField W
        ((biproduct.π (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W x) •
          chartFormsFinBasis c b j := by
  conv_lhs => rw [unitBiproduct_sections_eq_sum (wedgeRank n b) W x]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => rationalFormsSectionsEquiv_chartLatticeMap_ι c b j W _

theorem chartFormsFinBasis_repr_sum (c : EtaleChart K X n) (b : ℕ)
    (f : Fin (wedgeRank n b) → X.functionField) (j : Fin (wedgeRank n b)) :
    (chartFormsFinBasis c b).repr (∑ i, f i • chartFormsFinBasis c b i) j = f j := by
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem chartLatticeMap_mem (c : EtaleChart K X n) (b : ℕ) (W : (X.Opens)ᵒᵖ)
    (x : (CohomologyAux.unitBiproduct X (wedgeRank n b)).val.obj W) :
    (chartLatticeMap c b).val.app W x ∈ (chartLatticeSubmodule c b).obj W := by
  induction W using Opposite.rec with | op W => ?_
  intro y hy
  have : Nonempty W := ⟨⟨y, hy⟩⟩
  intro j
  change (chartFormsFinBasis c b).repr (rationalFormsSectionsEquiv K b W
    ((chartLatticeMap c b).app W x)) j ∈ _
  rw [rationalFormsSectionsEquiv_chartLatticeMap, chartFormsFinBasis_repr_sum,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := W) hy]
  exact ⟨_, rfl⟩

theorem chartLatticeMap_injective (c : EtaleChart K X n) (b : ℕ) (W : (X.Opens)ᵒᵖ) :
    Function.Injective ((chartLatticeMap c b).val.app W) := by
  induction W using Opposite.rec with | op W => ?_
  intro x x' h
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (CohomologyAux.unitBiproduct X (wedgeRank n b)) hbot) _ _
  · have h' : rationalFormsSectionsEquiv K b W ((chartLatticeMap c b).app W x) =
        rationalFormsSectionsEquiv K b W ((chartLatticeMap c b).app W x') := congrArg _ h
    rw [rationalFormsSectionsEquiv_chartLatticeMap, rationalFormsSectionsEquiv_chartLatticeMap] at h'
    have hc : ∀ j, (biproduct.π (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W x
        = (biproduct.π (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W x' := by
      intro j
      apply Scheme.germToFunctionField_injective X W
      have := congrArg (fun ω => (chartFormsFinBasis c b).repr ω j) h'
      simpa only [chartFormsFinBasis_repr_sum] using this
    rw [unitBiproduct_sections_eq_sum (wedgeRank n b) W x,
      unitBiproduct_sections_eq_sum (wedgeRank n b) W x']
    exact Finset.sum_congr rfl fun j _ => by rw [hc j]

theorem chartLatticeMap_surjective (c : EtaleChart K X n) (b : ℕ) (W : (X.Opens)ᵒᵖ)
    (s : (rationalFormsSheaf K X b).val.obj W) (hs : s ∈ (chartLatticeSubmodule c b).obj W) :
    ∃ t, (chartLatticeMap c b).val.app W t = s := by
  induction W using Opposite.rec with | op W => ?_
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact ⟨0, @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (rationalFormsSheaf K X b) hbot) _ _⟩
  · have hreg : ∀ j, ∃ a : Γ(X, W), X.germToFunctionField W a =
        (chartFormsFinBasis c b).repr (rationalFormsSectionsEquiv K b W s) j := fun j =>
      exists_germToFunctionField_eq_of_forall_mem_range fun y hy => hs y hy j
    choose a ha using hreg
    refine ⟨∑ j, (biproduct.ι (fun _ : Fin (wedgeRank n b) => CohomologyAux.unitModule X) j).app W
      (a j), ?_⟩
    apply (rationalFormsSectionsEquiv K b W).injective
    change rationalFormsSectionsEquiv K b W ((chartLatticeMap c b).app W _) = _
    rw [map_sum, map_sum]
    conv_rhs => rw [← (chartFormsFinBasis c b).sum_repr (rationalFormsSectionsEquiv K b W s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rationalFormsSectionsEquiv_chartLatticeMap_ι, ha j]

/-- **The chart lattice is free**: `𝒪_X^r ≅ chart lattice`. -/
noncomputable def chartLatticeIso (c : EtaleChart K X n) (b : ℕ) :
    CohomologyAux.unitBiproduct X (wedgeRank n b) ≅ (chartLatticeSubmodule c b).toSheafOfModules :=
  haveI := TauCeti.SheafOfModules.isIso_liftToSubmodule (chartLatticeSubmodule c b)
    (chartLatticeMap c b) (chartLatticeMap_mem c b) (chartLatticeMap_injective c b)
    (chartLatticeMap_surjective c b)
  asIso (TauCeti.SheafOfModules.liftToSubmodule (chartLatticeSubmodule c b) (chartLatticeMap c b)
    (chartLatticeMap_mem c b))

/-- **Over an étale chart, `Ω^b_X` is `𝒪^r`.** -/
noncomputable def differentialFormsOverChartIso (c : EtaleChart K X n) (b : ℕ) :
    (differentialFormsSheaf K (X := X) b).over c.U ≅
      (CohomologyAux.unitBiproduct X (wedgeRank n b)).over c.U :=
  SheafOfModules.Submodule.overIsoOfEq (regularFormsSubmodule K b) (chartLatticeSubmodule c b) c.U
      (fun _ i => regularFormsSections_eq_chartLatticeSections c b i.le) ≪≫
    (SheafOfModules.overFunctor _ c.U).mapIso (chartLatticeIso c b).symm

/-- **`Ω^b_X` is quasi-coherent** on a scheme covered by étale charts. -/
theorem isQuasicoherent_differentialFormsSheaf
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) :
    (differentialFormsSheaf K (X := X) b).IsQuasicoherent := by
  have h : ∀ c : EtaleChart K X n,
      ((differentialFormsSheaf K (X := X) b).over c.U).IsQuasicoherent := fun c => by
    obtain ⟨⟨q⟩⟩ := SheafOfModules.isQuasicoherent_over
      (CohomologyAux.unitBiproduct X (wedgeRank n b)) c.U
    exact (q.ofIsIso (differentialFormsOverChartIso c b).inv).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop (C := X.Opens)
    (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (differentialFormsSheaf K (X := X) b)
    (fun c : EtaleChart K X n => c.U) ((Opens.coversTop_iff X _).mpr (IsOpenCover.mk hcover))

/-- **`Ω^b_X` is coherent** on a scheme covered by étale charts. -/
theorem isCoherent_differentialFormsSheaf
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) :
    (differentialFormsSheaf K (X := X) b).IsCoherent := by
  have := isQuasicoherent_differentialFormsSheaf hcover b
  exact ⟨inferInstance, CohomologyAux.isFiniteType_of_finite_sections _
    (fun c : EtaleChart K X n => c.U) hcover (fun c => c.isAffine)
    fun c => Module.Finite.of_basis (chartSectionsBasis c b)⟩

end MixedFujita
