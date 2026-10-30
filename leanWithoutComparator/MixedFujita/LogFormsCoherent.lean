/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogDifferentialForms
public import MixedFujita.DifferentialFormsCoherent
public import MixedFujita.ProjectiveCoherentSectionSurjections

/-!
Coherence of the sheaves `Ω^b_X(log E)` (step 10, R2).

For any finite basis `B` of the rational `b`-forms, the forms whose coefficients in `B` are regular
at every point form a subsheaf of modules of the rational forms on all of `X`
(`basisLatticeSubmodule`), and the basis forms give `𝒪_X^m ≅ (this lattice)` (`basisLatticeIso`),
as for the chart lattice of check 417 (whose argument is copied with an arbitrary basis). Its
sections over every open subset are finitely generated (`finite_basisLatticeSections`).

On a simple normal crossing chart `c` the logarithmic forms are the lattice of the logarithmic
wedge basis of check 476 (`logFormsSections_zero_eq_basisLatticeSections`), so over the chart
`Ω^b_X(log E)` is `𝒪^r` (`logFormsOverChartIso`). The simple normal crossing charts cover `X`, so
`Ω^b_X(log E)` is quasi-coherent and coherent (`isQuasicoherent_logFormsSheaf_zero`,
`isCoherent_logFormsSheaf_zero`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section BasisLattice

variable {b m : ℕ} (B : Module.Basis (Fin m) X.functionField (RationalForms K X b))

/-- The rational `b`-forms on `W` whose coefficients in `B` are regular at every point of `W`. -/
noncomputable def basisLatticeSections (W : X.Opens) :
    Submodule Γ(X, W) Γ(rationalFormsSheaf K X b, W) where
  carrier := {s | ∀ (x : X) (hx : x ∈ W), haveI : Nonempty W := ⟨⟨x, hx⟩⟩
    ∀ j, B.repr (rationalFormsSectionsEquiv K b W s) j ∈
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

/-- **The lattice of a basis**, a subsheaf of modules of the rational `b`-forms on all of `X`. -/
noncomputable def basisLatticeSubmodule : (rationalFormsSheaf K X b).Submodule where
  obj W := basisLatticeSections B W.unop
  map {W V} i := fun s hs x hx => by
    have : Nonempty V.unop := ⟨⟨x, hx⟩⟩
    have : Nonempty W.unop := ⟨⟨x, i.unop.le hx⟩⟩
    have h := rationalFormsSectionsEquiv_map K b i.unop s
    change ∀ j, B.repr (rationalFormsSectionsEquiv K b V.unop
      ((rationalFormsSheaf K X b).presheaf.map i.unop.op s)) j ∈ _
    rw [h]
    exact hs x (i.unop.le hx)
  isSheaf {U} s hs := by
    intro x hx
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFormsSheaf K X b).presheaf.map i.op s ∈ basisLatticeSections B V := hi
    rw [← rationalFormsSectionsEquiv_map K b i s]
    exact hi' x hxV

/-- The basis forms as global sections of the rational forms. -/
noncomputable def basisSection (j : Fin m) : Γ(rationalFormsSheaf K X b, ⊤) :=
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  (rationalFormsSectionsEquiv K b ⊤).symm (B j)

/-- `𝒪_X^m → (rational b-forms)`, given by the basis forms. -/
noncomputable def basisLatticeMap : CohomologyAux.unitBiproduct X m ⟶ rationalFormsSheaf K X b :=
  biproduct.desc fun j => CohomologyAux.homOfSection _ (basisSection B j)

theorem basisLatticeMap_ι_app (j : Fin m) (W : X.Opens) (r : Γ(X, W)) :
    (basisLatticeMap B).app W
        ((biproduct.ι (fun _ : Fin m => CohomologyAux.unitModule X) j).app W r) =
      r • (rationalFormsSheaf K X b).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (basisSection B j) := by
  change (biproduct.ι (fun _ : Fin m => CohomologyAux.unitModule X) j ≫ basisLatticeMap B).app W r = _
  rw [basisLatticeMap, biproduct.ι_desc]
  exact CohomologyAux.homOfSection_app _ _ W r

theorem rationalFormsSectionsEquiv_basisLatticeMap_ι (j : Fin m) (W : X.Opens) [Nonempty W]
    (r : Γ(X, W)) :
    rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W
        ((biproduct.ι (fun _ : Fin m => CohomologyAux.unitModule X) j).app W r)) =
      X.germToFunctionField W r • B j := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  rw [basisLatticeMap_ι_app, rationalFormsSectionsEquiv_smul,
    rationalFormsSectionsEquiv_map K b (homOfLE le_top : W ⟶ ⊤), basisSection,
    AddEquiv.apply_symm_apply]

theorem rationalFormsSectionsEquiv_basisLatticeMap (W : X.Opens) [Nonempty W]
    (x : Γ(CohomologyAux.unitBiproduct X m, W)) :
    rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W x) =
      ∑ j, X.germToFunctionField W
        ((biproduct.π (fun _ : Fin m => CohomologyAux.unitModule X) j).app W x) • B j := by
  conv_lhs => rw [unitBiproduct_sections_eq_sum m W x]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => rationalFormsSectionsEquiv_basisLatticeMap_ι B j W _

theorem basis_repr_sum_smul (f : Fin m → X.functionField) (j : Fin m) :
    B.repr (∑ i, f i • B i) j = f j := by
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem basisLatticeMap_mem (W : (X.Opens)ᵒᵖ)
    (x : (CohomologyAux.unitBiproduct X m).val.obj W) :
    (basisLatticeMap B).val.app W x ∈ (basisLatticeSubmodule B).obj W := by
  induction W using Opposite.rec with | op W => ?_
  intro y hy
  have : Nonempty W := ⟨⟨y, hy⟩⟩
  intro j
  change B.repr (rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W x)) j ∈ _
  rw [rationalFormsSectionsEquiv_basisLatticeMap, basis_repr_sum_smul,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := W) hy]
  exact ⟨_, rfl⟩

theorem basisLatticeMap_injective (W : (X.Opens)ᵒᵖ) :
    Function.Injective ((basisLatticeMap B).val.app W) := by
  induction W using Opposite.rec with | op W => ?_
  intro x x' h
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (CohomologyAux.unitBiproduct X m) hbot) _ _
  · have h' : rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W x) =
        rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W x') := congrArg _ h
    rw [rationalFormsSectionsEquiv_basisLatticeMap, rationalFormsSectionsEquiv_basisLatticeMap] at h'
    have hc : ∀ j, (biproduct.π (fun _ : Fin m => CohomologyAux.unitModule X) j).app W x
        = (biproduct.π (fun _ : Fin m => CohomologyAux.unitModule X) j).app W x' := by
      intro j
      apply Scheme.germToFunctionField_injective X W
      have := congrArg (fun ω => B.repr ω j) h'
      simpa only [basis_repr_sum_smul] using this
    rw [unitBiproduct_sections_eq_sum m W x, unitBiproduct_sections_eq_sum m W x']
    exact Finset.sum_congr rfl fun j _ => by rw [hc j]

theorem basisLatticeMap_surjective (W : (X.Opens)ᵒᵖ)
    (s : (rationalFormsSheaf K X b).val.obj W) (hs : s ∈ (basisLatticeSubmodule B).obj W) :
    ∃ t, (basisLatticeMap B).val.app W t = s := by
  induction W using Opposite.rec with | op W => ?_
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact ⟨0, @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (rationalFormsSheaf K X b) hbot) _ _⟩
  · have hreg : ∀ j, ∃ a : Γ(X, W), X.germToFunctionField W a =
        B.repr (rationalFormsSectionsEquiv K b W s) j := fun j =>
      exists_germToFunctionField_eq_of_forall_mem_range fun y hy => hs y hy j
    choose a ha using hreg
    refine ⟨∑ j, (biproduct.ι (fun _ : Fin m => CohomologyAux.unitModule X) j).app W (a j), ?_⟩
    apply (rationalFormsSectionsEquiv K b W).injective
    change rationalFormsSectionsEquiv K b W ((basisLatticeMap B).app W _) = _
    rw [map_sum, map_sum]
    conv_rhs => rw [← B.sum_repr (rationalFormsSectionsEquiv K b W s)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rationalFormsSectionsEquiv_basisLatticeMap_ι, ha j]

/-- **The lattice of a basis is free**: `𝒪_X^m ≅ lattice`. -/
noncomputable def basisLatticeIso :
    CohomologyAux.unitBiproduct X m ≅ (basisLatticeSubmodule B).toSheafOfModules :=
  haveI := TauCeti.SheafOfModules.isIso_liftToSubmodule (basisLatticeSubmodule B)
    (basisLatticeMap B) (basisLatticeMap_mem B) (basisLatticeMap_injective B)
    (basisLatticeMap_surjective B)
  asIso (TauCeti.SheafOfModules.liftToSubmodule (basisLatticeSubmodule B) (basisLatticeMap B)
    (basisLatticeMap_mem B))

/-- The sections of the lattice of a basis are finitely generated. -/
theorem finite_basisLatticeSections (W : X.Opens) :
    Module.Finite Γ(X, W) (basisLatticeSections B W) := by
  have := CohomologyAux.finite_sections_unitBiproduct (X := X) m W
  let f : Γ(CohomologyAux.unitBiproduct X m, W) →ₗ[Γ(X, W)] basisLatticeSections B W :=
    LinearMap.codRestrict (basisLatticeSections B W) ((basisLatticeMap B).val.app (op W)).hom
      (fun x => basisLatticeMap_mem B (op W) x)
  refine Module.Finite.of_surjective f fun s => ?_
  obtain ⟨t, ht⟩ := basisLatticeMap_surjective B (op W) s.1 s.2
  exact ⟨t, Subtype.ext ht⟩

end BasisLattice

section SNC

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

/-- The logarithmic wedge basis of a chart, indexed by `Fin (wedgeRank n b)`. -/
noncomputable abbrev logChartFormsFinBasis (c : EtaleChart K X n) (σ : Fin r → Option (Fin n))
    (b : ℕ) : Module.Basis (Fin (wedgeRank n b)) X.functionField (RationalForms K X b) :=
  (logChartFormsBasis c σ b).reindex (Fintype.equivFin _)

include hnorm hinj hξ hEc in
/-- **Over a simple normal crossing chart, `Ω^b_X(log E)` is the lattice of the logarithmic wedge
basis.** -/
theorem logFormsSections_zero_eq_basisLatticeSections (c : EtaleChart K X n)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (b : ℕ) {W : X.Opens} (hW : W ≤ c.U) :
    logFormsSections K E 0 b W = basisLatticeSections (logChartFormsFinBasis c σ b) W := by
  ext s
  rw [mem_logFormsSections_iff_exists]
  constructor
  · intro hs x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    intro j
    obtain ⟨f, hf, hmem⟩ := hs x hx
    rw [smul_mem_logFormsLattice_iff_of_isLocalEquationAt E hf
      (CartierDivisor.isLocalEquationAt_zero x), Units.val_one, one_smul] at hmem
    have h := (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x (hW hx) b _).mp hmem
    rw [Module.Basis.repr_reindex_apply]
    exact h _
  · intro hs x hx
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    refine ⟨1, CartierDivisor.isLocalEquationAt_zero x, ?_⟩
    rw [Units.val_one, one_smul]
    refine (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x (hW hx) b _).mpr fun t => ?_
    have h := hs x hx (Fintype.equivFin _ t)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at h
    exact h

include hnorm hinj hξ hEc in
/-- **Over a simple normal crossing chart, `Ω^b_X(log E)` is `𝒪^r`.** -/
noncomputable def logFormsOverChartIso (c : EtaleChart K X n) (σ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (b : ℕ) :
    (logFormsSheaf K E 0 b).over c.U ≅ (CohomologyAux.unitBiproduct X (wedgeRank n b)).over c.U :=
  SheafOfModules.Submodule.overIsoOfEq (logFormsSubmodule K E 0 b)
      (basisLatticeSubmodule (logChartFormsFinBasis c σ b)) c.U
      (fun _ i => logFormsSections_zero_eq_basisLatticeSections hnorm ξ hinj hξ E hEc c σ hc b
        i.le) ≪≫
    (SheafOfModules.overFunctor _ c.U).mapIso (basisLatticeIso (logChartFormsFinBasis c σ b)).symm

omit [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
/-- The simple normal crossing charts cover `X`. -/
theorem iSup_sncCharts_eq_top (hsnc : IsSNCFamily K n ξ) :
    ⨆ i : {c : EtaleChart K X n // ∃ σ, IsSNCChart c ξ σ}, i.1.U = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  exact ⟨⟨c, σ, hc⟩, hx⟩

include hnorm hinj hξ hEc in
/-- **`Ω^b_X(log E)` is quasi-coherent.** -/
theorem isQuasicoherent_logFormsSheaf_zero (hsnc : IsSNCFamily K n ξ) (b : ℕ) :
    (logFormsSheaf K E 0 b).IsQuasicoherent := by
  have h : ∀ i : {c : EtaleChart K X n // ∃ σ, IsSNCChart c ξ σ},
      ((logFormsSheaf K E 0 b).over i.1.U).IsQuasicoherent := fun i => by
    obtain ⟨⟨q⟩⟩ := SheafOfModules.isQuasicoherent_over
      (CohomologyAux.unitBiproduct X (wedgeRank n b)) i.1.U
    exact (q.ofIsIso (logFormsOverChartIso hnorm ξ hinj hξ E hEc i.1 i.2.choose i.2.choose_spec
      b).inv).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop (C := X.Opens)
    (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (logFormsSheaf K E 0 b)
    (fun i : {c : EtaleChart K X n // ∃ σ, IsSNCChart c ξ σ} => i.1.U)
    ((Opens.coversTop_iff X _).mpr (IsOpenCover.mk (iSup_sncCharts_eq_top ξ hsnc)))

include hnorm hinj hξ hEc in
/-- **`Ω^b_X(log E)` is coherent.** -/
theorem isCoherent_logFormsSheaf_zero (hsnc : IsSNCFamily K n ξ) (b : ℕ) :
    (logFormsSheaf K E 0 b).IsCoherent := by
  have := isQuasicoherent_logFormsSheaf_zero hnorm ξ hinj hξ E hEc hsnc b
  refine ⟨inferInstance, CohomologyAux.isFiniteType_of_finite_sections _
    (fun i : {c : EtaleChart K X n // ∃ σ, IsSNCChart c ξ σ} => i.1.U)
    (iSup_sncCharts_eq_top ξ hsnc) (fun i => i.1.isAffine) fun i => ?_⟩
  have h := finite_basisLatticeSections (logChartFormsFinBasis i.1 i.2.choose b) i.1.U
  rw [← logFormsSections_zero_eq_basisLatticeSections hnorm ξ hinj hξ E hEc i.1 i.2.choose
    i.2.choose_spec b le_rfl] at h
  exact h

end SNC

end MixedFujita
