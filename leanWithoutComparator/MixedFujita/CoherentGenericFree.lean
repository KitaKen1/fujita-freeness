/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GenericModuleFreeAway
public import MixedFujita.FiniteFreeModuleSheafIso

/-! 整な局所Noether源の連接層の実非空開上有限自由化。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual freeness after an open immersion transfers to its actual image
open; the inverse image isomorphism is constructed from the scheme iso. -/
noncomputable def moduleOpenImageFreeIso
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] (M : Y.Modules) (k : ℕ)
    (a : (Scheme.Modules.pullback j).obj M ≅ CohomologyAux.unitBiproduct Z k) :
    (Scheme.Modules.pullback j.opensRange.ι).obj M ≅
      CohomologyAux.unitBiproduct j.opensRange.toScheme k :=
  Scheme.Modules.pullbackCompIso' j.isoOpensRange.inv j j.opensRange.ι
    j.isoOpensRange_inv_comp M ≪≫
      (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso a ≪≫
        modulePullbackUnitBiproductIso j.isoOpensRange.inv k


/-- Any coherent module on an integral locally noetherian scheme is
ACTUALLY finite free on a nonempty open, with the rank and isomorphism
constructed internally from fraction-field localization. -/
theorem coherent_exists_nonempty_open_unitBiproduct_iso
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (M : Y.Modules) [M.IsCoherent] :
    ∃ (W : Y.Opens), (W : Set Y).Nonempty ∧ ∃ k : ℕ,
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ CohomologyAux.unitBiproduct W.toScheme k) := by
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  obtain ⟨V, hV, hxU, _⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  let U : Y.affineOpens := ⟨V, hV⟩
  let : Nonempty U.1 := ⟨⟨genericPoint Y, hxU⟩⟩
  let R := Γ(Y, U.1)
  let N : ModuleCat.{u} R := ModuleCat.of R Γ(M, U.1)
  let : IsDomain R := inferInstance
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite R N := CohomologyAux.finite_sections_of_isFiniteType M U.2
  let : Module.FinitePresentation R N := Module.finitePresentation_of_finite R N
  obtain ⟨r, hr, hfree⟩ := finitePresentation_exists_nonzero_free_away_extension N
  let : IsDomain (away r) := Localization.Away.isDomain hr
  let : Module.Free (away r) ((ModuleCat.extendScalars (awayMap r).hom).obj N) := hfree
  let : Algebra R (away r) := (awayMap r).hom.toAlgebra
  let := isLocalization_away r
  let := isScalarTower_extendScalars_away N r
  let := isLocalizedModule_toExtendScalars_awayMap N r
  let : Module.Finite (away r) ((ModuleCat.extendScalars (awayMap r).hom).obj N) :=
    Module.Finite.of_isLocalizedModule (.powers r) (Rₚ := away r)
      (Mₚ := (ModuleCat.restrictScalars (awayMap r).hom).obj
        ((ModuleCat.extendScalars (awayMap r).hom).obj N)) (toExtendScalars N (awayMap r))
  let j : Spec (away r) ⟶ Y := Spec.map (awayMap r) ≫ U.2.fromSpec
  let : IsOpenImmersion j := inferInstance
  let k := Module.finrank (away r) ((ModuleCat.extendScalars (awayMap r).hom).obj N)
  let a : (Scheme.Modules.pullback j).obj M ≅ CohomologyAux.unitBiproduct (Spec (away r)) k :=
    Scheme.Modules.pullbackCompIso' (Spec.map (awayMap r)) U.2.fromSpec j rfl M ≪≫
      (Scheme.Modules.pullback (Spec.map (awayMap r))).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app M).symm ≪≫
          moduleAffineTildeIso M U) ≪≫
      pullbackSpecMapTildeIso (awayMap r) N ≪≫
      tildeUnitBiproductIso ((ModuleCat.extendScalars (awayMap r).hom).obj N)
  refine ⟨j.opensRange, ?_, k, ⟨moduleOpenImageFreeIso j M k a⟩⟩
  let z : Spec (away r) := genericPoint (Spec (away r))
  exact ⟨j z, by change j z ∈ Set.range j; exact ⟨z, rfl⟩⟩

end MixedFujita
