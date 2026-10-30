/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafAffineModulePresentation
public import MixedFujita.SGATwistPullbackIso

/-! 有限自由加群・実層とアフィン切断加群の同型辞書。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The finite free sheaf in the cohomology library is the standard free
sheaf on the same finite number of generators. -/
noncomputable def unitBiproductIsoFree (X : Scheme.{u}) (k : ℕ) :
    CohomologyAux.unitBiproduct X k ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin k)) :=
  ((Sigma.whiskerEquiv (f := fun _ : ULift.{u} (Fin k) => CohomologyAux.unitModule X)
    (g := fun _ : Fin k => CohomologyAux.unitModule X) Equiv.ulift fun _ => Iso.refl _) ≪≫
      (biproduct.isoCoproduct fun _ : Fin k => CohomologyAux.unitModule X).symm).symm


/-- An actual finite free affine module gives the finite free sheaf of its
actual rank, with no module presentation supplied by the caller. -/
noncomputable def tildeUnitBiproductIso
    {R : CommRingCat.{u}} [Nontrivial R] (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] :
    tilde M ≅ CohomologyAux.unitBiproduct (Spec R) (Module.finrank R M) :=
  (tilde.functor R).mapIso
    ((Module.finBasis R M).reindex (Equiv.ulift.symm)).repr.toModuleIso ≪≫
      tildeFinsupp _ ≪≫ (unitBiproductIsoFree (Spec R) (Module.finrank R M)).symm


/-- Any actual affine section-module isomorphism yields an actual module
isomorphism on the affine open, using the proved affine tilde dictionary. -/
noncomputable def moduleAffineOpenIsoOfSections
    {X : Scheme.{u}} (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : X.affineOpens) (a : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1)) :
    (Scheme.Modules.pullback U.1.ι).obj M ≅ (Scheme.Modules.pullback U.1.ι).obj N := by
  let h := U.2.isoSpec.hom
  let b (G : X.Modules) : (Scheme.Modules.pullback U.1.ι).obj G ≅
      (Scheme.Modules.pullback h).obj (G.restrict U.2.fromSpec) :=
    Scheme.Modules.pullbackCompIso' h U.2.fromSpec U.1.ι U.2.isoSpec_hom_fromSpec G ≪≫
      (Scheme.Modules.pullback h).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app G).symm
  exact b M ≪≫ (Scheme.Modules.pullback h).mapIso
    (moduleAffineTildeIso M U ≪≫ (tilde.functor _).mapIso a.toModuleIso ≪≫
      (moduleAffineTildeIso N U).symm) ≪≫ (b N).symm

end MixedFujita
