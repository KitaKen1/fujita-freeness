/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! 全整数捻りと実加群引き戻しの自然同型。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the existing all-integer SGA projection formula as a natural iso. -/
noncomputable def sgaTwistPushforwardNatIso
    {X Y : Scheme.{u}} (L : Y.LineBundle) (f : X ⟶ Y) (n : ℤ) :
    Scheme.LineBundle.twistFunctor X (L.pullback f) n ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f ⋙ Scheme.LineBundle.twistFunctor Y L n :=
  NatIso.ofComponents (fun M => L.twistPushforwardIso f M n) (fun {M N} a => by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rfl)


/-- Pullback commutes with every integer twist. This follows by uniqueness of
left adjoints from the proved projection formula for the opposite twist. -/
noncomputable def sgaTwistPullbackNatIso
    {X Y : Scheme.{u}} (L : Y.LineBundle) (f : X ⟶ Y) (n : ℤ) :
    Scheme.LineBundle.twistFunctor Y L n ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ Scheme.LineBundle.twistFunctor X (L.pullback f) n := by
  let a := (Scheme.LineBundle.twistEquivalence Y L n).toAdjunction.comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let b := (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.LineBundle.twistEquivalence X (L.pullback f) n).toAdjunction
  exact a.leftAdjointUniq (b.ofNatIsoRight (sgaTwistPushforwardNatIso L f (-n)))


/-- All integer powers of an SGA line bundle commute with actual module pullback. -/
noncomputable def sgaLineBundlePullbackPowerIso
    {X Y : Scheme.{u}} (L : Y.LineBundle) (f : X ⟶ Y) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (L.toModules n) ≅ (L.pullback f).toModules n :=
  (sgaTwistPullbackNatIso L f n).app (CohomologyAux.unitModule Y) ≪≫
    (Scheme.LineBundle.twistFunctor X (L.pullback f) n).mapIso
      (Scheme.Modules.pullbackObjUnitIso f)


/-- Actual module pullback preserves the finite free sheaf, with its specified
number of summands, on arbitrary schemes. -/
noncomputable def modulePullbackUnitBiproductIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (k : ℕ) :
    (Scheme.Modules.pullback f).obj (CohomologyAux.unitBiproduct Y k) ≅
      CohomologyAux.unitBiproduct X k := by
  let : (Scheme.Modules.pullback f).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isLeftAdjoint
  exact (Scheme.Modules.pullback f).mapBiproduct (fun _ : Fin k => CohomologyAux.unitModule Y) ≪≫
    biproduct.mapIso (fun _ : Fin k => Scheme.Modules.pullbackObjUnitIso f)


/-- A finite sum of arbitrary integer hyperplane powers pulls back to the same
finite sum for the actual pulled line bundle. -/
noncomputable def sgaTwistUnitBiproductPullbackIso
    {X Y : Scheme.{u}} (L : Y.LineBundle) (f : X ⟶ Y) (n : ℤ) (k : ℕ) :
    (Scheme.Modules.pullback f).obj (L.twist (CohomologyAux.unitBiproduct Y k) n) ≅
      (L.pullback f).twist (CohomologyAux.unitBiproduct X k) n :=
  (sgaTwistPullbackNatIso L f n).app (CohomologyAux.unitBiproduct Y k) ≪≫
    (Scheme.LineBundle.twistFunctor X (L.pullback f) n).mapIso
      (modulePullbackUnitBiproductIso f k)

end MixedFujita
