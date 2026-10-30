/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGATwistPullbackIso
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.CartierTwistExactness

/-! 非整・非被約源上の実Cartier引き戻し捻りの連接性と完全性。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The SGA line power of a pulled Cartier bundle is its original actual
module pullback, on arbitrary, possibly nonintegral sources. -/
noncomputable def cartierPulledSheafSGAPowerOneIso
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (p : Y ⟶ X) :
    ((cartierSGALineBundle D).pullback p).toModules 1 ≅
      (Scheme.Modules.pullback p).obj D.sheaf :=
  (sgaLineBundlePullbackPowerIso (cartierSGALineBundle D) p 1).symm ≪≫
    (Scheme.Modules.pullback p).mapIso (cartierSGAModuleIso D).symm


/-- Actual pulled Cartier tensor twists equal SGA twists even when the
source is nonintegral or nonreduced. -/
noncomputable def cartierPulledTensorSGATwistIso
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (p : Y ⟶ X) (M : Y.Modules) :
    ((cartierSGALineBundle D).pullback p).twist M 1 ≅
      (cartierPullbackTwistFunctor D p).obj M :=
  (sgaTwistTensorIso _ M 1).symm ≪≫
    tensorIso (cartierPulledSheafSGAPowerOneIso D p) (Iso.refl M)


/-- The pulled Cartier twist of every coherent module is coherent, with no
integrality hypothesis on the source. -/
theorem cartierPulledTensor_isCoherent
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (p : Y ⟶ X)
    (M : Y.Modules) [M.IsCoherent] : ((cartierPullbackTwistFunctor D p).obj M).IsCoherent := by
  let L := (cartierSGALineBundle D).pullback p
  let a := cartierPulledTensorSGATwistIso D p M
  let : (L.twist M 1).IsCoherent := inferInstance
  let : (L.twist M 1).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (L.twist M 1).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩


/-- Pulling an actual Cartier bundle to any source still gives an exact
invertible tensor functor. -/
theorem cartierPullbackTwistFunctor_isEquivalence
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (p : Y ⟶ X) :
    (cartierPullbackTwistFunctor D p).IsEquivalence :=
  inferInstanceAs (cartierPullbackTwistEquivalence D p).functor.IsEquivalence

attribute [instance] cartierPullbackTwistFunctor_isEquivalence


/-- Pulled Cartier tensor twists preserve the actual short exact sequence
on every source, using the existing inverse Cartier twist equivalence. -/
theorem cartierPulledTensor_shortExact
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (p : Y ⟶ X)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact) :
    (S.map (cartierPullbackTwistFunctor D p)).ShortExact := by
  exact hS.map_of_exact _

end MixedFujita
