/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing

/-! 実Cartier層と任意の連接層のテンソル連接性。 See reports/check-217-semiample-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring an actual coherent module by any actual Cartier sheaf is coherent. -/
theorem cartierTensorModule_isCoherent
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (M : X.Modules) [M.IsCoherent] : (D.sheaf ⊗ M).IsCoherent := by
  let L := cartierSGALineBundle D
  let a : L.twist M 1 ≅ D.sheaf ⊗ M :=
    (sgaTwistTensorIso L M 1).symm ≪≫ tensorIso (cartierSGAModuleIso D).symm (Iso.refl M)
  let : (L.twist M 1).IsCoherent := inferInstance
  let : (L.twist M 1).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (L.twist M 1).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩

end MixedFujita
