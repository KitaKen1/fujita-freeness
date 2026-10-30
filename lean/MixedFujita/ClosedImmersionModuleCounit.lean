/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! 閉埋め込みの実加群余単位の全射性。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A topologically inducing scheme morphism has faithful actual module
pushforward, since every source open is an inverse image of a target open. -/
theorem schemeModules_pushforward_faithful_of_isInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f) :
    (Scheme.Modules.pushforward f).Faithful where
  map_injective := by
    intro M N a b hab
    apply Scheme.Modules.hom_ext
    intro U
    obtain ⟨V, hV, heq⟩ := hf.isOpen_iff.mp U.isOpen
    let W : Y.Opens := ⟨V, hV⟩
    have hUW : f ⁻¹ᵁ W = U := SetLike.coe_injective heq
    subst U
    have h := congrArg (fun g => Scheme.Modules.Hom.app g W) hab
    ext s
    exact ConcreteCategory.congr_hom h s


/-- The actual pullback/pushforward counit along a closed immersion is epic.
This only needs faithful pushforward, rather than a chosen tensor presentation. -/
theorem closedImmersion_module_counit_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  let := schemeModules_pushforward_faithful_of_isInducing f f.isClosedEmbedding.isInducing
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).counit_epi_of_R_faithful M

end MixedFujita
