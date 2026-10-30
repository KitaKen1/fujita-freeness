/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierPushforwardUnit
public import MixedFujita.BirationalComposition

/-!
Actual module-sheaf isomorphisms O_X = p_* O_T(E) for effective exceptional
Cartier divisors, and O_Y = (f p)_* O_T(E) after a Stein-type map. All components,
including the empty open, are supplied by the canonical morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
  (π : T ⟶ X) [IsDominant π] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
  (E : CartierDivisor T) (hEff : E.IsEffective)
  (hE : ∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
    cartierCoefficient E (t : T) = 0)

include hnorm hnormT hπ hE

/-- The canonical morphism for an effective exceptional divisor is an actual
module-sheaf isomorphism, by unique section descent and the sheaf axiom. -/
theorem effectiveExceptionalCartierPushforwardUnitMap_isIso :
    IsIso (effectiveCartierPushforwardUnitMap π E hEff) := by
  apply effectiveCartierPushforwardUnitMap_isIso_of_section_criterion
  intro U _ z
  exact effective_exceptional_cartier_section_regular_descent
    hnorm hnormT π hπ E hEff hE U z

/-- The actual canonical direct-image isomorphism of an effective exceptional divisor. -/
noncomputable def effectiveExceptionalCartierPushforwardUnitIso :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pushforward π).obj E.sheaf :=
  letI := effectiveExceptionalCartierPushforwardUnitMap_isIso hnorm hnormT π hπ E hEff hE
  asIso (effectiveCartierPushforwardUnitMap π E hEff)

variable {Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
  (happ : ∀ V : Y.Opens, Function.Surjective (f.app V).hom)

include happ

/-- The canonical direct-image morphism stays an isomorphism after composition
with any dominant Stein-type map with surjective maps on functions on opens. -/
theorem steinExceptionalCartierPushforwardUnitMap_isIso :
    IsIso (effectiveCartierPushforwardUnitMap (π ≫ f) E hEff) := by
  apply effectiveCartierPushforwardUnitMap_isIso_of_section_criterion
  intro V _ z
  have h := effective_exceptional_stein_composite_section_descent
    hnorm hnormT π hπ E hEff hE f happ V z
  simpa only [Scheme.Hom.comp_preimage, dominantFunctionFieldMap_comp,
    CommRingCat.hom_comp, RingHom.comp_apply] using h

/-- The actual canonical direct-image isomorphism on the final Stein base. -/
noncomputable def steinExceptionalCartierPushforwardUnitIso :
    SheafOfModules.unit Y.ringCatSheaf ≅ (Scheme.Modules.pushforward (π ≫ f)).obj E.sheaf :=
  letI := steinExceptionalCartierPushforwardUnitMap_isIso hnorm hnormT π hπ E hEff hE f happ
  asIso (effectiveCartierPushforwardUnitMap (π ≫ f) E hEff)

end MixedFujita
