/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalCartierPushforwardIso
public import MixedFujita.CartierProjectionFormula

/-!
Twisting the actual rank-one direct-image isomorphism by any Cartier sheaf
gives the corresponding direct-image isomorphism after pullback and tensor.
Use the already proved projection formula, with the same exceptional divisor
and the same maps; a twisted direct-image identity is not an extra input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
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

/-- All Cartier twists of the actual exceptional direct-image identity. -/
noncomputable def effectiveExceptionalCartierTwistedPushforwardIso (D : CartierDivisor X) :
    D.sheaf ≅ (Scheme.Modules.pushforward π).obj
      ((Scheme.Modules.pullback π).obj D.sheaf ⊗ E.sheaf) :=
  (rightUnitor D.sheaf).symm ≪≫
    tensorIso (Iso.refl D.sheaf) (effectiveExceptionalCartierPushforwardUnitIso hnorm hnormT π hπ E hEff hE) ≪≫
    cartierProjectionFormulaIso D π E.sheaf

/-- All Cartier twists on the final Stein base use the same actual exceptional divisor. -/
noncomputable def steinExceptionalCartierTwistedPushforwardIso
    {Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (happ : ∀ V : Y.Opens, Function.Surjective (f.app V).hom) (D : CartierDivisor Y) :
    D.sheaf ≅ (Scheme.Modules.pushforward (π ≫ f)).obj
      ((Scheme.Modules.pullback (π ≫ f)).obj D.sheaf ⊗ E.sheaf) :=
  (rightUnitor D.sheaf).symm ≪≫
    tensorIso (Iso.refl D.sheaf)
      (steinExceptionalCartierPushforwardUnitIso hnorm hnormT π hπ E hEff hE f happ) ≪≫
    cartierProjectionFormulaIso D (π ≫ f) E.sheaf

end MixedFujita
