/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantRoundupDirectImageIso
public import MixedFujita.CartierNegativeGradedPullback

/-! Effective Cartier units supply the actual divisor/module pullback
dictionary. Inverse Cartier cancellation then identifies a negative twist
of an actual Cartier direct image with another actual Cartier direct image.
No nonzero global section of the negative divisor is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

noncomputable def effectiveCartierPullbackModuleIso
    {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective) :
    (Scheme.Modules.pullback β).obj C.sheaf ≅ (cartierPullback β C).sheaf :=
  Classical.choice (cartierPullback_sheaf_iso_modulePullback β C
    (Scheme.Modules.Hom.app (C.unitToSheaf hC) ⊤ (1 : Γ(B, ⊤)))
    (effectiveCartier_unit_global_section_ne_zero C hC))

noncomputable def effectiveCartierDirectImageUntwistIso
    {B T : Scheme.{u}} [IsIntegral B] [IsIntegral T]
    (q : T ⟶ B) [IsDominant q] (D : CartierDivisor B) (hD : D.IsEffective)
    (E : CartierDivisor T) :
    (-D).sheaf ⊗ (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward q).obj (E - cartierPullback q D).sheaf :=
  cartierProjectionFormulaIso (-D) q E.sheaf ≪≫
    (Scheme.Modules.pushforward q).mapIso
      (tensorIso (cartierPullbackNegativeIso D q (cartierPullback q D)
          (effectiveCartierPullbackModuleIso q D hD)) (Iso.refl E.sheaf) ≪≫
        cartierTensorSheafIso (-(cartierPullback q D)) E ≪≫
          eqToIso (congrArg CartierDivisor.sheaf
            (show -(cartierPullback q D) + E = E - cartierPullback q D by abel)))

end MixedFujita
