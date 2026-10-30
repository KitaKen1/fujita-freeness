/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveCartierPullbackDictionary
public import MixedFujita.CrepantRelativeAdjointCartier
public import MixedFujita.CartierSectionDivisor
public import MixedFujita.CartierGradedPullback

/-! Use the original base's projectivity to identify an actual moduli pullback
with a principal translate of an actual relative adjoint. Tensor with the same
rounded discrepancy and push forward. Every further multiple uses the supplied
proved Cartier-twist isomorphism on the same generic open, with no positivity
or global-section hypothesis on the moduli divisor. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {B T : Scheme.{u}} [IsIntegral B] [IsIntegral T]
  [B.Over (Spec (CommRingCat.of K))]

/-- An actual principal presentation identifies the actual module pullback with its adjoint sheaf. -/
noncomputable def projectivePrincipalPullbackSheafIso
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L : CartierDivisor T)
    (χ : T.functionFieldˣ) (hL : L = cartierPullback q A + principalCartierDivisor T χ) :
    (Scheme.Modules.pullback q).obj A.sheaf ≅ L.sheaf :=
  projectiveCartierPullbackIso hProj q A ≪≫
    (cartierSheafPrincipalShiftIso (cartierPullback q A) χ).symm ≪≫
    eqToIso (congrArg CartierDivisor.sheaf hL.symm)

/-- Transfer the same actual Cartier-twist direct image to the actual adjoint-plus-rounding divisor. -/
noncomputable def relativeAdjointDirectImageIsoOfTwist
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (U : B.Opens)
    (A : CartierDivisor B) (L E : CartierDivisor T) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (e : A.sheaf.restrict U.ι ≅
      ((Scheme.Modules.pushforward q).obj
        ((Scheme.Modules.pullback q).obj A.sheaf ⊗ E.sheaf)).restrict U.ι) :
    A.sheaf.restrict U.ι ≅ ((Scheme.Modules.pushforward q).obj (L + E).sheaf).restrict U.ι :=
  e ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso
    ((Scheme.Modules.pushforward q).mapIso
      (tensorIso (projectivePrincipalPullbackSheafIso hProj q A L χ hL) (Iso.refl E.sheaf) ≪≫
        cartierTensorSheafIso L E))

/-- All further multiples identify actual moduli sheaves with actual relative-adjoint direct images
on the same generic open, using the same rounded divisor. -/
noncomputable def relativeAdjointMultipleDirectImageIso
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (U : B.Opens)
    (A : CartierDivisor B) (L E : CartierDivisor T) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (htwists : ∀ F : CartierDivisor B,
      Nonempty (F.sheaf.restrict U.ι ≅
        ((Scheme.Modules.pushforward q).obj
          ((Scheme.Modules.pullback q).obj F.sheaf ⊗ E.sheaf)).restrict U.ι))
    (j : ℕ) :
    (j • A).sheaf.restrict U.ι ≅
      ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf).restrict U.ι :=
  relativeAdjointDirectImageIsoOfTwist hProj q U (j • A) (j • L) E (χ ^ j)
    (by simpa only [cartierPullback_nsmul] using
      cartier_principal_presentation_nsmul L (cartierPullback q A) χ hL j)
    (Classical.choice (htwists (j • A)))

end MixedFujita
