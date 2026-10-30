/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeAdjointCanonicalCartierMonomorphism
public import MixedFujita.CartierTargetImageIdeal

/-! Use the actual ideal presentation of F to
identify every relative-adjoint direct image with a twist of one fixed I. -/

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

noncomputable def relativeAdjointDirectImageIsoOfIdealPresentation
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData)
    (eF : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I) :
    (Scheme.Modules.pushforward q).obj (L + E).sheaf ≅
      (A + C).sheaf ⊗ idealSheafDataModule I :=
  ((Scheme.Modules.pushforward q).mapIso
    (tensorIso (projectivePrincipalPullbackSheafIso hProj q A L χ hL) (Iso.refl E.sheaf) ≪≫
      cartierTensorSheafIso L E)).symm ≪≫
    (cartierProjectionFormulaIso A q E.sheaf).symm ≪≫
    tensorIso (Iso.refl A.sheaf) eF ≪≫
    (α_ A.sheaf C.sheaf (idealSheafDataModule I)).symm ≪≫
    tensorIso (cartierTensorSheafIso A C) (Iso.refl (idealSheafDataModule I))

noncomputable def relativeAdjointMultipleDirectImageIsoOfIdealPresentation
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData)
    (eF : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (j : ℕ) :
    (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
      (j • A + C).sheaf ⊗ idealSheafDataModule I :=
  relativeAdjointDirectImageIsoOfIdealPresentation hProj q (j • A) (j • L) E C (χ ^ j)
    (by simpa only [cartierPullback_nsmul] using
      cartier_principal_presentation_nsmul L (cartierPullback q A) χ hL j) I eF

end MixedFujita

