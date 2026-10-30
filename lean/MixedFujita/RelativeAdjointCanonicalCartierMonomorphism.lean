/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeAdjointGenericDirectImage
public import MixedFujita.CartierProjectionFormula
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! Transport an actual roundup monomorphism through the global Cartier
projection formula and an exact principal adjoint presentation. All multiples
use the same actual Cartier correction and retain the original principal power. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {B T : Scheme.{u}} [IsIntegral B] [IsIntegral T]
  [B.Over (Spec (CommRingCat.of K))]

/-- An exact adjoint principal presentation transfers an actual roundup map
to a global map with a fixed actual Cartier correction. -/
noncomputable def relativeAdjointCanonicalCartierHom
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) :
    (Scheme.Modules.pushforward q).obj (L + E).sheaf ⟶ (A + C).sheaf :=
  ((Scheme.Modules.pushforward q).mapIso
    (tensorIso (projectivePrincipalPullbackSheafIso hProj q A L χ hL) (Iso.refl E.sheaf) ≪≫
      cartierTensorSheafIso L E)).inv ≫
    (cartierProjectionFormulaIso A q E.sheaf).inv ≫
    (cartierTwistFunctor A).map α ≫ (cartierTensorSheafIso A C).hom

theorem relativeAdjointCanonicalCartierHom_mono
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) [Mono α] :
    Mono (relativeAdjointCanonicalCartierHom hProj q A L E C χ hL α) := by
  dsimp only [relativeAdjointCanonicalCartierHom]
  infer_instance

theorem relativeAdjointCanonicalCartierHom_app_injective
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) [Mono α]
    (U : B.Opens) :
    Function.Injective (Scheme.Modules.Hom.app
      (relativeAdjointCanonicalCartierHom hProj q A L E C χ hL α) U) := by
  letI := relativeAdjointCanonicalCartierHom_mono hProj q A L E C χ hL α
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget _).map
      (relativeAdjointCanonicalCartierHom hProj q A L E C χ hL α)) (op U)

/-- All further multiples use the same correction C and retain χ^j. -/
noncomputable def relativeAdjointMultipleCanonicalCartierHom
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) (j : ℕ) :
    (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ⟶ (j • A + C).sheaf :=
  relativeAdjointCanonicalCartierHom hProj q (j • A) (j • L) E C (χ ^ j)
    (by simpa only [cartierPullback_nsmul] using
      cartier_principal_presentation_nsmul L (cartierPullback q A) χ hL j) α

theorem relativeAdjointMultipleCanonicalCartierHom_mono
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) [Mono α] (j : ℕ) :
    Mono (relativeAdjointMultipleCanonicalCartierHom hProj q A L E C χ hL α j) :=
  relativeAdjointCanonicalCartierHom_mono _ _ _ _ _ _ _ _ _

theorem relativeAdjointMultipleCanonicalCartierHom_app_injective
    (hProj : ∃ J : CartierDivisor B, CartierIsAmpleProj K J)
    (q : T ⟶ B) [IsDominant q] (A : CartierDivisor B) (L E : CartierDivisor T)
    (C : CartierDivisor B) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) [Mono α]
    (j : ℕ) (U : B.Opens) :
    Function.Injective (Scheme.Modules.Hom.app
      (relativeAdjointMultipleCanonicalCartierHom hProj q A L E C χ hL α j) U) := by
  letI := relativeAdjointMultipleCanonicalCartierHom_mono hProj q A L E C χ hL α j
  exact PresheafOfModules.injective_of_mono
    ((SheafOfModules.forget _).map
      (relativeAdjointMultipleCanonicalCartierHom hProj q A L E C χ hL α j)) (op U)

end MixedFujita
