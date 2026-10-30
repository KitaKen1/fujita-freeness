/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.UniformTwistedChangedComparison
public import MixedFujita.RelativeAdjointUniformImageIdeal
public import MixedFujita.BlowUpSequenceAmpleModel
public import MixedFujita.BirationalComposition

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]

/-- The original principal witness is preserved under the actual commuting
square. No projectivity of either source scheme is needed. -/
theorem relativeAdjointPullbackPrincipalPresentation
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A : CartierDivisor B) (L : CartierDivisor T) (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ) :
    cartierPullback τ L = cartierPullback q' (cartierPullback β A) +
      principalCartierDivisor T' (Units.map (dominantFunctionFieldMap τ).hom.toMonoidHom χ) := by
  simpa only [one_smul] using
    cartier_presentation_of_compatible_modification τ q β q' hsquare.symm L A 1 χ
      (by simpa only [one_smul] using hL)

noncomputable def changedRelativeAdjointMultipleSheafIso
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A : CartierDivisor B) (L : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ) (j : ℕ) :
    (cartierPullback q' (cartierPullback β (j • A)) + E').sheaf ≅
      (j • cartierPullback τ L + E').sheaf := by
  let χ' := Units.map (dominantFunctionFieldMap τ).hom.toMonoidHom χ
  have hp := cartier_principal_presentation_nsmul (cartierPullback τ L)
    (cartierPullback q' (cartierPullback β A)) χ'
    (relativeAdjointPullbackPrincipalPresentation q β q' τ hsquare A L χ hL) j
  have heq : j • cartierPullback τ L + E' =
      (cartierPullback q' (cartierPullback β (j • A)) + E') +
        principalCartierDivisor T' (χ' ^ j) := by
    rw [hp, cartierPullback_nsmul, cartierPullback_nsmul]
    abel
  exact (cartierSheafPrincipalShiftIso
    (cartierPullback q' (cartierPullback β (j • A)) + E') (χ' ^ j)).symm ≪≫
      eqToIso (congrArg CartierDivisor.sheaf heq.symm)

/-- An actual pushback isomorphism for the original relative-adjoint multiple
and the actual pulled divisor on the changed source. -/
noncomputable def actualRelativeAdjointChangedMultiplePushforwardIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData)
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    (j : ℕ) :
    (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj
        (j • cartierPullback τ L + E').sheaf) :=
  relativeAdjointChangedMultiplePushforwardIso hProj hProj' q β q' A C L E E' χ hL I s e j ≪≫
    (Scheme.Modules.pushforward β).mapIso ((Scheme.Modules.pushforward q').mapIso
      (changedRelativeAdjointMultipleSheafIso q β q' τ hsquare A L E' χ hL j))

theorem actualRelativeAdjointChangedMultipleComparison_uniform_actual_image_iso
    [IsLocallyNoetherian B']
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf)) :
    ∀ j : ℕ, Nonempty ((j • cartierPullback β A + (cartierPullback β C - P)).sheaf ≅
      image (changedRoundupBaseChangeMap β
        (actualRelativeAdjointChangedMultiplePushforwardIso hProj hProj' q β q' τ hsquare
          A C L E E' χ hL I s e j))) := by
  intro j
  let sj := relativeAdjointMultipleDirectImageIsoOfIdealPresentation hProj q A L E C χ hL I s j
  let ej := actualRelativeAdjointChangedMultiplePushforwardIso hProj hProj' q β q' τ hsquare
    A C L E E' χ hL I s e j
  obtain ⟨i⟩ := projectiveChangedRoundup_principalized_actual_image_iso hProj hProj' I hI β
    (j • A + C) sj P hP hIP q' (j • cartierPullback τ L + E') ej
  have heq : j • cartierPullback β A + (cartierPullback β C - P) =
      cartierPullback β (j • A + C) - P := by
    rw [cartierPullback_add, cartierPullback_nsmul]
    abel
  exact ⟨eqToIso (congrArg CartierDivisor.sheaf heq) ≪≫ i⟩

end MixedFujita
