/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePrincipalizedComparisonImage
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

noncomputable def cartierIdealTwistPresentationIso
    {B : Scheme.{u}} [IsIntegral B] (D C : CartierDivisor B) (I : B.IdealSheafData) :
    D.sheaf ⊗ (C.sheaf ⊗ idealSheafDataModule I) ≅
      (D + C).sheaf ⊗ idealSheafDataModule I :=
  (α_ D.sheaf C.sheaf (idealSheafDataModule I)).symm ≪≫
    tensorIso (cartierTensorSheafIso D C) (Iso.refl _)

variable {K : Type u} [Field K] {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]

noncomputable def projectiveCartierDirectImageTwistIso
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q]
    (D : CartierDivisor B') (E : CartierDivisor T) :
    D.sheaf ⊗ (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward q).obj (cartierPullback q D + E).sheaf :=
  cartierProjectionFormulaIso D q E.sheaf ≪≫
    (Scheme.Modules.pushforward q).mapIso
      (tensorIso (projectiveCartierPullbackIso hProj' q D) (Iso.refl E.sheaf) ≪≫
        cartierTensorSheafIso (cartierPullback q D) E)

noncomputable def changedCartierTwistPushforwardIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (β : B' ⟶ B) [IsDominant β] {T : Scheme.{u}} [IsIntegral T]
    (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T) {F : B.Modules}
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf))
    (D : CartierDivisor B) :
    D.sheaf ⊗ F ≅ (Scheme.Modules.pushforward β).obj
      ((Scheme.Modules.pushforward q).obj (cartierPullback q (cartierPullback β D) + E).sheaf) :=
  tensorIso (Iso.refl D.sheaf) e ≪≫
    cartierProjectionFormulaIso D β ((Scheme.Modules.pushforward q).obj E.sheaf) ≪≫
      (Scheme.Modules.pushforward β).mapIso
        (tensorIso (projectiveCartierPullbackIso hProj β D) (Iso.refl _) ≪≫
          projectiveCartierDirectImageTwistIso hProj' q (cartierPullback β D) E)

noncomputable def presentedChangedCartierTwistPushforwardIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (β : B' ⟶ B) [IsDominant β] {T : Scheme.{u}} [IsIntegral T]
    (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T) {F F' : B.Modules}
    (I : B.IdealSheafData) (C D : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (s' : F' ≅ (D + C).sheaf ⊗ idealSheafDataModule I)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    F' ≅ (Scheme.Modules.pushforward β).obj
      ((Scheme.Modules.pushforward q).obj (cartierPullback q (cartierPullback β D) + E).sheaf) :=
  s' ≪≫ (cartierIdealTwistPresentationIso D C I).symm ≪≫
    tensorIso (Iso.refl D.sheaf) s.symm ≪≫
      changedCartierTwistPushforwardIso hProj hProj' β q E e D

theorem projectiveChangedTwistedComparison_existsUnique_principalized_mono_factor
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F F' : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C D : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (s' : F' ≅ (D + C).sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    ∃! δ : (cartierPullback β (D + C) - P).sheaf ⟶
        (Scheme.Modules.pushforward q).obj (cartierPullback q (cartierPullback β D) + E).sheaf,
      projectivePresentedPrincipalizedPullbackMap hProj I β (D + C) s' P hP hIP ≫ δ =
        changedRoundupBaseChangeMap β
          (presentedChangedCartierTwistPushforwardIso hProj hProj' β q E I C D s s' e) ∧
      δ ≠ 0 ∧ Mono δ :=
  projectiveChangedRoundup_existsUnique_principalized_mono_factor hProj hProj' I hI β
    (D + C) s' P hP hIP q (cartierPullback q (cartierPullback β D) + E)
    (presentedChangedCartierTwistPushforwardIso hProj hProj' β q E I C D s s' e)

/-- The same actual principalization gives every twist's actual comparison
image, with the fixed correction β*C-P independent of D. -/
theorem projectiveChangedTwistedComparison_uniform_actual_image_iso
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F F' : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C D : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (s' : F' ≅ (D + C).sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    Nonempty ((cartierPullback β D + (cartierPullback β C - P)).sheaf ≅
      image (changedRoundupBaseChangeMap β
        (presentedChangedCartierTwistPushforwardIso hProj hProj' β q E I C D s s' e))) := by
  obtain ⟨i⟩ := projectiveChangedRoundup_principalized_actual_image_iso hProj hProj' I hI β
    (D + C) s' P hP hIP q (cartierPullback q (cartierPullback β D) + E)
    (presentedChangedCartierTwistPushforwardIso hProj hProj' β q E I C D s s' e)
  have hD : cartierPullback β D + (cartierPullback β C - P) = cartierPullback β (D + C) - P := by
    rw [cartierPullback_add]
    abel
  exact ⟨eqToIso (congrArg CartierDivisor.sheaf hD) ≪≫ i⟩

/-- The original relative-adjoint direct image is the source of the changed
comparison. Its presentation is constructed from the actual principal equation,
with the same ideal at every multiple. -/
noncomputable def relativeAdjointChangedMultiplePushforwardIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q']
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
        (cartierPullback q' (cartierPullback β (j • A)) + E').sheaf) :=
  presentedChangedCartierTwistPushforwardIso hProj hProj' β q' E' I C (j • A) s
    (relativeAdjointMultipleDirectImageIsoOfIdealPresentation hProj q A L E C χ hL I s j) e

/-- Every actual relative-adjoint multiple has the same principalization and
the fixed correction β*C-P in its actual comparison image. -/
theorem relativeAdjointChangedMultipleComparison_uniform_actual_image_iso
    [IsLocallyNoetherian B']
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (β : B' ⟶ B) [IsDominant β]
    (q' : T' ⟶ B') [IsDominant q']
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
        (relativeAdjointChangedMultiplePushforwardIso hProj hProj' q β q' A C L E E' χ hL I s e j))) := by
  intro j
  simpa only [cartierPullback_nsmul, relativeAdjointChangedMultiplePushforwardIso] using
    projectiveChangedTwistedComparison_uniform_actual_image_iso hProj hProj' I hI β C
      (j • A) s
      (relativeAdjointMultipleDirectImageIsoOfIdealPresentation hProj q A L E C χ hL I s j)
      P hP hIP q' E' e

/-- For the actual principalizing blow-up sequence, the higher base's ample
divisor is supplied by the existing model theorem. -/
noncomputable def blowUpSequenceChangedMultiplePushforwardIso
    [IsNoetherian B] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (S : Scheme.BlowUpSequence B) [IsIntegral S.last]
    [S.last.Over (Spec (CommRingCat.of K))]
    [S.composite.IsOver (Spec (CommRingCat.of K))] [IsDominant S.composite]
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (q' : T' ⟶ S.last) [IsDominant q']
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData)
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward S.composite).obj ((Scheme.Modules.pushforward q').obj E'.sheaf))
    (j : ℕ) :
    (Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
      (Scheme.Modules.pushforward S.composite).obj ((Scheme.Modules.pushforward q').obj
        (cartierPullback q' (cartierPullback S.composite (j • A)) + E').sheaf) :=
  relativeAdjointChangedMultiplePushforwardIso hProj
    (blowUpSequence_exists_ample_cartier hProj S) q S.composite q' A C L E E' χ hL I s e j

theorem blowUpSequenceChangedMultipleComparison_uniform_actual_image_iso
    [IsNoetherian B] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (S : Scheme.BlowUpSequence B) [IsIntegral S.last] [IsLocallyNoetherian S.last]
    [S.last.Over (Spec (CommRingCat.of K))]
    [S.composite.IsOver (Spec (CommRingCat.of K))] [IsDominant S.composite]
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] (q' : T' ⟶ S.last) [IsDominant q']
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor S.last) (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap S.composite)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward S.composite).obj ((Scheme.Modules.pushforward q').obj E'.sheaf)) :
    ∀ j : ℕ, Nonempty ((j • cartierPullback S.composite A +
      (cartierPullback S.composite C - P)).sheaf ≅
      image (changedRoundupBaseChangeMap S.composite
        (blowUpSequenceChangedMultiplePushforwardIso hProj S q q' A C L E E' χ hL I s e j))) :=
  relativeAdjointChangedMultipleComparison_uniform_actual_image_iso hProj
    (blowUpSequence_exists_ample_cartier hProj S) q S.composite q' A C L E E' χ hL I hI
    s P hP hIP e


end MixedFujita
