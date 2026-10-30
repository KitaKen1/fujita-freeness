/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualRelativeAdjointChangedComparison

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B B' : Scheme.{u}} (β : B' ⟶ B) {F : B.Modules} {F' M : B'.Modules}

theorem changedRoundupFactor_unit
    (e : F ≅ (Scheme.Modules.pushforward β).obj F')
    (χ : (Scheme.Modules.pullback β).obj F ⟶ M) (δ : M ⟶ F')
    (hfac : χ ≫ δ = changedRoundupBaseChangeMap β e) :
    ((Scheme.Modules.pullbackPushforwardAdjunction β).unit.app F ≫
      (Scheme.Modules.pushforward β).map χ) ≫ (Scheme.Modules.pushforward β).map δ = e.hom := by
  rw [Category.assoc, ← Functor.map_comp, hfac, changedRoundupBaseChangeMap_unit]

/-- A monic factor of the actual adjoint comparison becomes an isomorphism
after pushforward. This only uses the actual pushback isomorphism and adjunction. -/
theorem changedRoundupFactor_pushforward_isIso
    (e : F ≅ (Scheme.Modules.pushforward β).obj F')
    (χ : (Scheme.Modules.pullback β).obj F ⟶ M) (δ : M ⟶ F') [Mono δ]
    (hfac : χ ≫ δ = changedRoundupBaseChangeMap β e) :
    IsIso ((Scheme.Modules.pushforward β).map δ) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction β).unit.app F ≫
    (Scheme.Modules.pushforward β).map χ
  have hu : u ≫ (Scheme.Modules.pushforward β).map δ = e.hom :=
    changedRoundupFactor_unit β e χ δ hfac
  letI : IsSplitEpi ((Scheme.Modules.pushforward β).map δ) := IsSplitEpi.mk'
    { section_ := e.inv ≫ u
      id := by rw [Category.assoc, hu, e.inv_hom_id] }
  exact isIso_of_mono_of_isSplitEpi _

noncomputable def changedRoundupFactorPushforwardIso
    (e : F ≅ (Scheme.Modules.pushforward β).obj F')
    (χ : (Scheme.Modules.pullback β).obj F ⟶ M) (δ : M ⟶ F') [Mono δ]
    (hfac : χ ≫ δ = changedRoundupBaseChangeMap β e) :
    F ≅ (Scheme.Modules.pushforward β).obj M := by
  letI := changedRoundupFactor_pushforward_isIso β e χ δ hfac
  exact e ≪≫ (asIso ((Scheme.Modules.pushforward β).map δ)).symm

theorem changedRoundupFactorPushforwardIso_hom
    (e : F ≅ (Scheme.Modules.pushforward β).obj F')
    (χ : (Scheme.Modules.pullback β).obj F ⟶ M) (δ : M ⟶ F') [Mono δ]
    (hfac : χ ≫ δ = changedRoundupBaseChangeMap β e) :
    (changedRoundupFactorPushforwardIso β e χ δ hfac).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction β).unit.app F ≫
        (Scheme.Modules.pushforward β).map χ := by
  letI := changedRoundupFactor_pushforward_isIso β e χ δ hfac
  apply (cancel_mono ((Scheme.Modules.pushforward β).map δ)).mp
  change (e.hom ≫ inv ((Scheme.Modules.pushforward β).map δ)) ≫
      (Scheme.Modules.pushforward β).map δ = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (changedRoundupFactor_unit β e χ δ hfac).symm

theorem changedRoundupBaseChangeImage_pushforward_inclusion_isIso
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') :
    IsIso ((Scheme.Modules.pushforward β).map (image.ι (changedRoundupBaseChangeMap β e))) :=
  changedRoundupFactor_pushforward_isIso β e
    (factorThruImage (changedRoundupBaseChangeMap β e))
    (image.ι (changedRoundupBaseChangeMap β e)) (image.fac _)

noncomputable def changedRoundupBaseChangeImagePushforwardIso
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') :
    F ≅ (Scheme.Modules.pushforward β).obj (image (changedRoundupBaseChangeMap β e)) :=
  changedRoundupFactorPushforwardIso β e
    (factorThruImage (changedRoundupBaseChangeMap β e))
    (image.ι (changedRoundupBaseChangeMap β e)) (image.fac _)

variable {K : Type u} [Field K] [IsIntegral B] [IsIntegral B']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]

/-- The actual principalized line, rather than the whole changed direct image,
already pushes forward to the original sheaf. -/
noncomputable def projectivePrincipalizedComparisonPushforwardIso
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    F ≅ (Scheme.Modules.pushforward β).obj (cartierPullback β C - P).sheaf := by
  let i := Classical.choice (projectiveChangedRoundup_principalized_actual_image_iso
    hProj hProj' I hI β C s P hP hIP q E e)
  exact changedRoundupBaseChangeImagePushforwardIso β e ≪≫
    (Scheme.Modules.pushforward β).mapIso i.symm

theorem actualRelativeAdjointMultiple_principalized_pushforward_iso
    [IsLocallyNoetherian B']
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T T' : Scheme.{u}} [IsIntegral T] [IsIntegral T']
    (q : T ⟶ B) [IsDominant q] [IsDominant β]
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
    ∀ j : ℕ, Nonempty ((Scheme.Modules.pushforward q).obj (j • L + E).sheaf ≅
      (Scheme.Modules.pushforward β).obj
        (j • cartierPullback β A + (cartierPullback β C - P)).sheaf) := by
  intro j
  let ej := actualRelativeAdjointChangedMultiplePushforwardIso hProj hProj' q β q' τ hsquare
    A C L E E' χ hL I s e j
  obtain ⟨i⟩ := actualRelativeAdjointChangedMultipleComparison_uniform_actual_image_iso
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e j
  exact ⟨changedRoundupBaseChangeImagePushforwardIso β ej ≪≫
    (Scheme.Modules.pushforward β).mapIso i.symm⟩

end MixedFujita
