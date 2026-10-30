/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NonzeroCartierDirectImageMonomorphism
public import MixedFujita.ProjectiveCartierPullbackDictionary

/-! On the existing projective bases, arbitrary Cartier twists admit the
actual pullback dictionary. Every comparison from a source presented by
O(C) ⊗ I factors through O(β*C-P). A nonzero comparison has a monic factor,
so its actual categorical image is this invertible Cartier module. The
changed-roundup adjoint is nonzero internally, without a positivity premise
on C. This does not identify the image with the whole changed direct image. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem idealSheafDataModule_not_isZero_of_ne_bot
    {B : Scheme.{u}} (I : B.IdealSheafData) (hI : I ≠ ⊥) :
    ¬ IsZero (idealSheafDataModule I) := by
  intro hzero
  apply hI
  apply Scheme.IdealSheafData.ext
  funext U
  apply SetLike.coe_injective
  rw [← idealSheafDataModuleInclusion_affine_image I U,
    hzero.eq_of_src (idealSheafDataModuleInclusion I) 0]
  ext a
  change (∃ s : Γ(idealSheafDataModule I, U.1), 0 = a) ↔ a = 0
  simp [eq_comm]

theorem cartierIdealPresentedModule_not_isZero
    {B : Scheme.{u}} [IsIntegral B] {F : B.Modules}
    (I : B.IdealSheafData) (hI : I ≠ ⊥) (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I) : ¬ IsZero F := by
  intro hF
  have htw : IsZero ((cartierTwistFunctor C).obj (idealSheafDataModule I)) :=
    IsZero.of_iso hF s.symm
  exact idealSheafDataModule_not_isZero_of_ne_bot I hI
    (IsZero.of_full_of_faithful_of_isZero (cartierTwistFunctor C) (idealSheafDataModule I) htw)

variable {K : Type u} [Field K] {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]

noncomputable def projectiveCartierDirectImageUntwistIso
    (hProj : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q]
    (D : CartierDivisor B') (E : CartierDivisor T) :
    (-D).sheaf ⊗ (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward q).obj (E - cartierPullback q D).sheaf :=
  cartierProjectionFormulaIso (-D) q E.sheaf ≪≫
    (Scheme.Modules.pushforward q).mapIso
      (tensorIso (cartierPullbackNegativeIso D q (cartierPullback q D)
          (projectiveCartierPullbackIso hProj q D)) (Iso.refl E.sheaf) ≪≫
        cartierTensorSheafIso (-(cartierPullback q D)) E ≪≫
          eqToIso (congrArg CartierDivisor.sheaf
            (show -(cartierPullback q D) + E = E - cartierPullback q D by abel)))

noncomputable def projectivePresentedPrincipalizedSourceIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (s : F ≅ C.sheaf ⊗ idealSheafDataModule I) :
    (Scheme.Modules.pullback β).obj F ≅
      (cartierPullback β C).sheaf ⊗ (Scheme.Modules.pullback β).obj (idealSheafDataModule I) :=
  (Scheme.Modules.pullback β).mapIso s ≪≫
    cartierPullbackTensorIso C β (idealSheafDataModule I) ≪≫
      tensorIso (projectiveCartierPullbackIso hProj β C) (Iso.refl _)

noncomputable def projectivePresentedPrincipalizedPullbackMap
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    (Scheme.Modules.pullback β).obj F ⟶ (cartierPullback β C - P).sheaf :=
  (projectivePresentedPrincipalizedSourceIso hProj I β C s).hom ≫
    (cartierTwistFunctor (cartierPullback β C)).map (principalizedIdealPullbackMap I β P hP hIP) ≫
      (cartierCutTensorSourceIso (cartierPullback β C) P).hom

theorem projectivePresentedPrincipalizedPullbackMap_epi
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    Epi (projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP) := by
  letI := principalizedIdealPullbackMap_epi I β P hP hIP
  unfold projectivePresentedPrincipalizedPullbackMap
  infer_instance

theorem projectivePresentedPrincipalizedPullbackMap_existsUnique_factor
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj F ⟶ (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP ≫ δ = ψ := by
  let D := cartierPullback β C
  let A := (Scheme.Modules.pullback β).obj (idealSheafDataModule I)
  let N := (Scheme.Modules.pushforward q).obj E.sheaf
  let e := projectivePresentedPrincipalizedSourceIso hProj I β C s
  let c := cartierCutTensorSourceIso D P
  let Φ := cartierTwistEquivalence D
  let adj := Φ.toAdjunction
  let u := projectiveCartierDirectImageUntwistIso hProj' q D E
  let ψu := adj.homEquiv A N (e.inv ≫ ψ) ≫ u.hom
  obtain ⟨δu, hδu, _⟩ :=
    principalizedIdealPullbackMap_existsUnique_factor_to_cartier_direct_image I hI β q
      (E - cartierPullback q D) P hP hIP ψu
  let δt := (adj.homEquiv (-P).sheaf N).symm (δu ≫ u.inv)
  have hmid : Φ.functor.map (principalizedIdealPullbackMap I β P hP hIP) ≫ δt = e.inv ≫ ψ := by
    apply (adj.homEquiv A N).injective
    rw [Adjunction.homEquiv_naturality_left]
    simp only [δt, Equiv.apply_symm_apply]
    rw [← Category.assoc, hδu]
    simp only [ψu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfac : projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP ≫
      (c.inv ≫ δt) = ψ := by
    change (e.hom ≫ Φ.functor.map (principalizedIdealPullbackMap I β P hP hIP) ≫ c.hom) ≫
      (c.inv ≫ δt) = ψ
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hmid, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  letI := projectivePresentedPrincipalizedPullbackMap_epi hProj I β C s P hP hIP
  exact ⟨c.inv ≫ δt, hfac, fun δ' hδ' ↦
    (cancel_epi (projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP)).mp
      (hδ'.trans hfac.symm)⟩

theorem projectivePresentedPrincipalizedPullbackMap_existsUnique_nonzero_mono_factor
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj F ⟶ (Scheme.Modules.pushforward q).obj E.sheaf)
    (hψ : ψ ≠ 0) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP ≫ δ = ψ ∧
        δ ≠ 0 ∧ Mono δ := by
  obtain ⟨δ, hδ, huniq⟩ := projectivePresentedPrincipalizedPullbackMap_existsUnique_factor
    hProj hProj' I hI β C s P hP hIP q E ψ
  have hn : δ ≠ 0 := by
    intro hz
    apply hψ
    simpa only [hz, comp_zero] using hδ.symm
  exact ⟨δ, ⟨hδ, hn, nonzero_cartier_to_cartier_direct_image_mono q E _ δ hn⟩,
    fun δ' hδ' ↦ huniq δ' hδ'.1⟩

/-- The source's nonzero actual image ideal supplies nonvanishing of the
changed-roundup adjoint for every Cartier twist C, including arbitrary signs. -/
theorem projectiveChangedRoundup_existsUnique_principalized_mono_factor
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP ≫ δ =
        changedRoundupBaseChangeMap β e ∧ δ ≠ 0 ∧ Mono δ :=
  projectivePresentedPrincipalizedPullbackMap_existsUnique_nonzero_mono_factor
    hProj hProj' I hI β C s P hP hIP q E (changedRoundupBaseChangeMap β e)
      (changedRoundupBaseChangeMap_ne_zero β e (cartierIdealPresentedModule_not_isZero I hI C s))

theorem projectiveChangedRoundup_principalized_actual_image_iso
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    Nonempty ((cartierPullback β C - P).sheaf ≅ image (changedRoundupBaseChangeMap β e)) := by
  obtain ⟨δ, ⟨hδ, _, hmono⟩, _⟩ := projectiveChangedRoundup_existsUnique_principalized_mono_factor
    hProj hProj' I hI β C s P hP hIP q E e
  letI := hmono
  letI := projectivePresentedPrincipalizedPullbackMap_epi hProj I β C s P hP hIP
  letI := strongEpi_of_epi (projectivePresentedPrincipalizedPullbackMap hProj I β C s P hP hIP)
  exact ⟨image.isoStrongEpiMono _ δ hδ⟩

theorem projectiveChangedRoundup_actual_comparison_image_isInvertible
    [IsLocallyNoetherian B'] (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    {F : B.Modules} (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (e : F ≅ (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible B'
      (image (changedRoundupBaseChangeMap β e)) := by
  obtain ⟨i⟩ := projectiveChangedRoundup_principalized_actual_image_iso
    hProj hProj' I hI β C s P hP hIP q E e
  exact (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible B').prop_of_iso i
    (cartierPullback β C - P).isInvertible_sheaf

end MixedFujita
