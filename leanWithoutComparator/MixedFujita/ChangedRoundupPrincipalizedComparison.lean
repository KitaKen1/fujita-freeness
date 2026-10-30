/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedPrincipalizedIdealFactorization
public import MixedFujita.ChangedRoundupBaseChangeMap

/-! Apply the Cartier-twisted principalized ideal factorization to the actual
rounded direct-image comparison. The source presentation, effective Cartier
principalization and pushforward isomorphism are the actual witnesses already
constructed on the compatible models. Nonvanishing is supplied internally by
the original effective rounded divisor. No base-change isomorphism is claimed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']

noncomputable def presentedPrincipalizedCartierPullbackMap
    {F : B.Modules} (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (hC : C.IsEffective) (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    (Scheme.Modules.pullback β).obj F ⟶ (cartierPullback β C - P).sheaf :=
  (Scheme.Modules.pullback β).map s.hom ≫
    principalizedCartierTwistedPullbackMap I β C hC P hP hIP

theorem presentedPrincipalizedCartierPullbackMap_epi
    {F : B.Modules} (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (hC : C.IsEffective) (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    Epi (presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP) := by
  letI := principalizedCartierTwistedPullbackMap_epi I β C hC P hP hIP
  unfold presentedPrincipalizedCartierPullbackMap
  infer_instance

theorem presentedPrincipalizedCartierPullbackMap_existsUnique_factor_to_cartier_direct_image
    [IsLocallyNoetherian B'] {F : B.Modules}
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj F ⟶ (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP ≫ δ = ψ := by
  let e := (Scheme.Modules.pullback β).mapIso s
  obtain ⟨δ, hδ, _⟩ :=
    principalizedCartierTwistedPullbackMap_existsUnique_factor_to_cartier_direct_image
      I hI β C hC P hP hIP q E (e.inv ≫ ψ)
  have hfac : presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP ≫ δ = ψ := by
    change (e.hom ≫ principalizedCartierTwistedPullbackMap I β C hC P hP hIP) ≫ δ = ψ
    rw [Category.assoc, hδ, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  letI := presentedPrincipalizedCartierPullbackMap_epi I β C hC s P hP hIP
  exact ⟨δ, hfac, fun δ' hδ' ↦
    (cancel_epi (presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP)).mp
      (hδ'.trans hfac.symm)⟩

theorem presentedPrincipalizedCartierPullbackMap_existsUnique_nonzero_factor_to_cartier_direct_image
    [IsLocallyNoetherian B'] {F : B.Modules}
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective)
    (s : F ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj F ⟶ (Scheme.Modules.pushforward q).obj E.sheaf)
    (hψ : ψ ≠ 0) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP ≫ δ = ψ ∧ δ ≠ 0 := by
  obtain ⟨δ, hδ, huniq⟩ :=
    presentedPrincipalizedCartierPullbackMap_existsUnique_factor_to_cartier_direct_image
      I hI β C hC s P hP hIP q E ψ
  refine ⟨δ, ⟨hδ, ?_⟩, fun δ' hδ' ↦ huniq δ' hδ'.1⟩
  intro hz
  apply hψ
  simpa only [hz, comp_zero] using hδ.symm

/-- The actual original and changed rounded direct images give a nonzero
factor from the actual principalized Cartier line bundle. -/
theorem changedRoundupBaseChangeMap_existsUnique_principalized_cartier_factor
    [IsLocallyNoetherian B'] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (g : X ⟶ B) [IsDominant g] (E₀ : CartierDivisor X) (hE₀ : E₀.IsEffective)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective)
    (s : (Scheme.Modules.pushforward g).obj E₀.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (q : T ⟶ B') [IsDominant q] (E₁ : CartierDivisor T)
    (e : (Scheme.Modules.pushforward g).obj E₀.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q).obj E₁.sheaf)) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E₁.sheaf,
      presentedPrincipalizedCartierPullbackMap I β C hC s P hP hIP ≫ δ =
        changedRoundupBaseChangeMap β e ∧ δ ≠ 0 :=
  presentedPrincipalizedCartierPullbackMap_existsUnique_nonzero_factor_to_cartier_direct_image
    I hI β C hC s P hP hIP q E₁ (changedRoundupBaseChangeMap β e)
      (changedRoundupBaseChangeMap_ne_zero_of_effective β g E₀ hE₀ e)

end MixedFujita
