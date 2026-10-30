/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GlobalIdealComapCartierFactorization
public import MixedFujita.EffectiveCartierPullbackUntwist

/-! The actual Cartier-twisted ideal pullback maps epimorphically to
O(β*C-P). Untwisting by the Cartier equivalence and the actual projection
formula gives a unique factor of every comparison into a dominant Cartier
direct image. The factor is nonzero when the comparison is nonzero. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']

noncomputable def cartierTwistedIdealPullbackSourceIso
    (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (hC : C.IsEffective) :
    (Scheme.Modules.pullback β).obj (C.sheaf ⊗ idealSheafDataModule I) ≅
      (cartierPullback β C).sheaf ⊗ (Scheme.Modules.pullback β).obj (idealSheafDataModule I) :=
  cartierPullbackTensorIso C β (idealSheafDataModule I) ≪≫
    tensorIso (effectiveCartierPullbackModuleIso β C hC) (Iso.refl _)

noncomputable def principalizedCartierTwistedPullbackMap
    (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (hC : C.IsEffective)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    (Scheme.Modules.pullback β).obj (C.sheaf ⊗ idealSheafDataModule I) ⟶
      (cartierPullback β C - P).sheaf :=
  (cartierTwistedIdealPullbackSourceIso I β C hC).hom ≫
    (cartierTwistFunctor (cartierPullback β C)).map (principalizedIdealPullbackMap I β P hP hIP) ≫
      (cartierCutTensorSourceIso (cartierPullback β C) P).hom

theorem principalizedCartierTwistedPullbackMap_epi
    (I : B.IdealSheafData) (β : B' ⟶ B) [IsDominant β]
    (C : CartierDivisor B) (hC : C.IsEffective)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    Epi (principalizedCartierTwistedPullbackMap I β C hC P hP hIP) := by
  letI := principalizedIdealPullbackMap_epi I β P hP hIP
  unfold principalizedCartierTwistedPullbackMap
  infer_instance

theorem principalizedCartierTwistedPullbackMap_existsUnique_factor_to_cartier_direct_image
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj (C.sheaf ⊗ idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      principalizedCartierTwistedPullbackMap I β C hC P hP hIP ≫ δ = ψ := by
  let D := cartierPullback β C
  let A := (Scheme.Modules.pullback β).obj (idealSheafDataModule I)
  let N := (Scheme.Modules.pushforward q).obj E.sheaf
  let e := cartierTwistedIdealPullbackSourceIso I β C hC
  let c := cartierCutTensorSourceIso D P
  let Φ := cartierTwistEquivalence D
  let adj := Φ.toAdjunction
  let u := effectiveCartierDirectImageUntwistIso q D (cartierPullback_isEffective β C hC) E
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
  have hfac : principalizedCartierTwistedPullbackMap I β C hC P hP hIP ≫ (c.inv ≫ δt) = ψ := by
    change (e.hom ≫ Φ.functor.map (principalizedIdealPullbackMap I β P hP hIP) ≫ c.hom) ≫
      (c.inv ≫ δt) = ψ
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hmid, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  letI := principalizedCartierTwistedPullbackMap_epi I β C hC P hP hIP
  exact ⟨c.inv ≫ δt, hfac, fun δ' hδ' ↦
    (cancel_epi (principalizedCartierTwistedPullbackMap I β C hC P hP hIP)).mp (hδ'.trans hfac.symm)⟩

theorem principalizedCartierTwistedPullbackMap_existsUnique_nonzero_factor_to_cartier_direct_image
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (β : B' ⟶ B) [IsDominant β] (C : CartierDivisor B) (hC : C.IsEffective)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ B') [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback β).obj (C.sheaf ⊗ idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) (hψ : ψ ≠ 0) :
    ∃! δ : (cartierPullback β C - P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      principalizedCartierTwistedPullbackMap I β C hC P hP hIP ≫ δ = ψ ∧ δ ≠ 0 := by
  obtain ⟨δ, hδ, huniq⟩ :=
    principalizedCartierTwistedPullbackMap_existsUnique_factor_to_cartier_direct_image
      I hI β C hC P hP hIP q E ψ
  refine ⟨δ, ⟨hδ, ?_⟩, fun δ' hδ' ↦ huniq δ' hδ'.1⟩
  intro hz
  apply hψ
  simpa only [hz, comp_zero] using hδ.symm

end MixedFujita
