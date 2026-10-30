/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeLifts
public import MixedFujita.BirationalLocalExtension

/-! Separated birational morphisms have at most one point over a valuation
stalk of the target. The inverse stalk maps give local sections with the
same generic restriction, so separatedness identifies them. In particular,
the retained prime over a smooth codimension-one point is unique. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (ρ : T ⟶ X) [IsDominant ρ]

attribute [local instance] cartierGlobalStalkAlgebra

/-- Inverting an actual birational stalk isomorphism gives a section of
the target trait, with the prescribed generic map and closed-point image. -/
theorem birational_exists_stalk_section
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (b : X) (t : T) (ht : ρ t = b) (hbij : Function.Bijective (ρ.stalkMap t)) :
    ∃ l : Spec (X.presheaf.stalk b) ⟶ T,
      l ≫ ρ = X.fromSpecStalk b ∧
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk b) X.functionField)) ≫ l =
        Spec.map (CommRingCat.ofHom
          (RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm.toRingHom) ≫
          T.fromSpecStalk (genericPoint T) ∧
      l (IsLocalRing.closedPoint (X.presheaf.stalk b)) = t := by
  subst b
  let e := RingEquiv.ofBijective (ρ.stalkMap t).hom hbij
  let eF := RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ
  let l := Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ T.fromSpecStalk t
  have he : ρ.stalkMap t ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    ext a
    exact e.symm_apply_apply a
  have hF : CommRingCat.ofHom e.symm.toRingHom ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk (ρ t)) X.functionField) =
      CommRingCat.ofHom (algebraMap (T.presheaf.stalk t) T.functionField) ≫
        CommRingCat.ofHom eF.symm.toRingHom := by
    ext a
    apply eF.injective
    change (dominantFunctionFieldMap ρ).hom
        (algebraMap (X.presheaf.stalk (ρ t)) X.functionField (e.symm a)) = _
    rw [dominantFunctionFieldMap_algebraMap]
    simp only [RingEquiv.toRingHom_eq_coe, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, eF.apply_symm_apply]
    exact congrArg (algebraMap (T.presheaf.stalk t) T.functionField) (e.apply_symm_apply a)
  refine ⟨l, ?_, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ T.fromSpecStalk t ≫ ρ = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, he, Spec.map_id]
    exact Category.id_comp _
  · change Spec.map (CommRingCat.ofHom (algebraMap _ X.functionField)) ≫
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ T.fromSpecStalk t = _
    rw [← Spec.map_comp_assoc, hF, Spec.map_comp, Category.assoc, algebraMap_fromSpecStalk]
  · change T.fromSpecStalk t (Spec.map (CommRingCat.ofHom e.symm.toRingHom)
        (IsLocalRing.closedPoint (X.presheaf.stalk (ρ t)))) = t
    let : IsLocalHom (CommRingCat.ofHom e.symm.toRingHom).hom :=
      IsLocalHom.of_surjective _ e.symm.surjective
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- Separatedness identifies points over the same target valuation stalk;
properness and any supplied local isomorphism are unnecessary. -/
theorem eq_of_birational_over_valuation_stalk [IsSeparated ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (b : X) [ValuationRing (X.presheaf.stalk b)]
    (t₁ t₂ : T) (h₁ : ρ t₁ = b) (h₂ : ρ t₂ = b) : t₁ = t₂ := by
  have hb (t : T) (ht : ρ t = b) : Function.Bijective (ρ.stalkMap t) := by
    let : ValuationRing (X.presheaf.stalk (ρ t)) := ht.symm ▸ inferInstance
    exact stalkMap_bijective_of_birational_valuation_stalk ρ hρ t
  obtain ⟨l₁, hl₁, hη₁, hc₁⟩ := birational_exists_stalk_section ρ hρ b t₁ h₁ (hb t₁ h₁)
  obtain ⟨l₂, hl₂, hη₂, hc₂⟩ := birational_exists_stalk_section ρ hρ b t₂ h₂ (hb t₂ h₂)
  let ι := Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk b) X.functionField))
  have : IsDominant ι := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk b) X.functionField))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp
        (IsFractionRing.injective (X.presheaf.stalk b) X.functionField)]
    exact bot_le
  have hl : l₁ = l₂ := ext_of_isDominant_of_isSeparated ρ (hl₁.trans hl₂.symm) ι
    (hη₁.trans hη₂.symm)
  exact hc₁.symm.trans ((congrArg (fun l : Spec (X.presheaf.stalk b) ⟶ T =>
    l (IsLocalRing.closedPoint (X.presheaf.stalk b))) hl).trans hc₂)

section Smooth

variable {K : Type u} [Field K] {n : ℕ} [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]

include K n in
/-- The fibre over a prime of a smooth target contains at most one point,
without assuming that the source is smooth. -/
theorem eq_of_birational_over_smooth_prime [IsSeparated ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (b : CodimensionOnePoint X) (t₁ t₂ : T)
    (h₁ : ρ t₁ = (b : X)) (h₂ : ρ t₂ = (b : X)) : t₁ = t₂ := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) b
  exact eq_of_birational_over_valuation_stalk ρ hρ (b : X) t₁ t₂ h₁ h₂

include K n in
/-- Proper birational maps have a unique prime lift over a smooth prime;
the stalk map at that unique prime is bijective. -/
theorem proper_birational_existsUnique_smooth_prime_lift [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (b : CodimensionOnePoint X) :
    ∃! t : CodimensionOnePoint T, ρ (t : T) = (b : X) ∧
      Function.Bijective (ρ.stalkMap (t : T)) := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) b
  obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant ρ (b : X)
  have hbij : Function.Bijective (ρ.stalkMap t) := by
    let : ValuationRing (X.presheaf.stalk (ρ t)) := ht.symm ▸ inferInstance
    exact stalkMap_bijective_of_birational_valuation_stalk ρ hρ t
  have hcod : Order.coheight t = 1 :=
    (coheight_eq_of_stalkMap_bijective ρ t hbij).trans (by rw [ht]; exact b.property)
  refine ⟨⟨t, hcod⟩, ⟨ht, hbij⟩, ?_⟩
  intro t' ht'
  exact Subtype.ext (eq_of_birational_over_valuation_stalk ρ hρ (b : X) t' t ht'.1 ht)

end Smooth

end MixedFujita
