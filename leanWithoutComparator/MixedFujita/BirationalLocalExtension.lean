/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantKltCommonModel
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
The valuative criterion lifts the actual trait of a prime on a test model to a
proper birational model. Spreading out extends that trait map to an actual open
neighbourhood. No common smooth resolution is assumed or constructed here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T U : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral U]

/-- The generic trait maps commute with the actual dominant function-field map. -/
theorem dominantFunctionFieldMap_fromSpecStalk (ρ : T ⟶ X) [IsDominant ρ] :
    Spec.map (dominantFunctionFieldMap ρ) ≫ X.fromSpecStalk (genericPoint X) =
      T.fromSpecStalk (genericPoint T) ≫ ρ := by
  unfold dominantFunctionFieldMap
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The actual inclusion of a local ring in the function field defines its generic trait. -/
theorem algebraMap_fromSpecStalk (x : U) :
    Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk x) U.functionField)) ≫
      U.fromSpecStalk x = U.fromSpecStalk (genericPoint U) := by
  exact U.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec U).specializes trivial)

/-- The actual map from the generic stalk of an integral scheme is dominant. -/
theorem fromSpecStalk_genericPoint_isDominant :
    IsDominant (T.fromSpecStalk (genericPoint T)) := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  have h : ({genericPoint T} : Set T) ⊆ Set.range (T.fromSpecStalk (genericPoint T)) := by
    rintro y rfl
    exact ⟨IsLocalRing.closedPoint (T.presheaf.stalk (genericPoint T)),
      T.fromSpecStalk_closedPoint⟩
  simpa only [(genericPoint_spec T).def] using closure_mono h

/-- Every dominant open immersion induces an isomorphism on the actual function fields. -/
theorem dominantFunctionFieldMap_bijective_of_isOpenImmersion
    (ι : T ⟶ X) [IsOpenImmersion ι] [IsDominant ι] :
    Function.Bijective (dominantFunctionFieldMap ι).hom := by
  let e := X.presheaf.stalkCongr (Inseparable.of_eq (dominant_map_genericPoint ι).symm)
  have : IsIso (dominantFunctionFieldMap ι) := by
    change IsIso (e.hom ≫ ι.stalkMap (genericPoint T))
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (dominantFunctionFieldMap ι)

variable (ρ : T ⟶ X) (σ : U ⟶ X) [IsDominant ρ] [IsDominant σ]
  (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)

/-- Properness lifts each actual valuation stalk of the test model to the birational model. -/
theorem proper_birational_exists_trait_lift [IsProper ρ] (x : U)
    [ValuationRing (U.presheaf.stalk x)] :
    ∃ l : Spec (U.presheaf.stalk x) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk x) U.functionField)) ≫ l =
        Spec.map (CommRingCat.ofHom ((dominantFunctionFieldMap σ).hom.comp
          (RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm.toRingHom)) ≫
            T.fromSpecStalk (genericPoint T) ∧
      l ≫ ρ = U.fromSpecStalk x ≫ σ := by
  let θ : T.functionField →+* U.functionField := (dominantFunctionFieldMap σ).hom.comp
    (RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm.toRingHom
  have hθ : dominantFunctionFieldMap ρ ≫ CommRingCat.ofHom θ =
      dominantFunctionFieldMap σ := by
    ext a
    exact congrArg (dominantFunctionFieldMap σ).hom
      ((RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm_apply_apply a)
  let S : ValuativeCommSq ρ :=
    { R := U.presheaf.stalk x
      K := U.functionField
      i₁ := Spec.map (CommRingCat.ofHom θ) ≫ T.fromSpecStalk (genericPoint T)
      i₂ := U.fromSpecStalk x ≫ σ
      commSq := ⟨by
        rw [Category.assoc, ← dominantFunctionFieldMap_fromSpecStalk ρ,
          ← Spec.map_comp_assoc, hθ, dominantFunctionFieldMap_fromSpecStalk σ,
          ← algebraMap_fromSpecStalk x, Category.assoc]⟩ }
  have hp : IsProper ρ := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  obtain ⟨l, hl₁, hl₂⟩ := ((ValuativeCriterion.existence hp.1.1.1) S).exists_lift
  exact ⟨l, hl₁, hl₂⟩

include hρ in
/-- A proper birational model is reached over the source from an open neighbourhood of each
actual valuation point of a test model. The commuting map is constructed, not supplied. -/
theorem proper_birational_exists_local_extension [IsProper ρ] (x : U)
    [ValuationRing (U.presheaf.stalk x)] :
    ∃ (W : U.Opens) (hx : x ∈ W) (α : W.toScheme ⟶ T),
      α ≫ ρ = W.ι ≫ σ := by
  obtain ⟨l, _, hl⟩ := proper_birational_exists_trait_lift ρ σ hρ x
  obtain ⟨W, hx, α, _, hα⟩ := spread_out_of_isGermInjective' σ ρ l hl
  exact ⟨W, hx, α, hα⟩

include hρ in
/-- A trait lift spreads to a dominant map inducing a bijective actual function-field map.
Both birationality and the commuting square are proved from the actual maps. -/
theorem proper_birational_exists_local_birational_extension [IsProper ρ]
    (hσ : Function.Bijective (dominantFunctionFieldMap σ).hom) (x : U)
    [ValuationRing (U.presheaf.stalk x)] :
    ∃ (W : U.Opens) (_hx : x ∈ W) (_ : IsIntegral W.toScheme)
      (α : W.toScheme ⟶ T) (_ : IsDominant α),
      α ≫ ρ = W.ι ≫ σ ∧ Function.Bijective (dominantFunctionFieldMap α).hom := by
  obtain ⟨l, hl₁, hl₂⟩ := proper_birational_exists_trait_lift ρ σ hρ x
  obtain ⟨W, hx, α, hlα, hα⟩ := spread_out_of_isGermInjective' σ ρ l hl₂
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  letI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let eρ := RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ
  let eσ := RingEquiv.ofBijective (dominantFunctionFieldMap σ).hom hσ
  let e := eρ.symm.trans eσ
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (e.toCommRingCatIso).isIso_hom
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
  have : IsDominant (T.fromSpecStalk (genericPoint T)) := fromSpecStalk_genericPoint_isDominant
  have htop : IsDominant
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ T.fromSpecStalk (genericPoint T)) := inferInstance
  have : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap (U.presheaf.stalk x) U.functionField)) ≫ l) := by
    rw [hl₁]
    exact htop
  have : IsDominant l := IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk x) U.functionField))) l
  have : IsDominant (W.fromSpecStalkOfMem x hx ≫ α) := by rwa [← hlα]
  have : IsDominant α := IsDominant.of_comp (W.fromSpecStalkOfMem x hx) α
  have : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hι := dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  have hcomp : dominantFunctionFieldMap ρ ≫ dominantFunctionFieldMap α =
      dominantFunctionFieldMap σ ≫ dominantFunctionFieldMap W.ι := by
    rw [← dominantFunctionFieldMap_comp, ← dominantFunctionFieldMap_comp]
    simpa only [hα]
  have hsurj : Function.Surjective (dominantFunctionFieldMap α).hom := by
    have hs : Function.Surjective (dominantFunctionFieldMap ρ ≫ dominantFunctionFieldMap α).hom := by
      rw [hcomp]
      exact hι.2.comp hσ.2
    exact Function.Surjective.of_comp hs
  exact ⟨W, hx, inferInstance, α, inferInstance, hα,
    ⟨(dominantFunctionFieldMap α).hom.injective, hsurj⟩⟩

end MixedFujita
