/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltNonproperBirationalTests

/-!
An actual birational test whose centre belongs to an open immersion's range
factors through that immersion on an actual open neighbourhood of the centre.
The factor is dominant and birational on the actual function fields.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X Z U : Scheme.{u}}
  [IsIntegral X] [IsIntegral Z] [IsIntegral U]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))]

/-- The open factor, its centre neighbourhood, and its field bijection are constructed. -/
theorem birational_test_exists_open_immersion_lift
    (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (u : U) (hu : σ u ∈ j.opensRange) :
    ∃ (W : U.Opens) (huW : u ∈ W),
      letI : Nonempty W := ⟨⟨u, huW⟩⟩
      letI : W.toScheme.Over (Spec (CommRingCat.of K)) :=
        ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
      ∃ (α : W.toScheme ⟶ Z) (_ : IsDominant α) (_ : α.IsOver (Spec (CommRingCat.of K))),
        α ≫ j = W.ι ≫ σ ∧
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) α) := by
  let W := σ ⁻¹ᵁ j.opensRange
  have huW : u ∈ W := hu
  letI : Nonempty W := ⟨⟨u, huW⟩⟩
  letI : W.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  haveI : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let α : W.toScheme ⟶ Z := IsOpenImmersion.lift j (W.ι ≫ σ) (by
    intro x hx
    obtain ⟨w, rfl⟩ := hx
    exact w.property)
  have hcomm : α ≫ j = W.ι ≫ σ := IsOpenImmersion.lift_fac _ _ _
  have hgen : α (genericPoint W.toScheme) = genericPoint Z := by
    apply j.isOpenEmbedding.injective
    have heq := congrArg (fun m : W.toScheme ⟶ X => m (genericPoint W.toScheme)) hcomm
    simp only [Scheme.Hom.comp_apply] at heq
    rw [dominant_map_genericPoint W.ι, dominant_map_genericPoint σ] at heq
    exact heq.trans (dominant_map_genericPoint j).symm
  letI : IsDominant α := by
    constructor
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    have hs : ({genericPoint Z} : Set Z) ⊆ Set.range α := by
      exact Set.singleton_subset_iff.mpr ⟨genericPoint W.toScheme, hgen⟩
    simpa only [(genericPoint_spec Z).def] using closure_mono hs
  haveI : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := j) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι := dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  have hcomp : dominantFunctionFieldMap j ≫ dominantFunctionFieldMap α =
      dominantFunctionFieldMap σ ≫ dominantFunctionFieldMap W.ι := by
    rw [← dominantFunctionFieldMap_comp, ← dominantFunctionFieldMap_comp]
    simpa only [hcomm]
  have hsurj : Function.Surjective (dominantFunctionFieldMap α).hom := by
    have hs : Function.Surjective (dominantFunctionFieldMap j ≫ dominantFunctionFieldMap α).hom := by
      rw [hcomp]
      exact hι.2.comp hσ.2
    exact Function.Surjective.of_comp hs
  exact ⟨W, huW, α, inferInstance, inferInstance, hcomm,
    (dominantFunctionFieldMap α).hom.injective, hsurj⟩

end MixedFujita
