/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalLocalExtension
public import MixedFujita.LemmaThreeFromRestriction
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
Lifting a prime of a test model of a fibre to a proper birational model of the total space
(step 9, generic restriction).

A birational morphism of integral schemes, locally of finite type, has a section over an open
neighbourhood of the generic point of the target (`exists_section_of_birational`: spread out the
inverse at the generic point). If the morphism is moreover proper, a morphism τ : U → X from an
integral scheme whose generic point lands in the domain of the section lifts near every valuation
point x of U (`exists_local_lift_of_section`): the section gives the generic trait, the valuative
criterion of properness the trait at x, and spreading out a neighbourhood of x. The morphism τ need
not be dominant; it will be a test model of a fibre mapped into the total space.

For the fibres of a product A ⊗ B over the K-points w of B, a nonzero element stays nonzero on the
fibres over the w outside the zero set of one nonzero coefficient (`exists_ne_zero_fibreAt`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Lift

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- A birational morphism of integral schemes, locally of finite type, has a section over an open
neighbourhood of the generic point of the target. -/
theorem exists_section_of_birational (ρ : T ⟶ X) [IsDominant ρ] [LocallyOfFiniteType ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom) :
    ∃ (X₀ : X.Opens) (_ : genericPoint X ∈ X₀) (s : X₀.toScheme ⟶ T), s ≫ ρ = X₀.ι := by
  let e := RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ
  let l : Spec (X.presheaf.stalk (genericPoint X)) ⟶ T :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ T.fromSpecStalk (genericPoint T)
  have hid : dominantFunctionFieldMap ρ ≫ CommRingCat.ofHom e.symm.toRingHom =
      𝟙 X.functionField := by
    ext a
    exact e.symm_apply_apply a
  have hl : l ≫ ρ = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    rw [Category.comp_id, Category.assoc, ← dominantFunctionFieldMap_fromSpecStalk ρ,
      ← Category.assoc, ← Spec.map_comp, hid, Spec.map_id, Category.id_comp]
  obtain ⟨X₀, hη, s, -, hs⟩ := spread_out_of_isGermInjective' (𝟙 X) ρ l hl
  exact ⟨X₀, hη, s, by rw [hs, Category.comp_id]⟩

omit [IsIntegral X] [IsIntegral T] in
/-- A proper morphism with a section near the generic point lifts, near every valuation point, a
morphism from an integral scheme whose generic point lands in the domain of the section. -/
theorem exists_local_lift_of_section (ρ : T ⟶ X) [IsProper ρ] (X₀ : X.Opens)
    (s : X₀.toScheme ⟶ T) (hs : s ≫ ρ = X₀.ι) {U : Scheme.{u}} [IsIntegral U] (τ : U ⟶ X)
    (hτ : τ (genericPoint U) ∈ X₀) (x : U) [ValuationRing (U.presheaf.stalk x)] :
    ∃ (W : U.Opens) (_ : x ∈ W) (α : W.toScheme ⟶ T), α ≫ ρ = W.ι ≫ τ := by
  have hrange : Set.range (U.fromSpecStalk (genericPoint U) ≫ τ) ⊆ Set.range X₀.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : U.fromSpecStalk (genericPoint U) y = genericPoint U := by
      have h1 : U.fromSpecStalk (genericPoint U) y ⤳ genericPoint U :=
        (Scheme.range_fromSpecStalk (x := genericPoint U)).le ⟨y, rfl⟩
      exact (h1.antisymm ((genericPoint_spec U).specializes (Set.mem_univ _))).eq
    rw [Scheme.Hom.comp_apply, hy]
    exact hτ
  let i₁ : Spec U.functionField ⟶ T :=
    IsOpenImmersion.lift X₀.ι (U.fromSpecStalk (genericPoint U) ≫ τ) hrange ≫ s
  have hi₁ : i₁ ≫ ρ = U.fromSpecStalk (genericPoint U) ≫ τ := by
    simp only [i₁, Category.assoc, hs, IsOpenImmersion.lift_fac]
  let S : ValuativeCommSq ρ :=
    { R := U.presheaf.stalk x
      K := U.functionField
      i₁ := i₁
      i₂ := U.fromSpecStalk x ≫ τ
      commSq := ⟨by rw [hi₁, ← algebraMap_fromSpecStalk x, Category.assoc]⟩ }
  have hp : IsProper ρ := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  obtain ⟨l, -, hl₂⟩ := ((ValuativeCriterion.existence hp.1.1.1) S).exists_lift
  obtain ⟨W, hx, α, -, hα⟩ := spread_out_of_isGermInjective' τ ρ l hl₂
  exact ⟨W, hx, α, hα⟩

end Lift

section Fibre

variable {K : Type u} [Field K] {A B : Type u} [CommRing A] [CommRing B] [Algebra K A]
  [Algebra K B]

/-- A nonzero element of A ⊗ B is nonzero on the fibres over the K-points of B outside the zero set
of one nonzero element of B. -/
theorem exists_ne_zero_fibreAt {F : A ⊗[K] B} (hF : F ≠ 0) :
    ∃ b₀ : B, b₀ ≠ 0 ∧ ∀ w : B →ₐ[K] K, w b₀ ≠ 0 → fibreAt w F ≠ 0 := by
  classical
  let e := Module.Free.chooseBasis K A
  let Φ := TensorProduct.equivFinsuppOfBasisLeft (R := K) (N := B) e
  have hΦ : Φ F ≠ 0 := fun h => hF (Φ.injective (h.trans (map_zero Φ).symm))
  obtain ⟨i₀, hi₀⟩ : ∃ i, Φ F i ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ (Finsupp.ext h)
  have key : ∀ (w : B →ₐ[K] K) (G : A ⊗[K] B), e.repr (fibreAt w G) i₀ = w (Φ G i₀) := by
    intro w G
    induction G with
    | tmul a b =>
      rw [fibreAt_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul,
        smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  refine ⟨Φ F i₀, hi₀, fun w hw h0 => hw ?_⟩
  rw [← key, h0, map_zero, Finsupp.zero_apply]

end Fibre

end MixedFujita
