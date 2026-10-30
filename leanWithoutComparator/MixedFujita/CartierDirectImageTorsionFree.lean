/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierPushforwardUnit
public import MixedFujita.SpecIdealPullbackFactorization
public import SGA.Foundations.Cohomology.Helpers

/-! Cartier direct images under dominant morphisms of integral schemes
have torsion-free section modules. This supplies the target condition of
the nonflat extended-ideal factorization from actual geometry. No effective,
proper, normal or quasi-coherent hypothesis is required. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]

theorem cartier_direct_image_sections_noZeroSMulDivisors
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (U : B.Opens) :
    NoZeroSMulDivisors Γ(B, U) Γ((Scheme.Modules.pushforward q).obj E.sheaf, U) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
    haveI : Subsingleton Γ((Scheme.Modules.pushforward q).obj E.sheaf, U) :=
      abelianSheaf_empty_sections_subsingleton
        ((SheafOfModules.toSheaf B.ringCatSheaf).obj
          ((Scheme.Modules.pushforward q).obj E.sheaf)) hbot
    exact ⟨fun _ ↦ Or.inr (Subsingleton.elim _ _)⟩
  · letI := dominant_preimage_nonempty q U
    let V := q ⁻¹ᵁ U
    let e := rationalFunctionsEquiv (X := T) V
    refine ⟨fun {a s} h ↦ ?_⟩
    have hi := congrArg (Scheme.Modules.Hom.app E.sheafι V) h
    rw [map_zero] at hi
    change Scheme.Modules.Hom.app E.sheafι V
      ((q.app U).hom a • @id Γ(E.sheaf, V) s) = 0 at hi
    rw [Scheme.Modules.Hom.app_smul] at hi
    have hf := congrArg e hi
    rw [map_smul, map_zero, Algebra.smul_def] at hf
    rcases mul_eq_zero.mp hf with ha | hs
    · left
      change T.germToFunctionField V ((q.app U).hom a) = 0 at ha
      apply B.germToFunctionField_injective U
      apply (dominantFunctionFieldMap q).hom.injective
      rw [dominantFunctionFieldMap_germ q U V le_rfl]
      simpa only [V, Scheme.Hom.appLE_eq_app, map_zero] using ha
    · right
      apply E.sheafι_app_injective V
      apply e.injective
      simpa only [id_eq, map_zero] using hs

theorem cartier_direct_image_spec_sections_noZeroSMulDivisors
    {R : CommRingCat.{u}} [IsIntegral (Spec R)] (q : T ⟶ Spec R) [IsDominant q]
    (E : CartierDivisor T) :
    NoZeroSMulDivisors R
      ((moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) := by
  letI := cartier_direct_image_sections_noZeroSMulDivisors q E ⊤
  refine ⟨fun {a s} h ↦ ?_⟩
  let s' : Γ((Scheme.Modules.pushforward q).obj E.sheaf, ⊤) := s
  have h' : ((Scheme.ΓSpecIso R).inv a) • s' = 0 := by
    change a • s' = 0 at h
    rw [Scheme.Modules.smul_Spec_def] at h
    have hi : (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
    have hm : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ :=
      (congrArg (Spec R).presheaf.map hi).trans ((Spec R).presheaf.map_id _)
    rw [hm] at h
    exact h
  rcases eq_zero_or_eq_zero_of_smul_eq_zero h' with ha | hs
  · left
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1
      (by simpa only [map_zero] using ha)
  · exact Or.inr hs

/-- For an actual Cartier direct image the torsion-free target condition
in the Spec ideal-factorization theorem is supplied internally. -/
theorem specIdealPullbackImageMap_existsUnique_factor_to_cartier_direct_image
    {R S : CommRingCat.{u}} [IsIntegral (Spec S)]
    (φ : R ⟶ S) (I : Ideal R) (hI : I ≠ ⊥) (hφ : Function.Injective φ.hom)
    (q : T ⟶ Spec S) [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde (ModuleCat.of R I)) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : tilde (ModuleCat.of S (I.map φ.hom)) ⟶
        (Scheme.Modules.pushforward q).obj E.sheaf,
      specIdealPullbackImageMap φ I ≫ δ = ψ := by
  letI := cartier_direct_image_spec_sections_noZeroSMulDivisors q E
  exact specIdealPullbackImageMap_existsUnique_factor φ I hI hφ _ ψ

end MixedFujita
