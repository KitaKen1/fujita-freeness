/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierNefDefinition
public import MixedFujita.CartierActualPullbackOrder
public import MixedFujita.CartierSectionNonvanishingOpen
public import MixedFujita.CartierSectionDivisor
public import MixedFujita.PointClosureHyperplaneEquivalence
public import MixedFujita.DominantCartierPullback
public import MixedFujita.AmpleEffectiveComparison

/-!
Nefness under pullback along a dominant morphism (steps 12 and 14).

Let ρ : T → X be a dominant morphism of integral schemes and D a Cartier divisor of X with a
nonzero global section. Every Cartier divisor of T representing the module pullback ρ*O(D) is
linearly equivalent to the pullback divisor ρ*D: the pulled back section has, at every point, the
pulled back local coefficient up to a unit. Hence O(ρ*D) ≅ ρ*O(D) and, for every curve
ψ : C → T, the degree of ρ*D along ψ is the degree of D along ψ ≫ ρ. By additivity of the degree
the same holds for differences of such divisors, so the pullback of a nef divisor which is a
difference of two divisors with nonzero sections is nef; on a scheme with an ample divisor every
Cartier divisor is such a difference.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Iso

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- For a Cartier divisor D with a nonzero global section, every Cartier divisor representing the
module pullback of O(D) along a dominant morphism is the pullback divisor plus a principal
divisor. -/
theorem cartierPullback_representation_eq_add_principal (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (E : CartierDivisor T)
    (a : (Scheme.Modules.pullback ρ).obj D.sheaf ≅ E.sheaf) :
    ∃ h : T.functionFieldˣ, E = cartierPullback ρ D + principalCartierDivisor T h := by
  have hgen : genericPoint X ∈ cartierSectionNonvanishingOpen D s :=
    (cartierSectionNonvanishingOpen_genericPoint_iff D s).mpr hs
  have hs' : cartierPullbackGlobalSectionViaIso D ρ E a s ≠ 0 := by
    rw [cartierPullbackGlobalSectionViaIso_ne_zero_iff,
      cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen]
    have : Nonempty (cartierSectionNonvanishingOpen D s) := ⟨⟨genericPoint X, hgen⟩⟩
    obtain ⟨⟨t₀, ht₀⟩⟩ := dominant_preimage_nonempty ρ (cartierSectionNonvanishingOpen D s)
    exact ⟨t₀, ht₀⟩
  have hrs : cartierSectionRational D s ≠ 0 :=
    (map_ne_zero_iff _ (cartierSectionRational_injective D)).mpr hs
  have hrs' : cartierSectionRational E (cartierPullbackGlobalSectionViaIso D ρ E a s) ≠ 0 :=
    (map_ne_zero_iff _ (cartierSectionRational_injective E)).mpr hs'
  have hφrs : (dominantFunctionFieldMap ρ).hom (cartierSectionRational D s) ≠ 0 :=
    (map_ne_zero _).mpr hrs
  refine ⟨Units.mk0 _ hφrs * (Units.mk0 _ hrs')⁻¹, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
  obtain ⟨g, hg, v, hv⟩ := cartierActualPullback_local_coefficients D ρ E a t f hf
  refine ⟨Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f *
    (Units.mk0 _ hφrs * (Units.mk0 _ hrs')⁻¹), ?_,
    (cartierPullback_isLocalEquationAt ρ D t hf).mul
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor t _)⟩
  apply isLocalEquationAt_stalkUnit_mul hg v
  have h1 := congrArg (algebraMap (T.presheaf.stalk t) T.functionField) (hv s)
  rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap,
    cartierLocalCoefficient_image, map_mul, map_mul, cartierLocalCoefficient_image] at h1
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  change (dominantFunctionFieldMap ρ).hom (f : X.functionField) *
      ((dominantFunctionFieldMap ρ).hom (cartierSectionRational D s) *
        (cartierSectionRational E (cartierPullbackGlobalSectionViaIso D ρ E a s))⁻¹) = _
  field_simp
  linear_combination h1

/-- For a Cartier divisor D with a nonzero global section and a dominant morphism ρ, the sheaf of
the pullback divisor is the module pullback of the sheaf of D. -/
theorem cartierPullback_sheaf_iso_modulePullback (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤))
    (hs : s ≠ 0) :
    Nonempty ((Scheme.Modules.pullback ρ).obj D.sheaf ≅ (cartierPullback ρ D).sheaf) := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D ρ
  obtain ⟨h, hE⟩ := cartierPullback_representation_eq_add_principal ρ D s hs E a
  subst hE
  exact ⟨a ≪≫ cartierSheafPrincipalShiftIso (cartierPullback ρ D) h⟩

end Iso

section Degree

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- The degree along a curve ψ of the pullback ρ*D of a divisor with a nonzero section is the
degree of D along ψ ≫ ρ. -/
theorem cartierCurvePullbackDegree_cartierPullback {C : Scheme.{u}} [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (ρ : T ⟶ X) [IsDominant ρ] (ψ : C ⟶ T) (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤))
    (hs : s ≠ 0) :
    cartierCurvePullbackDegree (K := K) (cartierPullback ρ D) ψ =
      cartierCurvePullbackDegree (K := K) D (ψ ≫ ρ) := by
  obtain ⟨e⟩ := cartierPullback_sheaf_iso_modulePullback ρ D s hs
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D (ψ ≫ ρ)
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hC D (ψ ≫ ρ) A a,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hC (cartierPullback ρ D) ψ A
      ((Scheme.Modules.pullback ψ).mapIso e.symm ≪≫
        (Scheme.Modules.pullbackComp ψ ρ).app D.sheaf ≪≫ a)]

variable [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

/-- The pullback along a dominant morphism over the base field of a nef divisor which is a
difference of two divisors with nonzero global sections is nef. -/
theorem cartierIsNef_cartierPullback_of_sub (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] (G₁ G₂ : CartierDivisor X)
    (s₁ : Γ(G₁.sheaf, ⊤)) (hs₁ : s₁ ≠ 0) (s₂ : Γ(G₂.sheaf, ⊤)) (hs₂ : s₂ ≠ 0)
    (hN : CartierIsNef K (G₁ - G₂)) : CartierIsNef K (cartierPullback ρ (G₁ - G₂)) := by
  intro C _ _ _ _ hC ψ hψ
  have h1 := cartierCurvePullbackDegree_cartierPullback (K := K) hC ρ ψ G₁ s₁ hs₁
  have h2 := cartierCurvePullbackDegree_cartierPullback (K := K) hC ρ ψ G₂ s₂ hs₂
  have hsubT : cartierCurvePullbackDegree (K := K)
      (cartierPullback ρ G₁ - cartierPullback ρ G₂) ψ =
      cartierCurvePullbackDegree (K := K) (cartierPullback ρ G₁) ψ -
        cartierCurvePullbackDegree (K := K) (cartierPullback ρ G₂) ψ :=
    map_sub (cartierCurvePullbackDegreeHom (K := K) hC ψ) _ _
  have hsubX : cartierCurvePullbackDegree (K := K) (G₁ - G₂) (ψ ≫ ρ) =
      cartierCurvePullbackDegree (K := K) G₁ (ψ ≫ ρ) -
        cartierCurvePullbackDegree (K := K) G₂ (ψ ≫ ρ) :=
    map_sub (cartierCurvePullbackDegreeHom (K := K) hC (ψ ≫ ρ)) _ _
  have hover : (ψ ≫ ρ) ≫ (X ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) := by
    rw [Category.assoc, HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)), hψ]
  rw [cartierPullback_sub, hsubT, h1, h2, ← hsubX]
  exact hN C hC (ψ ≫ ρ) hover

/-- On a scheme with an ample divisor, the pullback of a nef divisor along a dominant morphism
over the base field is nef. -/
theorem cartierIsNef_cartierPullback_of_ample {H N : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) (hN : CartierIsNef K N) (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] : CartierIsNef K (cartierPullback ρ N) := by
  obtain ⟨j₁, h₁⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH N
  obtain ⟨j₂, h₂⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (0 : CartierDivisor X)
  obtain ⟨s₁, hs₁⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (h₁ (max j₁ j₂) (le_max_left _ _))
  obtain ⟨s₂, hs₂⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (h₂ (max j₁ j₂) (le_max_right _ _))
  have hdec : N = (N + max j₁ j₂ • H) - (0 + max j₁ j₂ • H) := by abel
  have hN' : CartierIsNef K ((N + max j₁ j₂ • H) - (0 + max j₁ j₂ • H)) := by
    rw [← hdec]
    exact hN
  rw [hdec]
  exact cartierIsNef_cartierPullback_of_sub ρ _ _ s₁ hs₁ s₂ hs₂ hN'

end Degree

end MixedFujita
