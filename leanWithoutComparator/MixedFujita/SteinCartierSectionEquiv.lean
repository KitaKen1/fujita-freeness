/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinCartierSections
public import MixedFujita.CartierGlobalGenerationOperations

/-!
The actual Cartier section pullback is a linear equivalence for an integral Stein-type map.
If the map is also surjective on points, ordinary global generation is equivalent upstairs
and downstairs: descend the actual generating section, then reflect a unit through the local
stalk map. The map need not be birational and its fibres need not be zero dimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (g : T ⟶ X) [IsDominant g]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Global generation descends through the actual surjective Stein section maps. -/
theorem cartierIsGloballyGenerated_of_stein_pullback
    (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom)
    (hsurj : Function.Surjective g) (D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated (cartierPullback g D)) : CartierIsGloballyGenerated D := by
  apply (cartierIsGloballyGenerated_iff_local_frames D).mpr
  intro x f hf
  obtain ⟨t, rfl⟩ := hsurj x
  have hft := cartierPullback_isLocalEquationAt g D t hf
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames _).mp hD t _ hft
  obtain ⟨a, rfl⟩ := cartierDominantPullbackSection_surjective_of_open_app_surjective g happ D s
  refine ⟨a, (isUnit_map_iff (g.stalkMap t).hom _).mp ?_⟩
  rwa [cartierDominantPullbackSection_localCoefficient] at hs

/-- Ordinary global generation is equivalent on the two sides of a surjective Stein-type map. -/
theorem cartierIsGloballyGenerated_stein_pullback_iff
    (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom)
    (hsurj : Function.Surjective g) (D : CartierDivisor X) :
    CartierIsGloballyGenerated (cartierPullback g D) ↔ CartierIsGloballyGenerated D :=
  ⟨cartierIsGloballyGenerated_of_stein_pullback g happ hsurj D,
    cartierIsGloballyGenerated_cartierPullback g D⟩

section BaseField

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))] [g.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra functionFieldBaseAlgebra
  cartierBaseSectionScalarTower functionFieldBaseScalarTower

/-- The existing actual section pullback, with its base-field linearity proved. -/
noncomputable def cartierDominantPullbackLinear (D : CartierDivisor X) :
    Γ(D.sheaf, ⊤) →ₗ[K] Γ((cartierPullback g D).sheaf, ⊤) where
  toFun := cartierDominantPullbackSection g D
  map_add' s t := by
    apply cartierSectionRational_injective _
    simp only [cartierDominantPullbackSection_rational, map_add]
  map_smul' a s := by
    apply cartierSectionRational_injective _
    change cartierSectionRational _ (cartierDominantPullbackSection g D (a • s)) =
      cartierSectionRational _ (a • cartierDominantPullbackSection g D s)
    have h₁ : cartierSectionRational D (a • s) = a • cartierSectionRational D s :=
      ((cartierSectionRational D).restrictScalars K).map_smul a s
    have h₂ : cartierSectionRational _ (a • cartierDominantPullbackSection g D s) =
        a • cartierSectionRational _ (cartierDominantPullbackSection g D s) :=
      ((cartierSectionRational (cartierPullback g D)).restrictScalars K).map_smul a _
    rw [cartierDominantPullbackSection_rational, h₁, h₂,
      cartierDominantPullbackSection_rational]
    exact (dominantFunctionFieldAlgHom (K := K) g).toLinearMap.map_smul a (cartierSectionRational D s)

theorem cartierDominantPullbackLinear_injective (D : CartierDivisor X) :
    Function.Injective (cartierDominantPullbackLinear g K D) := by
  intro s t h
  apply cartierSectionRational_injective D
  apply (dominantFunctionFieldMap g).hom.injective
  exact (cartierDominantPullbackSection_rational g D s).symm.trans
    ((congrArg (cartierSectionRational _) h).trans (cartierDominantPullbackSection_rational g D t))

/-- An actual linear equivalence of the full global section spaces, not just equal dimensions. -/
noncomputable def steinCartierSectionEquiv
    (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom) (D : CartierDivisor X) :
    Γ(D.sheaf, ⊤) ≃ₗ[K] Γ((cartierPullback g D).sheaf, ⊤) :=
  LinearEquiv.ofBijective (cartierDominantPullbackLinear g K D)
    ⟨cartierDominantPullbackLinear_injective g K D,
      cartierDominantPullbackSection_surjective_of_open_app_surjective g happ D⟩

theorem steinCartierSectionEquiv_rational
    (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom) (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionRational _ (steinCartierSectionEquiv g K happ D s) =
      (dominantFunctionFieldMap g).hom (cartierSectionRational D s) :=
  cartierDominantPullbackSection_rational g D s

end BaseField

end MixedFujita
