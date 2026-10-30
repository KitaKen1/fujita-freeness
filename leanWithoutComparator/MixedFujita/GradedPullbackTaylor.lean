/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorExponentObjective
public import MixedFujita.CartierGradedTaylor

/-!
Graded Taylor maps at a point of a model and the semigroup of initial exponents (step 11,
section 5.1 of the manuscript, the property (15)).

Let π : X → Y be a morphism over the base field, A a Cartier divisor of Y with a local equation f
at π(z) and Taylor coordinates at z. With the compatible local equations f^j of j A, the Taylor
expansions at z of the pullbacks of the sections of j A form a graded family of linear maps which
is multiplicative for the product of sections: T_{j+h}(s t) = T_j(s) T_h(t).

The Taylor map of j A used for the monomial Taylor tests (`cartierPullbackTaylorLinear`, with a
chosen local equation of j A) differs from T_j by a unit power series. A unit has initial exponent
zero for every monomial order, so the two maps have the same set of initial exponents; this set
does not depend on the local equation. Consequently the initial exponents Γ(j A) at z of the
sections of j A satisfy Γ(j A) + Γ(h A) ⊆ Γ((j + h) A): the sets of initial exponents of the
first variation (16) and of the comparison (21) form a graded semigroup.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open scoped Pointwise

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Algebra

variable {σ K : Type*} [Field K]

/-- A unit power series has initial exponent zero for every monomial order. -/
theorem isInitialMonomial_zero_of_isUnit (m : MonomialOrder σ) {u : MvPowerSeries σ K}
    (hu : IsUnit u) : IsInitialMonomial m u 0 := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero
  · rw [map_zero] at hq
    exact absurd hq (not_lt.mpr (m.zero_le _))

/-- Multiplying a finite-dimensional space of power series by a unit does not change its set of
initial exponents. -/
theorem initialMonomialFinset_eq_of_unit_mul (m : MonomialOrder σ)
    (S S' : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] [FiniteDimensional K S']
    {u : MvPowerSeries σ K} (hu : IsUnit u) (h : ∀ φ, φ ∈ S' ↔ ∃ ψ ∈ S, φ = u * ψ) :
    initialMonomialFinset m S' = initialMonomialFinset m S := by
  ext p
  rw [mem_initialMonomialFinset, mem_initialMonomialFinset]
  constructor
  · rintro ⟨φ, hφ, hp⟩
    obtain ⟨ψ, hψ, rfl⟩ := (h φ).mp hφ
    obtain ⟨v, rfl⟩ := hu
    have h2 := initialMonomial_mul m
      (isInitialMonomial_zero_of_isUnit m (v⁻¹ : (MvPowerSeries σ K)ˣ).isUnit) hp
    rw [← mul_assoc, Units.inv_mul, one_mul, zero_add] at h2
    exact ⟨ψ, hψ, h2⟩
  · rintro ⟨ψ, hψ, hp⟩
    refine ⟨u * ψ, (h _).mpr ⟨ψ, hψ, rfl⟩, ?_⟩
    have h2 := initialMonomial_mul m (isInitialMonomial_zero_of_isUnit m hu) hp
    rwa [zero_add] at h2

end Algebra

section Graded

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]

/-- The Taylor expansion at a point z of a model of the pullbacks of the sections of j A, for the
local equation f^j of j A at π(z). -/
noncomputable def cartierGradedPullbackTaylor (A : CartierDivisor Y) (z : X)
    (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) :
    Γ((j • A).sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin n) K where
  toFun s := stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient (j • A) π z (f ^ j)
    (cartierLocalEquation_pow A (π z) f hf j) s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c s := by
    rw [cartierStalkPullbackCoefficient_smul, map_mul, RingHom.id_apply, Algebra.smul_def]
    congr 1
    exact (stalkTaylorExpansion z ez).commutes c

/-- The graded Taylor maps at a point of a model are multiplicative for the product of
sections. -/
theorem cartierGradedPullbackTaylor_product (A : CartierDivisor Y) (z : X)
    (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) (j h : ℕ)
    (s : Γ((j • A).sheaf, ⊤)) (t : Γ((h • A).sheaf, ⊤)) :
    cartierGradedPullbackTaylor π A z f hf ez (j + h) (cartierGradedSectionProduct A j h s t) =
      cartierGradedPullbackTaylor π A z f hf ez j s *
        cartierGradedPullbackTaylor π A z f hf ez h t := by
  change stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient ((j + h) • A) π z
    (f ^ (j + h)) (cartierLocalEquation_pow A (π z) f hf (j + h))
    (cartierGradedSectionProduct A j h s t)) = _
  rw [cartierStalkPullbackCoefficient_apply,
    cartierGradedSectionProduct_localCoefficient A (π z) f hf j h s t, map_mul, map_mul]
  rfl

/-- The Taylor map of j A for the chosen local equation is a unit multiple of the graded Taylor
map. -/
theorem cartierPullbackTaylorLinear_eq_unit_mul_graded (A : CartierDivisor Y) (z : X)
    (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) :
    ∃ u : MvPowerSeries (Fin n) K, IsUnit u ∧ ∀ s : Γ((j • A).sheaf, ⊤),
      cartierPullbackTaylorLinear (j • A) π z ez s =
        u * cartierGradedPullbackTaylor π A z f hf ez j s := by
  obtain ⟨v, hv⟩ := cartierStalkPullbackCoefficient_change_frame (j • A) π z
    (Classical.choose ((j • A).exists_isLocalEquationAt (π z))) (f ^ j)
    (Classical.choose_spec ((j • A).exists_isLocalEquationAt (π z)))
    (cartierLocalEquation_pow A (π z) f hf j)
  refine ⟨stalkTaylorExpansion z ez (v : X.presheaf.stalk z),
    v.isUnit.map (stalkTaylorExpansion z ez), fun s => ?_⟩
  change stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient (j • A) π z
    (Classical.choose ((j • A).exists_isLocalEquationAt (π z)))
    (Classical.choose_spec ((j • A).exists_isLocalEquationAt (π z))) s) = _
  rw [hv s, map_mul]
  rfl

/-- The initial exponents at z of the sections of j A do not depend on the local equation: the
Taylor map for the chosen equation and the graded Taylor map have the same initial exponents. -/
theorem initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded (m : MonomialOrder (Fin n))
    (A : CartierDivisor Y) (z : X) (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ)
    [FiniteDimensional K Γ((j • A).sheaf, ⊤)] :
    initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear (j • A) π z ez)) =
      initialMonomialFinset m (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez j)) := by
  obtain ⟨u, hu, huT⟩ := cartierPullbackTaylorLinear_eq_unit_mul_graded π A z f hf ez j
  refine initialMonomialFinset_eq_of_unit_mul m _ _ hu fun φ => ?_
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, huT s⟩
  · rintro ⟨ψ, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, huT s⟩

/-- The initial exponents at a point of a model of the sections of the multiples of a Cartier
divisor form a graded semigroup: Γ(j A) + Γ(h A) ⊆ Γ((j + h) A). -/
theorem initialMonomialFinset_cartierPullbackTaylorLinear_add_subset
    (m : MonomialOrder (Fin n)) (A : CartierDivisor Y)
    [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)] (z : X)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) (j h : ℕ) :
    initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear (j • A) π z ez)) +
        initialMonomialFinset m (LinearMap.range (cartierPullbackTaylorLinear (h • A) π z ez)) ⊆
      initialMonomialFinset m
        (LinearMap.range (cartierPullbackTaylorLinear ((j + h) • A) π z ez)) := by
  classical
  obtain ⟨f, hf⟩ := A.exists_isLocalEquationAt (π z)
  rw [initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded π m A z f hf ez j,
    initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded π m A z f hf ez h,
    initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded π m A z f hf ez (j + h)]
  refine initialMonomialFinset_add_subset m _ _ _ ?_
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  exact ⟨cartierGradedSectionProduct A j h s t,
    cartierGradedPullbackTaylor_product π A z f hf ez j h s t⟩

end Graded

end MixedFujita
