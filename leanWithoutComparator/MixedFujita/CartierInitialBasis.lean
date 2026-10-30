/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGradedTaylor
public import MixedFujita.BasisOptimality

/-!
Construct adapted bases and initial-exponent witnesses in the actual
global section spaces O(j*A), using the actual Taylor coefficient map.
The determinant comparison now applies directly to competing geometric
section bases. Given completion coordinates and finite dimensionality
remain inputs; geometric minimality under moving centers is not asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

noncomputable def cartierGradedCoefficientMap {σ : Type*}
    (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    Γ((j • A).sheaf, ⊤) →ₗ[K] (m.syn → K) :=
  (monomialCoefficientMap m).comp (cartierGradedTaylor A x f hf coordinates j)

theorem cartierGradedCoefficientMap_injective {σ : Type*}
    (A : CartierDivisor X) (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f) (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    Function.Injective (cartierGradedCoefficientMap A x f hf m coordinates j) :=
  (monomialCoefficientMap_injective m).comp
    (cartierGradedTaylor_injective A x f hf coordinates j)

section FiniteSections
variable (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
  [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]

noncomputable def cartierGradedInitialBasis {σ : Type*}
    [IsNoetherianRing (X.presheaf.stalk x)] (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    Module.Basis (initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates j))
      K Γ((j • A).sheaf, ⊤) :=
  initialCoefficientBasis _ (cartierGradedCoefficientMap_injective A x f hf m coordinates j)

theorem cartierGradedInitialBasis_spec {σ : Type*}
    [IsNoetherianRing (X.presheaf.stalk x)] (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ)
    (p : initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates j)) :
    IsInitialMonomial m (cartierGradedTaylor A x f hf coordinates j
      (cartierGradedInitialBasis A x f hf m coordinates j p)) (m.toSyn.symm p.val) := by
  rw [initialMonomial_iff_initialCoefficient, m.toSyn.apply_symm_apply]
  exact initialCoefficientBasis_spec _
    (cartierGradedCoefficientMap_injective A x f hf m coordinates j) p

theorem cartierGradedInitialBasis_index_card {σ : Type*}
    [IsNoetherianRing (X.presheaf.stalk x)] (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) :
    (initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates j)).ncard =
      Module.finrank K Γ((j • A).sheaf, ⊤) :=
  initialIndexSet_card _ (cartierGradedCoefficientMap_injective A x f hf m coordinates j)

noncomputable def cartierInitialSection {σ : Type*} (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) (p : σ →₀ ℕ)
    (hp : p ∈ cartierGradedInitialExponents A x f hf m coordinates j) :
    Γ((j • A).sheaf, ⊤) :=
  Classical.choose ((cartierGradedInitialExponents_mem A x f hf m coordinates j p).mp hp)

theorem cartierInitialSection_spec {σ : Type*} (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) (p : σ →₀ ℕ)
    (hp : p ∈ cartierGradedInitialExponents A x f hf m coordinates j) :
    IsInitialMonomial m (cartierGradedTaylor A x f hf coordinates j
      (cartierInitialSection A x f hf m coordinates j p hp)) p :=
  Classical.choose_spec ((cartierGradedInitialExponents_mem A x f hf m coordinates j p).mp hp)

theorem cartierInitialSection_ne_zero {σ : Type*} (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K) (j : ℕ) (p : σ →₀ ℕ)
    (hp : p ∈ cartierGradedInitialExponents A x f hf m coordinates j) :
    cartierInitialSection A x f hf m coordinates j p hp ≠ 0 := by
  intro hzero
  have h := (cartierInitialSection_spec A x f hf m coordinates j p hp).1
  apply h
  rw [hzero, map_zero]
  exact map_zero _

theorem weightedCartierInitialBasis_exponential_optimal {σ : Type*} [Fintype σ]
    [IsNoetherianRing (X.presheaf.stalk x)] (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K)
    (w : σ → ℝ) (v z : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (j : ℕ)
    [Fintype (initialIndexSet (cartierGradedCoefficientMap A x f hf
      (weightedMonomialOrder m w v hw) coordinates j))]
    (B : Module.Basis (initialIndexSet (cartierGradedCoefficientMap A x f hf
      (weightedMonomialOrder m w v hw) coordinates j)) K Γ((j • A).sheaf, ⊤))
    {c : ℝ} (hc : 0 < c) :
    (∑ p, Real.exp (-powerSeriesPerturbedValue m w v z hw
      (cartierGradedTaylor A x f hf coordinates j
        (cartierGradedInitialBasis A x f hf (weightedMonomialOrder m w v hw) coordinates j p))
          0 / c)) ≤
      ∑ i, Real.exp (-powerSeriesPerturbedValue m w v z hw
        (cartierGradedTaylor A x f hf coordinates j (B i)) 0 / c) := by
  let n := weightedMonomialOrder m w v hw
  apply initialCoefficientBasis_exponential_optimal
    (cartierGradedCoefficientMap A x f hf n coordinates j)
    (cartierGradedCoefficientMap_injective A x f hf n coordinates j) B
    (fun p => realExponentWeight w (n.toSyn.symm p))
    (fun s => powerSeriesPerturbedValue m w v z hw
      (cartierGradedTaylor A x f hf coordinates j s) 0) hc
  · intro s p hp
    exact powerSeriesPerturbedValue_le_weight_of_coeff m w v z hw hp
  · intro p
    exact powerSeriesPerturbedValue_zero m w v z hw
      (cartierGradedInitialBasis_spec A x f hf n coordinates j p)

theorem weightedCartierInitialBasis_objective_optimal {σ : Type*} [Fintype σ]
    [IsNoetherianRing (X.presheaf.stalk x)] (m : MonomialOrder σ)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries σ K)
    (w : σ → ℝ) (v z : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (j : ℕ)
    [Fintype (initialIndexSet (cartierGradedCoefficientMap A x f hf
      (weightedMonomialOrder m w v hw) coordinates j))]
    (B : Module.Basis (initialIndexSet (cartierGradedCoefficientMap A x f hf
      (weightedMonomialOrder m w v hw) coordinates j)) K Γ((j • A).sheaf, ⊤))
    (discrepancy : ℝ → ℝ) (t : ℝ) {c : ℝ} (hc : 0 < c) :
    sectionExponentialObjective Finset.univ t c discrepancy
      (fun p => powerSeriesPerturbedValue m w v z hw
        (cartierGradedTaylor A x f hf coordinates j
          (cartierGradedInitialBasis A x f hf (weightedMonomialOrder m w v hw)
            coordinates j p))) 0 ≤
      sectionExponentialObjective Finset.univ t c discrepancy
        (fun i => powerSeriesPerturbedValue m w v z hw
          (cartierGradedTaylor A x f hf coordinates j (B i))) 0 := by
  rw [sectionExponentialObjective_factor, sectionExponentialObjective_factor]
  apply mul_le_mul_of_nonneg_left
    (weightedCartierInitialBasis_exponential_optimal A x f hf m coordinates w v z hw j B hc)
  exact div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)

end FiniteSections
end MixedFujita
