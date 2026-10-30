/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianValuationBound
public import MixedFujita.CompletionLocalMap
public import MixedFujita.CartierStalkPullbackOrder
public import MixedFujita.ClosedImmersionCohomology
public import MixedFujita.CartierAmpleDefinition

/-!
Lemma 1 for monomial test valuations on other smooth models. Every K-algebra map of power series
rings sends the variables into the maximal ideal: otherwise X_i - c would be a unit with image of
constant term zero. Let ρ : T' → T be a morphism over the base field and p ∈ T'. For a morphism
over the base field the stalk map is a K-algebra map, so in completion coordinates at ρ(p) and at
p the map of completed local rings is a K-algebra map ψ of power series rings, carrying the Taylor
expansion of a local function at ρ(p) to that of its pullback at p. For the monomial valuation v
with weights w at p, the Jacobian inequality gives v(ρ^* s) ≤ A(v) ord_{ρ(p)}(s) for every nonzero
section s of a Cartier divisor, with A(v) = Σ w + v(det J_ψ), the log discrepancy of v over T, and
the value does not depend on the local equation. With the uniform order bound this is Lemma 1 for
these test valuations on a smooth projective variety: v(ρ^* s) ≤ A(v) c j for nonzero sections of
j J or of j A with A ample, one constant c for all closed centres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPowerSeries
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section PowerSeries

variable {σ τ K : Type*} [Field K]

/-- Every K-algebra map of power series rings sends the variables into the maximal ideal. -/
theorem constantCoeff_algHom_X (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries τ K) (i : σ) :
    constantCoeff (ψ (X i)) = 0 := by
  by_contra hc
  set c := constantCoeff (ψ (X i)) with hcdef
  have hunit : IsUnit (X i - C c : MvPowerSeries σ K) := by
    rw [isUnit_iff_constantCoeff, map_sub, constantCoeff_X, constantCoeff_C, zero_sub,
      IsUnit.neg_iff]
    exact Ne.isUnit hc
  have hC : ψ (C c) = C c := by
    rw [c_eq_algebraMap, c_eq_algebraMap, AlgHom.commutes]
  have hzero : constantCoeff (ψ (X i - C c)) = 0 := by
    rw [map_sub, hC, map_sub, constantCoeff_C, ← hcdef, sub_self]
  have hu := isUnit_iff_constantCoeff.mp (hunit.map ψ)
  rw [hzero] at hu
  exact not_isUnit_zero hu

/-- A unit has weighted order zero. -/
theorem weightedOrder_eq_zero_of_isUnit (w : σ → ℕ) {f : MvPowerSeries σ K} (hf : IsUnit f) :
    f.weightedOrder w = 0 := by
  have hc : coeff (0 : σ →₀ ℕ) f ≠ 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (isUnit_iff_constantCoeff.mp hf).ne_zero
  refine le_antisymm ?_ zero_le
  calc f.weightedOrder w ≤ (Finsupp.weight w 0 : ℕ∞) := weightedOrder_le w hc
    _ = 0 := by simp

/-- lct ≥ 1/mult through the Jacobian, for every K-algebra map of power series rings. -/
theorem weightedOrder_algHom_le_logDiscrepancy_mul_order_of_algHom [CharZero K] [Fintype σ]
    [DecidableEq σ] (w : σ → ℕ) (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)
    {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    (ψ f).weightedOrder w ≤
      (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) * f.order :=
  weightedOrder_algHom_le_logDiscrepancy_mul_order ψ w (constantCoeff_algHom_X ψ) hf

end PowerSeries

universe u

variable {K : Type u} [Field K] {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower

/-- For a morphism over the base field, the stalk map is a map of algebras over it. -/
noncomputable def schemeStalkMapAlgHom (ρ : T' ⟶ T) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') : T.presheaf.stalk (ρ p) →ₐ[K] T'.presheaf.stalk p :=
  { (ρ.stalkMap p).hom with
    commutes' := fun c => by
      change ρ.stalkMap p (T.presheaf.germ ⊤ (ρ p) trivial
          (Scheme.Modules.baseRingToGlobalSections K T c)) =
        T'.presheaf.germ ⊤ p trivial (Scheme.Modules.baseRingToGlobalSections K T' c)
      rw [Scheme.Hom.germ_stalkMap_apply, ← scheme_appTop_baseRingToGlobalSections K ρ c]
      rfl }

theorem schemeStalkMap_maximalIdeal_map_le (ρ : T' ⟶ T) (p : T') :
    (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p))).map (ρ.stalkMap p).hom ≤
      IsLocalRing.maximalIdeal (T'.presheaf.stalk p) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  have h := scheme_stalkMap_maximalIdeal_pow_mem ρ p r 1 (by rwa [pow_one])
  rwa [pow_one] at h

theorem schemeStalkMapAlgHom_apply (ρ : T' ⟶ T) [ρ.IsOver (Spec (CommRingCat.of K))] (p : T')
    (a : T.presheaf.stalk (ρ p)) : schemeStalkMapAlgHom (K := K) ρ p a = ρ.stalkMap p a := rfl

theorem schemeStalkMapAlgHom_maximalIdeal_map_le (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') :
    (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p))).map
        (schemeStalkMapAlgHom (K := K) ρ p).toRingHom ≤
      IsLocalRing.maximalIdeal (T'.presheaf.stalk p) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  have h := scheme_stalkMap_maximalIdeal_pow_mem ρ p r 1 (by rwa [pow_one])
  rw [pow_one] at h
  exact h

/-- The map of completed local rings of ρ at p in the given completion coordinates. -/
noncomputable def schemeCompletedStalkMap (ρ : T' ⟶ T) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {n : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K :=
  ep.toAlgHom.comp ((adicCompletionMapₐ K _ _ (schemeStalkMapAlgHom (K := K) ρ p)
    (schemeStalkMapAlgHom_maximalIdeal_map_le (K := K) ρ p)).comp ez.symm.toAlgHom)

/-- The completed stalk map carries Taylor expansions at ρ(p) to Taylor expansions at p. -/
theorem schemeCompletedStalkMap_algebraMap (ρ : T' ⟶ T) [ρ.IsOver (Spec (CommRingCat.of K))]
    (p : T') {n : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K) (a : T.presheaf.stalk (ρ p)) :
    schemeCompletedStalkMap ρ p ez ep (ez (algebraMap _
        (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
          (T.presheaf.stalk (ρ p))) a)) =
      ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p)) (ρ.stalkMap p a)) := by
  show ep (adicCompletionMapₐ K _ _ (schemeStalkMapAlgHom (K := K) ρ p)
      (schemeStalkMapAlgHom_maximalIdeal_map_le (K := K) ρ p) (ez.symm (ez (algebraMap _
        (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
          (T.presheaf.stalk (ρ p))) a)))) = _
  rw [AlgEquiv.symm_apply_apply]
  have h1 : algebraMap (T.presheaf.stalk (ρ p))
      (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
        (T.presheaf.stalk (ρ p))) a = AdicCompletion.of _ _ a := rfl
  have h2 : algebraMap (T'.presheaf.stalk p)
      (AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p)) (T'.presheaf.stalk p))
        (ρ.stalkMap p a) = AdicCompletion.of _ _ (ρ.stalkMap p a) := rfl
  rw [h1, h2, adicCompletionMapₐ_of]
  rfl

variable [IsIntegral T]

/-- The monomial valuation with weights w, in completion coordinates at p, of the pullback of a
section along ρ. -/
noncomputable def cartierPullbackMonomialValuation (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T')
    {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (s : Γ(D.sheaf, ⊤)) : ℕ∞ :=
  (ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
    (T'.presheaf.stalk p)) (cartierStalkPullbackCoefficient D ρ p
      (Classical.choose (D.exists_isLocalEquationAt (ρ p)))
      (Classical.choose_spec (D.exists_isLocalEquationAt (ρ p))) s))).weightedOrder w

omit [T.Over (Spec (CommRingCat.of K))] in
/-- The pulled-back monomial valuation does not depend on the local equation. -/
theorem cartierPullbackMonomialValuation_eq (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T')
    {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (s : Γ(D.sheaf, ⊤)) (f : T.functionFieldˣ)
    (hf : D.IsLocalEquationAt (ρ p) f) :
    cartierPullbackMonomialValuation D ρ p ep w s =
      (ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p)) (cartierStalkPullbackCoefficient D ρ p f hf s))).weightedOrder w := by
  obtain ⟨v, hv⟩ := cartierStalkPullbackCoefficient_change_frame D ρ p
    (Classical.choose (D.exists_isLocalEquationAt (ρ p))) f
    (Classical.choose_spec (D.exists_isLocalEquationAt (ρ p))) hf
  unfold cartierPullbackMonomialValuation
  rw [hv s, map_mul, map_mul, weightedOrder_mul]
  have hu : IsUnit (ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal
      (T'.presheaf.stalk p)) (T'.presheaf.stalk p)) (v : T'.presheaf.stalk p))) :=
    (v.isUnit.map _).map _
  rw [weightedOrder_eq_zero_of_isUnit w hu, zero_add]

/-- Lemma 1 for a monomial test valuation: v(ρ^* s) ≤ A(v) ord_{ρ(p)}(s), with
A(v) = Σ w + v(det J) for the Jacobian J of the completed stalk map. -/
theorem cartierPullbackMonomialValuation_le [CharZero K] (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') [IsNoetherianRing (T.presheaf.stalk (ρ p))]
    {n : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) {s : Γ(D.sheaf, ⊤)} (hs : s ≠ 0) :
    cartierPullbackMonomialValuation D ρ p ep w s ≤
      (((∑ i, w i : ℕ) : ℕ∞) +
          (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w) *
        cartierSectionVanishingOrder D (ρ p) s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ p)
  rw [cartierPullbackMonomialValuation_eq D ρ p ep w s f hf, cartierStalkPullbackCoefficient_apply,
    ← schemeCompletedStalkMap_algebraMap,
    ← cartierTaylorCoordinates_order_eq_vanishingOrder D (ρ p) f hf ez s,
    cartierTaylorCoordinates_apply]
  apply weightedOrder_algHom_le_logDiscrepancy_mul_order_of_algHom
  rw [← cartierTaylorCoordinates_apply]
  exact (cartierTaylorCoordinates_ne_zero_iff D (ρ p) f hf ez s).mpr hs

end MixedFujita
