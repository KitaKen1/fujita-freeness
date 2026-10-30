/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DiscrepancyPrimeComparison

/-!
An actual birational stalk map over a valuation stalk is bijective: regular
elements in the target stalk descend through the actual function-field map.
Thus proper birational maps lift every prime of a smooth target to an actual
prime with the same stalk and discrepancy coefficient. No supplied stalk
isomorphism or prime-lift certificate is required in the smooth applications.

Existence of a common smooth dominating model for two unrelated models remains
separate from these lift and coefficient-comparison theorems.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Stalks

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (ρ : T ⟶ X) [IsDominant ρ]

attribute [local instance] cartierGlobalStalkAlgebra

/-- Actual birational maps are stalk isomorphisms over valuation stalks. -/
theorem stalkMap_bijective_of_birational_valuation_stalk
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom) (t : T)
    [ValuationRing (X.presheaf.stalk (ρ t))] : Function.Bijective (ρ.stalkMap t) := by
  constructor
  · intro a b hab
    apply IsFractionRing.injective (X.presheaf.stalk (ρ t)) X.functionField
    apply (dominantFunctionFieldMap ρ).hom.injective
    rw [dominantFunctionFieldMap_algebraMap ρ t a,
      dominantFunctionFieldMap_algebraMap ρ t b, hab]
  · intro a
    obtain ⟨g, hg⟩ := hρ.2 (algebraMap (T.presheaf.stalk t) T.functionField a)
    obtain ⟨b, hb⟩ := mem_range_stalk_of_pullback ρ t g ⟨a, hg.symm⟩
    refine ⟨b, ?_⟩
    apply IsFractionRing.injective (T.presheaf.stalk t) T.functionField
    rw [← dominantFunctionFieldMap_algebraMap, hb, hg]

omit [IsIntegral X] [IsIntegral T] [IsDominant ρ] in
/-- Actual stalk isomorphisms preserve the point's coheight. -/
theorem coheight_eq_of_stalkMap_bijective (t : T)
    (hρt : Function.Bijective (ρ.stalkMap t)) : Order.coheight t = Order.coheight (ρ t) := by
  have h := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective (ρ.stalkMap t).hom hρt)
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_injective h.symm

end Stalks

section Smooth

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

include hρ n in
/-- Smooth codimension-one geometry supplies the actual birational stalk isomorphism. -/
theorem stalkMap_bijective_of_birational_over_smooth_prime (t : T)
    (hξ : Order.coheight (ρ t) = 1) : Function.Bijective (ρ.stalkMap t) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let ξ : CodimensionOnePoint X := ⟨ρ t, hξ⟩
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) ξ
  exact stalkMap_bijective_of_birational_valuation_stalk ρ hρ t

variable [IsProper ρ]

include hρ n in
/-- Every prime of a smooth target has an actual prime lift with a bijective actual stalk map. -/
theorem proper_birational_exists_prime_lift (x : CodimensionOnePoint X) :
    ∃ t : CodimensionOnePoint T, ρ (t : T) = (x : X) ∧
      Function.Bijective (ρ.stalkMap (t : T)) := by
  obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant ρ (x : X)
  have hξ : Order.coheight (ρ t) = 1 := by simpa only [ht] using x.property
  have hb := stalkMap_bijective_of_birational_over_smooth_prime (n := n) ρ hρ t hξ
  have hcod : Order.coheight t = 1 := (coheight_eq_of_stalkMap_bijective ρ t hb).trans hξ
  exact ⟨⟨t, hcod⟩, ht, hb⟩

end Smooth

section Discrepancy

variable {K : Type u} [Field K] {n : ℕ} {X T U : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral U]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) (σ : U ⟶ T) [IsDominant ρ] [IsDominant σ]
  [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- Actual discrepancy is preserved above a smooth prime, without supplied local isomorphisms. -/
theorem logDiscrepancyDivisor_comp_coefficient_over_smooth_prime
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) (t : CodimensionOnePoint U)
    (hξ : Order.coheight (σ (t : U)) = 1) :
    cartierCoefficient (logDiscrepancyDivisor n (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f d D c'' etaleCharts_cover)
      (t : U) =
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D c' etaleCharts_cover)
      (σ (t : U)) :=
  logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective ρ σ hρ hσ c f d D c' c'' t hξ
    (stalkMap_bijective_of_birational_over_smooth_prime (n := n) σ hσ (t : U) hξ)

variable [IsProper σ]

/-- A given proper smooth upper model contains an actual prime with the earlier discrepancy. -/
theorem proper_birational_exists_prime_discrepancy_lift
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) (x : CodimensionOnePoint T) :
    ∃ t : CodimensionOnePoint U, σ (t : U) = (x : T) ∧
      cartierCoefficient (logDiscrepancyDivisor n (σ ≫ ρ)
        (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f d D c'' etaleCharts_cover)
        (t : U) =
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D c' etaleCharts_cover) (x : T) := by
  obtain ⟨t, ht, _⟩ := proper_birational_exists_prime_lift (n := n) σ hσ x
  refine ⟨t, ht, ?_⟩
  have hξ : Order.coheight (σ (t : U)) = 1 := by simpa only [ht] using x.property
  simpa only [ht] using
    logDiscrepancyDivisor_comp_coefficient_over_smooth_prime ρ σ hρ hσ c f d D c' c'' t hξ

end Discrepancy

end MixedFujita
