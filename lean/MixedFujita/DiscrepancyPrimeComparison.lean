/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalBirationalOrders

/-!
Discrepancy on an actual tower is the actual Cartier pullback of the earlier
discrepancy plus the relative canonical divisor. At a prime where the actual
stalk map is an isomorphism, the relative canonical coefficient vanishes and
the discrepancy coefficient is preserved.

This proves the comparison once such an actual prime lift is provided. The
geometric existence of a common smooth model with these lifts remains separate.
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

section Form

variable {K : Type u} [Field K] {n : ℕ} {T U : Scheme.{u}}
  [IsIntegral T] [IsIntegral U]
  [T.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  (σ : U ⟶ T) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- Pulling the actual rational form adds the actual relative canonical divisor. -/
theorem pullbackFormDivisor_eq_pullback_add_relative (c : EtaleChart K T n)
    (f : T.functionFieldˣ) (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤)
    (c' : EtaleChart K U n) (hU : iSup (fun e : EtaleChart K U n => e.U) = ⊤) :
    pullbackFormDivisor σ hσ c f c' hU =
      cartierPullback σ (canonicalDivisor n c hT + principalCartierDivisor T f) +
        birationalRelativeCanonicalDivisor n σ hσ c hT c' hU := by
  unfold pullbackFormDivisor birationalRelativeCanonicalDivisor relativeCanonicalDivisor
  rw [cartierPullback_add, cartierPullback_principal, principalCartierDivisor_mul]
  abel

end Form

section Tower

variable {K : Type u} [Field K] {n : ℕ} {X T U : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral U]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) (σ : U ⟶ T) [IsDominant ρ] [IsDominant σ]
  [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- The actual discrepancy tower formula, as an equality of Cartier divisors. -/
theorem logDiscrepancyDivisor_comp_eq_pullback_add_relative (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (c' : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) (c'' : EtaleChart K U n)
    (hU : iSup (fun e : EtaleChart K U n => e.U) = ⊤) :
    logDiscrepancyDivisor n (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f d D c'' hU =
    cartierPullback σ (logDiscrepancyDivisor n ρ hρ c f d D c' hT) +
      d • birationalRelativeCanonicalDivisor n σ hσ c' hT c'' hU := by
  rw [logDiscrepancyDivisor_comp ρ σ hρ hσ c f d D c' c'' hU]
  unfold logDiscrepancyDivisor
  rw [pullbackFormDivisor_eq_pullback_add_relative σ hσ c'
    (crepantPullbackFormUnit ρ hρ c f c') hT c'' hU,
    cartierPullback_sub, cartierPullback_nsmul, nsmul_add]
  change _ = d • cartierPullback σ
    (canonicalDivisor n c' hT + principalCartierDivisor T
      (crepantPullbackFormUnit ρ hρ c f c')) - _ + _
  abel

variable [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]

/-- On smooth actual models, a prime with bijective actual stalk map preserves discrepancy. -/
theorem logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) (t : CodimensionOnePoint U)
    (hξ : Order.coheight (σ (t : U)) = 1)
    (hσt : Function.Bijective (σ.stalkMap (t : U))) :
    cartierCoefficient (logDiscrepancyDivisor n (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f d D c'' etaleCharts_cover)
      (t : U) =
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D c' etaleCharts_cover)
      (σ (t : U)) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let ξ : CodimensionOnePoint T := ⟨σ (t : U), hξ⟩
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) ξ
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  obtain ⟨e, he⟩ : ∃ e : EtaleChart K T n, σ (t : U) ∈ e.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (σ (t : U)))
  obtain ⟨e', he'⟩ : ∃ e' : EtaleChart K U n, (t : U) ∈ e'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := U) (n := n)).symm ▸
      Opens.mem_top (t : U))
  rw [logDiscrepancyDivisor_comp_eq_pullback_add_relative ρ σ hρ hσ c f d D c'
    etaleCharts_cover c'' etaleCharts_cover, cartierCoefficient_add, cartierCoefficient_nsmul,
    cartierCoefficient_pullback_of_stalkMap_bijective σ t hξ hσt,
    birationalRelativeCanonicalDivisor_coefficient_zero_of_stalkMap_bijective σ hσ c'
      etaleCharts_cover c'' etaleCharts_cover t hσt e he e' he', mul_zero, add_zero]

end Tower

end MixedFujita
