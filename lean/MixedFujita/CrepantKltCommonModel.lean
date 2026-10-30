/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeLifts

/-!
Crepant klt on one model implies the strict discrepancy bound on another test
model if an actual common proper smooth birational model is provided. Prime
lifts and the discrepancy comparison are proved internally.

The common model and commuting square are explicit inputs. Their existence for
every test model, and therefore unconditional all-model klt descent, are not
asserted in this module.
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

variable {K : Type u} [Field K] {n : ℕ} {X T U V : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral U] [IsIntegral V]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))] [V.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian U] [IsLocallyNoetherian V]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (V ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) (σ : U ⟶ X) (α : V ⟶ T) (β : V ⟶ U)
  [IsDominant ρ] [IsDominant σ] [IsDominant α] [IsDominant β]
  [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]
  [α.IsOver (Spec (CommRingCat.of K))] [β.IsOver (Spec (CommRingCat.of K))]
  [IsProper α] [IsProper β]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
  (hα : Function.Bijective (dominantFunctionFieldAlgHom (K := K) α))
  (hβ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) β))

include hα hβ in
/-- On a given actual common smooth model, crepant klt gives every test-model discrepancy bound. -/
theorem crepant_klt_discrepancy_bound_of_common_model (hsquare : α ≫ ρ = β ≫ σ)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (cT : EtaleChart K T n) (cU : EtaleChart K U n) (cV : EtaleChart K V n)
    (hklt : LogPairIsKlt cT (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D))
    (x : CodimensionOnePoint U) :
    -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U) := by
  obtain ⟨v, _, hv⟩ :=
    proper_birational_exists_prime_discrepancy_lift σ β hσ hβ c f d D cU cV x
  have h := hklt V α hα cV (v : V) v.property
  rw [← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cV etaleCharts_cover] at h
  have h' : -(d : ℤ) < cartierCoefficient (logDiscrepancyDivisor n (β ≫ σ)
      (dominantFunctionFieldAlgHom_comp_bijective σ β hσ hβ) c f d D cV etaleCharts_cover)
      (v : V) := by
    simpa only [hsquare] using h
  simpa only [hv] using h'

end MixedFujita
