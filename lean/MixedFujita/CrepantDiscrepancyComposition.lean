/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalComposition

/-!
Pulling back the rational top form through an actual tower agrees with pulling
it back along the composite. The crepant pair on the intermediate model has
exactly the source's discrepancy on every model factoring through it. Thus klt
ascends to every actual proper birational model. Descending klt requires a
comparison with models that do not factor through it, and is treated separately.
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

section Tower

variable {K : Type u} [Field K] {n : ℕ} {X T U : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral U]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) (σ : U ⟶ T) [IsDominant ρ] [IsDominant σ]
  [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The actual pulled rational form coefficient is functorial in a birational tower. -/
theorem crepantPullbackFormUnit_comp (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) :
    crepantPullbackFormUnit (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f c'' =
    crepantPullbackFormUnit σ hσ c' (crepantPullbackFormUnit ρ hρ c f c') c'' := by
  apply Units.ext
  simp only [crepantPullbackFormUnit, Units.val_mul, Units.coe_map,
    IsUnit.unit_spec, map_mul, dominantFunctionFieldMap_comp, CommRingCat.hom_comp]
  change (dominantFunctionFieldAlgHom (K := K) σ
      (dominantFunctionFieldAlgHom (K := K) ρ (f : X.functionField))) *
      chartRelativeJacobianDet (σ ≫ ρ) c c'' =
    (dominantFunctionFieldAlgHom (K := K) σ
      (dominantFunctionFieldAlgHom (K := K) ρ (f : X.functionField))) *
      dominantFunctionFieldAlgHom (K := K) σ (chartRelativeJacobianDet ρ c c') *
      chartRelativeJacobianDet σ c' c''
  rw [chartRelativeJacobianDet_comp, mul_assoc]

/-- Actual pulled-form Cartier divisors agree for the composite and the tower. -/
theorem pullbackFormDivisor_comp (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n)
    (hU : iSup (fun e : EtaleChart K U n => e.U) = ⊤) :
    pullbackFormDivisor (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f c'' hU =
    pullbackFormDivisor σ hσ c' (crepantPullbackFormUnit ρ hρ c f c') c'' hU := by
  change canonicalDivisor n c'' hU + principalCartierDivisor U
    (crepantPullbackFormUnit (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f c'') =
    canonicalDivisor n c'' hU + principalCartierDivisor U
      (crepantPullbackFormUnit σ hσ c' (crepantPullbackFormUnit ρ hρ c f c') c'')
  rw [crepantPullbackFormUnit_comp]

/-- Discrepancy of the crepant Cartier pullback equals the source discrepancy on the composite. -/
theorem logDiscrepancyDivisor_comp (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (c' : EtaleChart K T n) (c'' : EtaleChart K U n)
    (hU : iSup (fun e : EtaleChart K U n => e.U) = ⊤) :
    logDiscrepancyDivisor n (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c f d D c'' hU =
    logDiscrepancyDivisor n σ hσ c' (crepantPullbackFormUnit ρ hρ c f c') d
      (cartierPullback ρ D) c'' hU := by
  unfold logDiscrepancyDivisor
  rw [pullbackFormDivisor_comp ρ σ hρ hσ c f c' c'' hU, cartierPullback_comp]

end Tower

section Ascent

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- All-model klt ascends to the actual crepant Cartier pullback on any proper
birational intermediate scheme admitting the reference chart. The intermediate
scheme need not be smooth; every test model is composed with its actual map. -/
theorem logPairIsKlt_crepant_pullback (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (c' : EtaleChart K T n) :
    LogPairIsKlt c' (crepantPullbackFormUnit ρ hρ c f c') d (cartierPullback ρ D) := by
  intro U _ _ _ _ σ _ _ _ hσ c'' t ht
  have h := hklt U (σ ≫ ρ)
    (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) c'' t ht
  rw [logDiscrepancyDivisor_comp ρ σ hρ hσ c f d D c' c'' etaleCharts_cover] at h
  exact h

end Ascent

end MixedFujita
