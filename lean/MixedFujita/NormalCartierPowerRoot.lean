/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NormalCartierWeilSectionComparison
public import MixedFujita.NormalBirationalPrimeLifts

/-! normal Cartier格子の係数≥-1から正則関数の冪根閉性。 See reports/check-246-lc-radical-reduced-fixed-subscheme-lifting.json for the verified scope. The actual lc kernel image ideal is radical and its nonempty lower-dimensional subscheme W is reduced. One fixed I and W works for all nef-big adjoints. Usual KV gives actual restriction section lifting; any nonzero restricted section removes an original basepoint on W. Usual KV itself, restricted-section nonvanishing and stable-base-locus placement remain unproved; no normal lc-center adjunction, klt BPF or full F1/F2 is claimed. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Orders of powers are ordinary integer multiples for every nonzero rational function. -/
theorem scheme_ord_pow_of_ne_zero
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (z : T.functionField) (hz : z ≠ 0) (m : ℕ) (t : T) :
    T.ord (z ^ m) t = (m : ℤ) * T.ord z t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, T.ord_mul (pow_ne_zero m hz) hz, ih]
    push_cast
    ring


/-- A regular function belongs to a Cartier lattice with all coefficients at least -1
as soon as ANY natural power belongs. The normal Hartogs and DVR criteria are internal. -/
theorem normal_cartier_regular_power_root_mem_sections
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (C : CartierDivisor T) (hC : ∀ t : CodimensionOnePoint T, -1 ≤ cartierCoefficient C (t : T))
    (U : T.Opens) [Nonempty U] (a : Γ(T, U)) (m : ℕ)
    (hpow : Scheme.Modules.Hom.app (toRationalFunctions T) U (a ^ m) ∈ C.sections U) :
    Scheme.Modules.Hom.app (toRationalFunctions T) U a ∈ C.sections U := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, Submodule.zero_mem]
  let : ∀ t : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (t : T)) :=
    fun t => by let := hnorm (t : T); exact normal_codimensionOne_stalk_DVR t
  let z := T.germToFunctionField U a
  have hz : z ≠ 0 := (map_ne_zero_iff _ (T.germToFunctionField_injective U)).mpr ha
  have heq (b : Γ(T, U)) : Scheme.Modules.Hom.app (toRationalFunctions T) U b =
      (rationalFunctionsEquiv (X := T) U).symm (T.germToFunctionField U b) := by
    apply (rationalFunctionsEquiv (X := T) U).injective
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, LinearEquiv.apply_symm_apply]
  rw [heq, map_pow] at hpow
  rw [heq]
  apply (normal_cartier_rational_mem_sections_iff_prime_orders hnorm C U z).mpr
  right
  intro t ht
  have hp := ((normal_cartier_rational_mem_sections_iff_prime_orders hnorm C U (z ^ m)).mp
    hpow).resolve_left (pow_ne_zero m hz)
  have hb := hp t ht
  rw [scheme_ord_pow_of_ne_zero z hz m] at hb
  have hnon := Scheme.ord_germToFunctionField_nonneg a ht
  change 0 ≤ T.ord z (t : T) at hnon
  have hc := hC t
  by_cases hv : T.ord z (t : T) = 0
  · rw [hv, mul_zero] at hb
    omega
  · omega

end MixedFujita
