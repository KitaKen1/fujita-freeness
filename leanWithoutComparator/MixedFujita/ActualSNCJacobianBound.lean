/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DVRJacobianOrderBound

/-!
The SNC coordinate-sum inequality on actual smooth birational models. The actual
codimension-one stalk is a DVR; its coordinate derivations compute the actual
relative Jacobian. The DVR determinant bound is transported through the real stalk
and function-field maps, and distinct selected SNC coordinates form a sub-sum.
No completion coordinates or formal-test-valuation comparison are supplied.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- At an actual DVR stalk, the finite natural ring order is the integer prime order. -/
theorem scheme_regular_ringOrd_and_primeOrd_nat {T : Scheme.{u}}
    [IsIntegral T] [IsLocallyNoetherian T] (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (a : T.presheaf.stalk (t : T)) (ha : a ≠ 0) :
    ∃ m : ℕ, Ring.ord (T.presheaf.stalk (t : T)) a = m ∧
      T.ord (algebraMap (T.presheaf.stalk (t : T)) T.functionField a) (t : T) = (m : ℤ) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  refine ⟨m, hm.symm, scheme_ord_regular_eq_localAdicOrder_nat t a ha m ?_⟩
  rw [dvr_localAdicOrder_eq_ringOrd]
  exact hm.symm

/-- Distinct selected coordinates, with zero for absent components, give a sub-sum. -/
theorem option_selected_sum_le {ι α : Type*} [Fintype ι] [Fintype α]
    (σ : ι → Option α) (hσ : ∀ i j a, σ i = some a → σ j = some a → i = j)
    (v : α → ℤ) (hv : ∀ a, 0 ≤ v a) :
    ∑ i, (σ i).elim 0 v ≤ ∑ a, v a := by
  classical
  have hi (i : ι) : (σ i).elim 0 v = ∑ a, if σ i = some a then v a else 0 := by
    cases h : σ i with
    | none => simp
    | some a => simp
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : ∃ i, σ i = some a
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : σ j ≠ some a := fun hj => hji (hσ j i a hj hi)
      simp [hj]
    · simp
  · have hz : ∀ i, σ i ≠ some a := by simpa using h
    simpa [hz] using hv a

section Charts

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]

/-- A pulled chart coordinate is the actual image of its pulled germ in the model stalk. -/
theorem chartCoordinate_pullback_eq_stalk (t : T) (c : EtaleChart K X n)
    (hc : ρ t ∈ c.U) (a : Fin n) :
    (dominantFunctionFieldMap ρ).hom (etaleChartCoordinateRationalUnit c a : X.functionField) =
      algebraMap (T.presheaf.stalk t) T.functionField
        (schemeStalkMapAlgHom (K := K) ρ t
          (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X a))) := by
  simp only [etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
  rw [← X.algebraMap_germ_eq_germToFunctionField hc,
    dominantFunctionFieldMap_algebraMap]
  rfl

variable [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

include hρ in
/-- Every full source-coordinate system satisfies the Jacobian order bound on the actual model. -/
theorem actual_chart_coordinate_sum_le_jacobian (t : CodimensionOnePoint T)
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) :
    ∑ a, T.ord ((dominantFunctionFieldMap ρ).hom
      (etaleChartCoordinateRationalUnit c a : X.functionField)) (t : T) ≤
        1 + T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI := smoothOverField_stalk_regular (K := K) (t : T)
  letI := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  let f := fun a => schemeStalkMapAlgHom (K := K) ρ (t : T)
    (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X a))
  let D := fun j => etaleCoordinateDerivation (etaleChartStalkCoords c' (t : T) hc')
    (etaleChartStalkCoords_formallyEtale c' (t : T) hc') j
  let J := Matrix.of fun a j => D j (f a)
  have hf (a : Fin n) : f a ≠ 0 := by
    have h := (map_ne_zero (dominantFunctionFieldMap ρ).hom).mpr
      (Units.ne_zero (etaleChartCoordinateRationalUnit c a))
    rw [chartCoordinate_pullback_eq_stalk ρ (t : T) c hc a] at h
    intro hz
    exact h (by
      change algebraMap (T.presheaf.stalk (t : T)) T.functionField (f a) = 0
      rw [hz, map_zero])
  have hJmap : chartRelativeJacobianDet ρ c c' =
      algebraMap (T.presheaf.stalk (t : T)) T.functionField J.det := by
    simpa only [J, D, f, etaleRelativeJacobian, stalkFunctionFieldAlgHom,
      AlgHom.coe_mk] using
      chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc'
  have hJ0 : J.det ≠ 0 := by
    have h := (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c c').ne_zero
    rw [hJmap] at h
    intro hz
    exact h (by rw [hz, map_zero])
  choose m hm hprime using fun a => scheme_regular_ringOrd_and_primeOrd_nat t (f a) (hf a)
  obtain ⟨k, hk, hkprime⟩ := scheme_regular_ringOrd_and_primeOrd_nat t J.det hJ0
  have hbound := dvr_derivation_jacobian_order_bound D f hf
  change ∑ a, Ring.ord (T.presheaf.stalk (t : T)) (f a) ≤
    1 + Ring.ord (T.presheaf.stalk (t : T)) J.det at hbound
  simp_rw [hm] at hbound
  rw [hk, ← Nat.cast_sum, ← Nat.cast_one, ← Nat.cast_add] at hbound
  have hnat : ∑ a, m a ≤ 1 + k := by exact_mod_cast hbound
  simp_rw [chartCoordinate_pullback_eq_stalk ρ (t : T) c hc]
  change ∑ a, T.ord (algebraMap (T.presheaf.stalk (t : T)) T.functionField (f a))
    (t : T) ≤ _
  simp_rw [hprime]
  rw [hJmap, hkprime, ← Nat.cast_sum]
  exact_mod_cast hnat

include hρ in
/-- The SNC family selects distinct coordinates, so the actual all-model sum inequality follows. -/
theorem actual_snc_coordinate_sum_le_jacobian (t : CodimensionOnePoint T)
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U) {r : ℕ}
    (ξ : Fin r → X) (σ : Fin r → Option (Fin n)) (hcsnc : IsSNCChart c ξ σ)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) :
    ∑ i, T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T) ≤
        1 + T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
  let v := fun a => T.ord ((dominantFunctionFieldMap ρ).hom
    (etaleChartCoordinateRationalUnit c a : X.functionField)) (t : T)
  have hi (i : Fin r) : T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T) = (σ i).elim 0 v := by
    cases hσ : σ i with
    | none => simp [sncChartComponentEquation, hσ]
    | some a => simp only [sncChartComponentEquation, hσ, Option.elim_some]; rfl
  have hv (a : Fin n) : 0 ≤ v a := by
    change 0 ≤ T.ord ((dominantFunctionFieldMap ρ).hom
      (etaleChartCoordinateRationalUnit c a : X.functionField)) (t : T)
    rw [chartCoordinate_pullback_eq_stalk ρ (t : T) c hc a]
    exact scheme_ord_nonneg_of_mem_stalk (t : T) _ ⟨_, rfl⟩
  simp_rw [hi]
  exact (option_selected_sum_le σ hcsnc.1 v hv).trans
    (actual_chart_coordinate_sum_le_jacobian ρ hρ t c hc c' hc')

end Charts

end MixedFujita
