/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantDiscrepancyComposition

/-!
Actual prime orders are preserved at points where the actual stalk map is an
isomorphism. The local Jacobian is a unit there by the inverse chain rule.
The existence of such lifts on a common smooth model is a separate geometric
problem; no lift or resolution is asserted here.
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

section Algebra

variable {R S F G : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field G] [Algebra S G] [IsFractionRing S G]

/-- An actual compatible fraction-field map preserves order under a DVR isomorphism. -/
theorem dvr_ordFrac_map_of_ringEquiv (e : R ≃+* S) (φ : F →+* G)
    (hφ : ∀ a, φ (algebraMap R F a) = algebraMap S G (e a)) (f : F) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, v, rfl⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hf
  have heπ : Irreducible (e π) := hπ.map e.toMulEquiv
  simp only [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, hφ]
  rw [Ring.ordFrac_of_isUnit ((Units.isUnit v).map e),
    Ring.ordFrac_irreducible heπ,
    Ring.ordFrac_of_isUnit (Units.isUnit v), Ring.ordFrac_irreducible hπ]

end Algebra

section Jacobian

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R]
  [CommRing S] [Algebra K S] {n : ℕ}

/-- The inverse chain rule makes the Jacobian of an actual algebra isomorphism a unit. -/
theorem etaleRelativeJacobian_det_isUnit_of_bijective (φ : R →ₐ[K] S)
    (hφ : Function.Bijective φ) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (hx : x.toRingHom.FormallyEtale) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) : IsUnit (etaleRelativeJacobian φ x y hy).det := by
  let e := AlgEquiv.ofBijective φ hφ
  have h := etaleRelativeJacobian_det_comp φ e.symm.toAlgHom x y hy x hx
  have hid : e.symm.toAlgHom.comp φ = AlgHom.id K R := by
    apply AlgHom.ext
    intro a
    change e.symm (e a) = a
    exact e.symm_apply_apply a
  rw [hid, etaleRelativeJacobian_id_det x x hx hx, Module.Basis.det_self] at h
  have hu : IsUnit (e.symm (etaleRelativeJacobian φ x y hy).det) :=
    IsUnit.of_mul_eq_one _ h.symm
  have hu' := hu.map e
  rwa [AlgEquiv.apply_symm_apply] at hu'

end Jacobian

section Scheme

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- At a point where the actual stalk map is bijective, the actual stalk Jacobian is a unit. -/
theorem chartRelativeJacobianDet_stalk_isUnit_of_bijective (t : T)
    (hρt : Function.Bijective (ρ.stalkMap t)) (c : EtaleChart K X n)
    (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U) :
    IsUnit (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ t)
      (etaleChartStalkCoords c (ρ t) hc) (etaleChartStalkCoords c' t hc')
      (etaleChartStalkCoords_formallyEtale c' t hc')).det :=
  etaleRelativeJacobian_det_isUnit_of_bijective _ hρt _
    (etaleChartStalkCoords_formallyEtale c (ρ t) hc) _
    (etaleChartStalkCoords_formallyEtale c' t hc')

variable [IsLocallyNoetherian X] [IsLocallyNoetherian T]

/-- A prime's actual rational-function order is preserved by its actual stalk isomorphism. -/
theorem scheme_ord_pullback_of_stalkMap_bijective (t : CodimensionOnePoint T)
    (hξ : Order.coheight (ρ (t : T)) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk (ρ (t : T)))]
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (hρt : Function.Bijective (ρ.stalkMap (t : T))) (f : X.functionField) :
    T.ord ((dominantFunctionFieldMap ρ).hom f) (t : T) = X.ord f (ρ (t : T)) := by
  by_cases hf : f = 0
  · simp [hf]
  have hne : (dominantFunctionFieldMap ρ).hom f ≠ 0 := (map_ne_zero _).mpr hf
  have he := dvr_ordFrac_map_of_ringEquiv
    (RingEquiv.ofBijective (ρ.stalkMap (t : T)).hom hρt)
    (dominantFunctionFieldMap ρ).hom
    (dominantFunctionFieldMap_algebraMap ρ (t : T)) f
  rw [T.ord_eq_iff t.property hne]
  exact he.trans ((X.ord_eq_iff hξ hf).mp rfl)

/-- Actual Cartier coefficients are preserved at a prime with bijective actual stalk map. -/
theorem cartierCoefficient_pullback_of_stalkMap_bijective (t : CodimensionOnePoint T)
    (hξ : Order.coheight (ρ (t : T)) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk (ρ (t : T)))]
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (hρt : Function.Bijective (ρ.stalkMap (t : T))) (D : CartierDivisor X) :
    cartierCoefficient (cartierPullback ρ D) (t : T) = cartierCoefficient D (ρ (t : T)) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ (t : T))
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ D (t : T) hf),
    cartierCoefficient_eq_ord hf]
  exact scheme_ord_pullback_of_stalkMap_bijective ρ t hξ hρt f

/-- The actual rational Jacobian has prime order zero where the actual stalk map is bijective. -/
theorem chartRelativeJacobianDet_ord_zero_of_stalkMap_bijective (t : CodimensionOnePoint T)
    (hρt : Function.Bijective (ρ.stalkMap (t : T))) (c : EtaleChart K X n)
    (hc : ρ (t : T) ∈ c.U) (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) :
    T.ord (chartRelativeJacobianDet ρ c c') (t : T) = 0 := by
  rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
  have hu := chartRelativeJacobianDet_stalk_isUnit_of_bijective ρ (t : T) hρt c hc c' hc'
  simpa only [IsUnit.unit_spec, stalkFunctionFieldAlgHom, AlgHom.coe_mk] using
    scheme_ord_stalk_unit (t : T) hu.unit

/-- The actual relative canonical coefficient is zero at a prime with an actual stalk isomorphism. -/
theorem birationalRelativeCanonicalDivisor_coefficient_zero_of_stalkMap_bijective
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (t : CodimensionOnePoint T) (hρt : Function.Bijective (ρ.stalkMap (t : T)))
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) :
    cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ hX c'₀ hT)
      (t : T) = 0 := by
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt ρ c₀ hX
    c'₀ hT (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀)
    (t : T) c hc c' hc'), IsUnit.unit_spec]
  exact chartRelativeJacobianDet_ord_zero_of_stalkMap_bijective ρ t hρt c hc c' hc'

end Scheme

end MixedFujita
