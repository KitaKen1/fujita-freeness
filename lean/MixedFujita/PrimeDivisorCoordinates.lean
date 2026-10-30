/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DivisorialLogDiscrepancy

/-!
Coordinates along prime divisors and the birational case (step 6). In characteristic zero a nonzero
power series H without constant term does not divide all of its partial derivatives: if d is an
exponent of minimal degree with a nonzero coefficient and d_j ≥ 1, the coefficient of ∂H/∂X_j at
d - e_j is d_j times that of H at d, while a multiple of H has no terms below the order of H.
Through the Taylor expansion, an element a of the maximal ideal of a local ring with étale
coordinates has some coordinate derivative ∂a/∂y_j outside (a): the local equation h of a prime
divisor E does not have all its derivatives vanishing on E, so at the points of E where ∂h/∂y_j
does not vanish (a nonempty open subset of E) the chart can be adapted to E, and ord_E is a
monomial test valuation there. For a birational morphism the function field map is an
isomorphism, the chain rule for φ⁻¹ ∘ φ = id makes every Jacobian determinant J(c, c') a unit, so
K_{T/X} is defined with no further condition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential MvPowerSeries
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {n : ℕ}

section PowerSeries

variable {σ K : Type*} [Field K]

/-- A nonzero power series without constant term does not divide all its partial derivatives
(characteristic zero). -/
theorem exists_not_dvd_pderiv [CharZero K] {H : MvPowerSeries σ K} (hH : H ≠ 0)
    (h0 : constantCoeff H = 0) : ∃ j, ¬H ∣ pderiv j H := by
  have hfin : (H.order.toNat : ℕ∞) = H.order :=
    ENat.natCast_toNat (by rwa [ne_eq, order_eq_top_iff])
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (by rwa [coeff_zero_eq_constantCoeff_apply])
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    exact hd0 (Finsupp.ext fun j => by_contra fun hj => h ⟨j, by simpa using hj⟩)
  refine ⟨j, fun ⟨g, hg⟩ => ?_⟩
  set d' := d - Finsupp.single j 1 with hd'
  have hdd : d' + Finsupp.single j 1 = d :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj))
  have hcoeff : coeff d' (pderiv j H) ≠ 0 := by
    rw [coeff_pderiv, hdd]
    exact mul_ne_zero hd (Nat.cast_add_one_ne_zero _)
  apply hcoeff
  apply coeff_of_lt_order
  rw [hg]
  have hdeg' : (Finsupp.degree d' : ℕ) + 1 = Finsupp.degree d := by
    rw [← hdd, map_add, Finsupp.degree_single]
  calc ((Finsupp.degree d' : ℕ) : ℕ∞) < ((Finsupp.degree d : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : (Finsupp.degree d' : ℕ) < Finsupp.degree d)
    _ = H.order := hdeg
    _ ≤ H.order + g.order := le_self_add
    _ ≤ (H * g).order := le_order_mul

end PowerSeries

section Taylor

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- Some coordinate derivative of a is outside (a), if the Taylor expansion of a is nonzero
without constant term. -/
theorem exists_derivation_notMem_span_of_taylor [CharZero K]
    (φ : S →ₐ[K] MvPowerSeries (Fin n) K) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hφ : ∀ i, φ (y (MvPolynomial.X i)) = X i) (a : S)
    (ha : constantCoeff (φ a) = 0) (ha0 : φ a ≠ 0) :
    ∃ j, etaleCoordinateDerivation y hy j a ∉ Ideal.span {a} := by
  obtain ⟨j, hj⟩ := exists_not_dvd_pderiv ha0 ha
  refine ⟨j, fun hmem => hj ?_⟩
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨φ g, ?_⟩
  rw [← etaleCoordinateDerivation_taylor φ y hy hφ j a, ← hg, map_mul, mul_comm]

end Taylor

section Scheme

universe u

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Point

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- At a point with a K-valued stalk point, a nonzero element a of the maximal ideal has some
chart derivative ∂a/∂y_j outside (a): the derivatives of a local equation of a prime divisor do
not all vanish on the divisor. -/
theorem etaleChart_exists_derivation_notMem_span [CharZero K] (c : EtaleChart K X n) (p : X)
    (hp : p ∈ c.U) (β : X.presheaf.stalk p →ₐ[K] K) [IsNoetherianRing (X.presheaf.stalk p)]
    (a : X.presheaf.stalk p) (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (ha0 : a ≠ 0) :
    ∃ j, etaleCoordinateDerivation (etaleChartStalkCoords c p hp)
      (etaleChartStalkCoords_formallyEtale c p hp) j a ∉ Ideal.span {a} := by
  obtain ⟨e, he, hord⟩ := etaleChart_exists_taylorCoordinates c p hp β
  have hy := etaleChartCenteredStalkCoords_formallyEtale c p hp β
  have hord' : (stalkTaylorExpansion p e a).order = localAdicOrder (X.presheaf.stalk p) a := hord a
  have hconst : constantCoeff (stalkTaylorExpansion p e a) = 0 := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (stalkTaylorExpansion p e a).order := by
      rw [hord', localAdicOrder_nat_le_iff, pow_one]
      exact ha
    rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_of_lt_order
    rw [map_zero]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_one) h1
  have hne : stalkTaylorExpansion p e a ≠ 0 := by
    intro h0
    rw [h0, order_zero] at hord'
    exact ha0 ((localAdicOrder_eq_top_iff a).mp hord'.symm)
  obtain ⟨j, hj⟩ := exists_derivation_notMem_span_of_taylor (stalkTaylorExpansion p e) _ hy he a
    hconst hne
  refine ⟨j, ?_⟩
  rw [etaleCoordinateDerivation_apply] at hj ⊢
  rw [etaleChartCenteredStalkCoords_basis] at hj
  exact hj

end Point

section Birational

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [X.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
  [ρ.IsOver (Spec (CommRingCat.of K))]

/-- For a birational morphism, every chart Jacobian determinant J(c, c') is a unit. -/
theorem isUnit_chartRelativeJacobianDet_of_bijective
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (c : EtaleChart K X n)
    (c' : EtaleChart K T n) : IsUnit (chartRelativeJacobianDet ρ c c') := by
  let φ := dominantFunctionFieldAlgHom (K := K) ρ
  let ε := AlgEquiv.ofBijective φ hρ
  have h := etaleRelativeJacobian_det_comp φ ε.symm.toAlgHom (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords c') (etaleChartFunctionFieldCoords_formallyEtale c')
    (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
  have hid : ε.symm.toAlgHom.comp φ = AlgHom.id K X.functionField := by
    apply AlgHom.ext
    intro a
    change ε.symm (ε a) = a
    exact ε.symm_apply_apply a
  rw [hid, etaleRelativeJacobian_id_det (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
    (etaleChartFunctionFieldCoords_formallyEtale c), Module.Basis.det_self] at h
  have hu : IsUnit (ε.symm (chartRelativeJacobianDet ρ c c')) :=
    IsUnit.of_mul_eq_one _ h.symm
  have hu' := hu.map ε
  rwa [AlgEquiv.apply_symm_apply] at hu'

variable (n) in
/-- The relative canonical divisor of a birational morphism. -/
noncomputable def birationalRelativeCanonicalDivisor
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) : CartierDivisor T :=
  relativeCanonicalDivisor n ρ c₀ hX c'₀ hT (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀)

end Birational

end Scheme

end MixedFujita
