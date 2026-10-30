/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCoordinateOrders

/-!
A Cartier boundary supported on a finite injective SNC prime family has the actual local
equation u * product_i x_i^(b_i), with b_i its signed integer prime coefficients and u an
actual stalk unit. Components absent from the chart contribute one. On a normal scheme
this follows by comparing all codimension-one orders and applying two-sided Hartogs;
the local product is constructed, rather than assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Products and signed powers of actual rational equations have the expected prime order. -/
theorem scheme_ord_prod_zpow {ι : Type*} [Fintype ι] (g : ι → X.functionFieldˣ)
    (b : ι → ℤ) (x : CodimensionOnePoint X) :
    X.ord ((∏ i, g i ^ b i : X.functionFieldˣ) : X.functionField) (x : X) =
      ∑ i, b i * X.ord (g i : X.functionField) (x : X) := by
  have h := SchemeWeilDivisor.orderAt_apply x (Additive.ofMul (∏ i, g i ^ b i))
  simp only [toMul_ofMul] at h
  rw [← h, ofMul_prod, map_sum]
  simp only [ofMul_zpow, map_zsmul, zsmul_eq_mul,
    SchemeWeilDivisor.orderAt_apply, toMul_ofMul, Int.cast_id]

/-- A Cartier boundary supported on an injective prime family is its coefficient indicator sum. -/
theorem cartierCoefficient_eq_sum_supported_family (B : CartierDivisor X) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (x : CodimensionOnePoint X) :
    cartierCoefficient B (x : X) =
      ∑ i, cartierCoefficient B (ξ i) * (if (x : X) = ξ i then 1 else 0) := by
  classical
  by_cases hx : (x : X) ∈ Set.range ξ
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simp only [hi, ite_true, mul_one]
    · intro j _ hji
      have hne : (x : X) ≠ ξ j := fun h => hji (hinj (h.symm.trans hi.symm))
      simp only [ite_eq_right hne, mul_zero]
    · simp
  · rw [hsupport x hx]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : (x : X) ≠ ξ i := fun h => hx ⟨i, h.symm⟩
    simp only [ite_eq_right hne, mul_zero]

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

/-- The coordinate equation for a present SNC component, or one for an absent component. -/
noncomputable def sncChartComponentEquation (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (i : Fin r) : X.functionFieldˣ :=
  (σ i).elim 1 (etaleChartCoordinateRationalUnit c)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- Every selected SNC component equation has the prescribed prime-order indicator. -/
theorem sncChartComponentEquation_ord (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (i : Fin r) (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    X.ord (sncChartComponentEquation c σ i : X.functionField) (x : X) =
      if (x : X) = ξ i then 1 else 0 := by
  cases hσ : σ i with
  | some a =>
    simp only [sncChartComponentEquation, hσ, Option.elim_some]
    exact isSNCChart_coordinate_ord c ξ hξ σ hc i a hσ x hx
  | none =>
    have hne : (x : X) ≠ ξ i := by
      intro heq
      have hmem : (x : X) ∈ closure ({ξ i} : Set X) ∩ c.U :=
        ⟨heq ▸ subset_closure rfl, hx⟩
      have hset := hc.2 i
      rw [hσ, Option.elim_none] at hset
      rw [hset] at hmem
      exact hmem
    simp only [sncChartComponentEquation, hσ, Option.elim_none, Units.val_one,
      TauCeti.AlgebraicGeometry.Scheme.ord_one, ite_eq_right hne]

/-- The coordinate product has precisely the coefficients of the supplied Cartier boundary. -/
theorem sncChart_boundary_product_ord (B : CartierDivisor X) (c : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    X.ord ((∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) :
      X.functionFieldˣ) : X.functionField) (x : X) = cartierCoefficient B (x : X) := by
  rw [scheme_ord_prod_zpow, cartierCoefficient_eq_sum_supported_family B ξ hinj hsupport x]
  exact Finset.sum_congr rfl fun i _ => congrArg (cartierCoefficient B (ξ i) * ·)
    (sncChartComponentEquation_ord c ξ hξ σ hc i x hx)

/-- On a normal scheme, the signed coordinate product is an actual local boundary equation
up to a constructed stalk unit. Normality is stated explicitly; the product is not an input. -/
theorem normal_isSNCChart_boundary_local_product
    [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (B : CartierDivisor X) (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (x : X) (hx : x ∈ c.U) :
    ∃ (f : X.functionFieldˣ) (_ : B.IsLocalEquationAt x f) (u : (X.presheaf.stalk x)ˣ),
      (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField u *
        (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) : X.functionFieldˣ) := by
  obtain ⟨W, hWc, hxW, f, hf⟩ := B.exists_localEquation_le c.U hx
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hloc := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxW
  obtain ⟨u, hu⟩ := normal_scheme_equal_orders_unit_ratio hnorm x W hxW f
    (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i)) (by
      intro z hz
      rw [← cartierCoefficient_eq_ord
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hz)]
      exact (sncChart_boundary_product_ord B c ξ hinj hξ σ hc hsupport z (hWc hz)).symm)
  exact ⟨f, hloc, u, hu⟩

/-- The ordinary SNC family constructs local products everywhere; its charts supply the DVRs. -/
theorem normal_isSNCFamily_boundary_local_product
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0) (x : X) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hx : x ∈ c.U),
      IsSNCChart c ξ σ ∧
      ∃ (f : X.functionFieldˣ) (_ : B.IsLocalEquationAt x f) (u : (X.presheaf.stalk x)ˣ),
        (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField u *
          (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) : X.functionFieldˣ) := by
  have : ∀ z : CodimensionOnePoint X, IsRegularLocalRing (X.presheaf.stalk (z : X)) :=
    fun z => isSNCFamily_stalk_regular hsnc (z : X)
  have : ∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    fun z => inferInstance
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  exact ⟨c, σ, hx, hc, normal_isSNCChart_boundary_local_product hnorm B c ξ hinj hξ σ hc
    hsupport x hx⟩

end MixedFujita
