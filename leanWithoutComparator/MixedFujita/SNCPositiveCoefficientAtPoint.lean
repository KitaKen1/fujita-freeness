/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCEffectiveStalkProduct

/-!
An effective divisor supported on an actual SNC family has a positive component
through every point where its local equation is a nonunit. The local equation
is factored by the existing stalk-unit product theorem; components away from
the point have unit coordinates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- The stalk coordinate of an SNC component missing the point is a unit. -/
theorem isSNCChart_coordinate_isUnit_of_notMem_closure
    (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (hsnc : IsSNCChart c ξ σ) (x : X) (hx : x ∈ c.U) (i : Fin r)
    (hnot : x ∉ closure ({ξ i} : Set X)) :
    IsUnit ((σ i).elim 1 fun j => etaleChartStalkCoords c x hx (MvPolynomial.X j)) := by
  cases hσ : σ i with
  | none => simp only [hσ, Option.elim_none]; exact isUnit_one
  | some j =>
    simp only [hσ, Option.elim_some]
    have hset := hsnc.2 i
    rw [hσ, Option.elim_some] at hset
    have hb : x ∈ X.basicOpen (c.coords (MvPolynomial.X j)) := by
      by_contra hb
      apply hnot
      have hm : x ∈ X.zeroLocus ({c.coords (MvPolynomial.X j)} : Set Γ(X, c.U)) ∩ c.U :=
        ⟨by rw [Scheme.zeroLocus_singleton]; exact hb, hx⟩
      rw [← hset] at hm
      exact hm.1
    exact (X.mem_basicOpen _ x hx).mp hb

/-- Nonunit local equations force an actual positive component through the point. -/
theorem snc_effective_exists_positive_coefficient_through_point
    (D : CartierDivisor X) (hD : D.IsEffective) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient D (t : X) = 0)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (hnonunit : ¬ IsUnit a) :
    ∃ i, x ∈ closure ({ξ i} : Set X) ∧ 0 < cartierCoefficient D (ξ i) := by
  classical
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  obtain ⟨u, hu⟩ := snc_effective_localEquation_stalk_unit_product D hD c ξ hinj hξ σ hc
    hsupport x hx f hf a ha
  by_contra hno
  apply hnonunit
  rw [hu]
  apply u.isUnit.mul
  apply IsUnit.prod_iff.mpr
  intro i _
  by_cases hi : x ∈ closure ({ξ i} : Set X)
  · have hb := cartierCoefficient_nonneg_of_isEffective D hD (ξ i)
    have hnot : ¬ 0 < cartierCoefficient D (ξ i) := fun h => hno ⟨i, hi, h⟩
    have hz : cartierCoefficient D (ξ i) = 0 := by omega
    simp only [hz, Int.toNat_zero, pow_zero]
    exact isUnit_one
  · exact (isSNCChart_coordinate_isUnit_of_notMem_closure c ξ σ hc x hx i hi).pow _

end MixedFujita
