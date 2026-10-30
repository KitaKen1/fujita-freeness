/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalSNCBoundaryKlt
public import MixedFujita.SmoothStalkNormality

/-!
An ordinary SNC configuration supplies normality of the actual stalks. This
removes the explicit normality input from the signed local product, all-model
discrepancy formula and klt theorem. Resolution existence and comparison with
a singular source are separate geometric tasks.
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

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]

section Configuration

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

omit [IsLocallyNoetherian X] in
/-- SNC charts themselves supply normality of every actual stalk. -/
theorem isSNCFamily_stalk_isIntegrallyClosed {r : ℕ} {ξ : Fin r → X}
    (hsnc : IsSNCFamily K n ξ) (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  exact etaleChart_stalk_isIntegrallyClosed c x hx

/-- Construct the actual signed local product from SNC configuration alone. -/
theorem isSNCFamily_boundary_local_product
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0) (x : X) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (_hx : x ∈ c.U),
      IsSNCChart c ξ σ ∧
      ∃ (f : X.functionFieldˣ) (_ : B.IsLocalEquationAt x f) (u : (X.presheaf.stalk x)ˣ),
        (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField u *
          (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient B (ξ i) :
            X.functionFieldˣ) :=
  normal_isSNCFamily_boundary_local_product (isSNCFamily_stalk_isIntegrallyClosed hsnc)
    B ξ hinj hξ hsnc hsupport x

end Configuration

variable [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

section Models

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Exact discrepancy coefficients on every actual smooth birational model,
with no supplied normality or local boundary product. -/
theorem isSNCFamily_actual_discrepancy_formula
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (_ : ρ (t : T) ∈ c.U),
      IsSNCChart c ξ σ ∧ ∀ (c' : EtaleChart K T n), (t : T) ∈ c'.U →
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T) =
            (d : ℤ) * T.ord (chartRelativeJacobianDet ρ c c') (t : T) -
              ∑ i, cartierCoefficient B (ξ i) *
                T.ord ((dominantFunctionFieldMap ρ).hom
                  (sncChartComponentEquation c σ i : X.functionField)) (t : T) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact normal_isSNCFamily_actual_discrepancy_formula ρ hρ
    (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
    c₀ f₀ d B ξ hinj hξ hsnc hsupport c'₀ t

/-- Signed SNC coefficients below d give the strict discrepancy bound at every
prime of every actual smooth birational model, without a geometric estimate input. -/
theorem isSNCFamily_actual_discrepancy_bound
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ))
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) :
    -(d : ℤ) < cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      c'₀ etaleCharts_cover) (t : T) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact normal_isSNCFamily_discrepancy_bound_of_jacobian_sum ρ hρ
    (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
    c₀ f₀ d hd B ξ hinj hξ hsnc hsupport hb c'₀ t
    (fun c σ hc hcsnc c' hc' =>
      actual_snc_coordinate_sum_le_jacobian ρ hρ t c hc ξ σ hcsnc c' hc')

end Models

/-- Ordinary SNC geometry and signed coefficients<d imply all-model klt. -/
theorem isSNCFamily_logPairIsKlt
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ)) :
    LogPairIsKlt c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact normal_isSNCFamily_logPairIsKlt
    (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
    c₀ f₀ d hd B ξ hinj hξ hsnc hsupport hb

end MixedFujita
