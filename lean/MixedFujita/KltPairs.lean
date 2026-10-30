/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierDivisorCoefficients
public import MixedFujita.PrimeDivisorGeneralPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
Klt pairs (step 1). A pair (Y, B) with r(K_Y + B) Cartier is described by a rational top form
ω = f₀ dx_1 ∧ ⋯ ∧ dx_n in the coordinates of an étale chart c₀ (so K_Y = div ω, computed on the
charts, which cover the codimension-one points of a normal variety in characteristic zero), an
integer r ≥ 1 and a Cartier divisor D = r(K_Y + B). The boundary is effective when D - r div ω has
nonnegative coefficients. For a proper birational morphism ρ : T → Y from a smooth T, the pulled
back form has divisor div(ρ*ω) = K_T + div(φ(f₀) J(c₀, c'₀)), which does not depend on the
reference chart c'₀ of T, and the discrepancy divisor r(K_T - ρ*(K_Y + B)) = r div(ρ*ω) - ρ*D has
the coefficients r a(E; Y, B) along the prime divisors E of T (for the strict transform of a
component of B this is -r b). The pair is klt when all these coefficients are > -r on every such
model. If Y is smooth and B = 0, the discrepancy divisor is r K_{T/Y}, whose local equations are
regular, so (Y, 0) is klt and the boundary is effective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ}

section PullbackGroup

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

theorem cartierPullback_neg (D : CartierDivisor X) :
    cartierPullback ρ (-D) = -cartierPullback ρ D := by
  have h := cartierPullback_add ρ D (-D)
  rw [add_neg_cancel, cartierPullback_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem cartierPullback_sub (D E : CartierDivisor X) :
    cartierPullback ρ (D - E) = cartierPullback ρ D - cartierPullback ρ E := by
  rw [sub_eq_add_neg, cartierPullback_add, cartierPullback_neg, ← sub_eq_add_neg]

theorem cartierPullback_nsmul (D : CartierDivisor X) (m : ℕ) :
    cartierPullback ρ (m • D) = m • cartierPullback ρ D := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul, cartierPullback_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, cartierPullback_add, ih]

end PullbackGroup

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Charts

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

theorem etaleChartCanonicalEquation_mul_swap (a b : EtaleChart K Y n) :
    etaleChartCanonicalEquation a b * etaleChartCanonicalEquation b a = 1 := by
  apply Units.ext
  rw [Units.val_mul, etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val,
    Module.Basis.det_mul_det, Module.Basis.det_self, Units.val_one]

end Charts

section Pullback

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [Y.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))] (ρ : T ⟶ Y) [IsDominant ρ]
  [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The divisor of the pulled back form ρ*ω, for ω = f₀ dx_1 ∧ ⋯ ∧ dx_n in the chart c₀:
K_T + div(φ(f₀) J(c₀, c'₀)) for the reference chart c'₀ of T. -/
noncomputable def pullbackFormDivisor (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    CartierDivisor T :=
  canonicalDivisor n c'₀ hT + principalCartierDivisor T
    (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f₀ *
      (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀).unit)

/-- div(ρ*ω) does not depend on the reference chart of T. -/
theorem pullbackFormDivisor_change_reference (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (c'₀ c'₁ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    pullbackFormDivisor ρ hρ c₀ f₀ c'₁ hT = pullbackFormDivisor ρ hρ c₀ f₀ c'₀ hT := by
  unfold pullbackFormDivisor
  rw [canonicalDivisor_change_reference c'₀ c'₁ hT, add_assoc, ← principalCartierDivisor_mul]
  congr 2
  apply Units.ext
  have hJ := chartRelativeJacobianDet_change ρ c₀ c₀ c'₀ c'₁
  have hg : (etaleChartCanonicalEquation c₀ c₀ : Y.functionField) = 1 := by
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
  rw [hg, map_one, one_mul] at hJ
  have hswap := congrArg Units.val (etaleChartCanonicalEquation_mul_swap c'₁ c'₀)
  rw [Units.val_mul, Units.val_one] at hswap
  rw [Units.val_mul, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hJ]
  linear_combination (↑(Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f₀ :
    T.functionFieldˣ) * chartRelativeJacobianDet ρ c₀ c'₀) * hswap

variable (n) in
/-- The discrepancy divisor r(K_T - ρ*(K_Y + B)) = r div(ρ*ω) - ρ*D. -/
noncomputable def logDiscrepancyDivisor (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (r : ℕ)
    (D : CartierDivisor Y) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) : CartierDivisor T :=
  r • pullbackFormDivisor ρ hρ c₀ f₀ c'₀ hT - cartierPullback ρ D

end Pullback

section Pairs

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

variable (n) in
/-- Every codimension-one point lies in an étale chart: Y is smooth in codimension one, as a
normal variety in characteristic zero. -/
def CodimOneChartCovered (K : Type u) [Field K] (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of K))] :
    Prop :=
  ∀ ξ : Y, Order.coheight ξ = 1 → ∃ c : EtaleChart K Y n, ξ ∈ c.U

/-- The boundary B = D/r - div ω is effective: on every chart c, where div ω has the local
equation f₀ g_c, the coefficients of D are at least r times those of div ω. -/
def LogPairBoundaryEffective [IsLocallyNoetherian Y] (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (r : ℕ) (D : CartierDivisor Y) : Prop :=
  ∀ (c : EtaleChart K Y n) (ξ : Y), ξ ∈ c.U → Order.coheight ξ = 1 →
    (r : ℤ) * Y.ord ((f₀ * etaleChartCanonicalEquation c₀ c : Y.functionFieldˣ) :
      Y.functionField) ξ ≤ cartierCoefficient D ξ

/-- The pair (Y, B) with r(K_Y + B) = D and K_Y = div ω is klt: for every proper birational
morphism ρ : T → Y from a smooth T over K, every coefficient of the discrepancy divisor
r(K_T - ρ*(K_Y + B)) along a prime divisor of T is > -r, that is a(E; Y, B) > -1. -/
def LogPairIsKlt (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (r : ℕ) (D : CartierDivisor Y) :
    Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ Y) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (c'₀ : EtaleChart K T n)
    (ξ : T), Order.coheight ξ = 1 →
      -(r : ℤ) < cartierCoefficient
        (logDiscrepancyDivisor n ρ hρ c₀ f₀ r D c'₀ etaleCharts_cover) ξ

end Pairs

section Smooth

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- For a smooth Y and B = 0, the discrepancy divisor is r K_{T/Y}. -/
theorem logDiscrepancyDivisor_boundary_zero {T : Scheme.{u}} [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ Y) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (r : ℕ) (c'₀ : EtaleChart K T n) :
    logDiscrepancyDivisor n ρ hρ c₀ f₀ r
        (r • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y f₀)) c'₀ etaleCharts_cover =
      r • birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover c'₀ etaleCharts_cover := by
  unfold logDiscrepancyDivisor pullbackFormDivisor birationalRelativeCanonicalDivisor
    relativeCanonicalDivisor smoothCanonicalDivisor
  rw [cartierPullback_nsmul, cartierPullback_add, cartierPullback_principal,
    principalCartierDivisor_mul, ← nsmul_sub]
  congr 1
  abel

/-- A smooth variety with zero boundary is klt (indeed terminal: K_{T/Y} is effective). -/
theorem smooth_logPairIsKlt_boundary_zero (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (r : ℕ) (hr : 1 ≤ r) :
    LogPairIsKlt c₀ f₀ r (r • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y f₀)) := by
  intro T _ _ _ _ ρ _ _ _ hρ c'₀ ξ _
  rw [logDiscrepancyDivisor_boundary_zero ρ hρ c₀ f₀ r c'₀, cartierCoefficient_nsmul]
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K Y n, ρ ξ ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top (ρ ξ))
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, ξ ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top ξ)
  have h0 : 0 ≤ cartierCoefficient
      (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover c'₀ etaleCharts_cover) ξ :=
    cartierCoefficient_nonneg_of_mem_range
      (relativeCanonicalDivisor_isLocalEquationAt ρ c₀ etaleCharts_cover c'₀ etaleCharts_cover
        (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀) ξ c hc c' hc')
      (relativeCanonicalDivisor_localEquation_mem_stalk ρ c₀ c'₀
        (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀) ξ c hc c' hc')
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  nlinarith

/-- For a smooth Y, the zero boundary is effective. -/
theorem smooth_logPairBoundaryEffective_zero [IsLocallyNoetherian Y] (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (r : ℕ) :
    LogPairBoundaryEffective c₀ f₀ r (r • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y f₀)) := by
  intro c ξ hξ _
  have hloc := (canonicalDivisor_isLocalEquationAt c₀ etaleCharts_cover c hξ).mul
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor ξ f₀)
  refine le_of_eq ?_
  rw [cartierCoefficient_nsmul,
    show smoothCanonicalDivisor c₀ = canonicalDivisor n c₀ etaleCharts_cover from rfl,
    cartierCoefficient_eq_ord hloc, mul_comm f₀]

end Smooth

end MixedFujita
