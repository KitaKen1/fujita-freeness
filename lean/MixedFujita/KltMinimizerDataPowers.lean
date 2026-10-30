/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.CartierSectionPowers
public import MixedFujita.KltPairs

/-!
The data of the minimizer at one degree give the data for every divisibility condition.

Suppose the data of the minimizer (`KltIsolationMinimizerData`) exist for some m₁: sections s_i
of j L, a model, c and q. For k ≥ 1 take the powers s_i^k, which are sections of (k j) L, with
c/k and k q. The Cartier coefficients of the pullbacks of the zero divisors are multiplied by k,
so the profile polytope of every point is multiplied by k. The products c · q, the left sides of
(24) and the budget d (k j) Σ c_i/k = d j Σ c_i do not change. With k = m₀ the degree k j is
divisible by m₀, so one good degree gives the data for every m₀ ≥ 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Polytope

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Multiplying the divisors by k > 0 multiplies the profile polytope of every point by k. -/
theorem inSNCProfilePolytope_nsmul_iff {ι : Type*} {r : ℕ} (ξ : Fin r → X) (d : ℕ)
    (B : CartierDivisor X) (Dv : ι → CartierDivisor X) (q : ι → ℝ) (p : X) {k : ℕ}
    (hk : 0 < k) :
    InSNCProfilePolytope ξ d B (fun i => k • Dv i) (fun i => (k : ℝ) * q i) p ↔
      InSNCProfilePolytope ξ d B Dv q p := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  constructor
  · rintro ⟨μ, h0, h1, hsupp, hq⟩
    refine ⟨μ, h0, h1, hsupp, fun i => ?_⟩
    have h := hq i
    simp only [cartierCoefficient_nsmul, Int.cast_mul, Int.cast_natCast] at h
    apply mul_left_cancel₀ hk'
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · rintro ⟨μ, h0, h1, hsupp, hq⟩
    refine ⟨μ, h0, h1, hsupp, fun i => ?_⟩
    simp only [cartierCoefficient_nsmul, Int.cast_mul, Int.cast_natCast]
    rw [hq i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end Polytope

section Data

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- The data of the minimizer from data with sections of a divisor E equal to j L. -/
theorem kltIsolationMinimizerData_of_eq_nsmul (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D L : CartierDivisor Y) (m₀ : ℕ) (x : Y) (E : CartierDivisor Y) (j : ℕ)
    (hE : E = j • L) (hjm₀ : m₀ ∣ j) {N : ℕ} (s : Fin N → Γ(E.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (y : X) (c q : Fin N → ℝ)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) =
        0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) (z : X) =
        0)
    (hy : π y = x) (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q y)
    (hpoly : ∀ p ∈ π ⁻¹' ({x} : Set Y), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor E (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q p →
      p ∈ π ⁻¹' ({x} : Set Y))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    KltIsolationMinimizerData cY fY d D L m₀ x := by
  subst hE
  exact ⟨j, N, s, hs, X, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, π, inferInstance, inferInstance, inferInstance, hπ, cX, r, ξ, y, c, q, hjm₀,
    hinj, hξ, hsnc, hBsupp, hDsupp, hy, hc, hcq, hqy, hpoly, hcentre, hbudget⟩

/-- The data of the minimizer for some m₁ give the data for every m₀ ≥ 1: the m₀-th powers of
the sections, with c/m₀ and m₀ q, are data at the degree m₀ j. -/
theorem kltIsolationMinimizerData_of_kltIsolationMinimizerData (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D L : CartierDivisor Y) {m₁ : ℕ} (x : Y)
    (h : KltIsolationMinimizerData cY fY d D L m₁ x) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY fY d D L m₀ x := by
  obtain ⟨j, N, s, hs, X, hXi, hXN, hXo, hXp, hXs, π, hdom, hover, hprop, hπ, cX, r, ξ, y, c, q,
    -, hinj, hξ, hsnc, hBsupp, hDsupp, hy, hc, hcq, hqy, hpoly, hcentre, hbudget⟩ := h
  have hk : 0 < m₀ := hm₀
  have hk' : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast hk
  -- the powers of the sections and their zero divisors
  have hs' : ∀ i, cartierSectionPower (j • L) (s i) m₀ ≠ 0 := fun i =>
    cartierSectionPower_ne_zero (j • L) (s i) (hs i) m₀
  have hzero : ∀ i, cartierPullback π (cartierSectionZeroDivisor (m₀ • j • L)
      (cartierSectionPower (j • L) (s i) m₀) (hs' i)) =
      m₀ • cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)) := fun i => by
    rw [cartierSectionZeroDivisor_power, cartierPullback_nsmul]
  have hcoef : ∀ i (z : X), (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
      (m₀ • j • L) (cartierSectionPower (j • L) (s i) m₀) (hs' i))) z : ℝ) =
      (m₀ : ℝ) * cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) z := fun i z => by
    rw [hzero i, cartierCoefficient_nsmul]
    push_cast
    ring
  -- the polytopes are multiplied by m₀
  have hpolyiff : ∀ p : X, InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (m₀ • j • L)
        (cartierSectionPower (j • L) (s i) m₀) (hs' i))) (fun i => (m₀ : ℝ) * q i) p ↔
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i))) q p :=
    fun p => by
      simp only [hzero]
      exact inSNCProfilePolytope_nsmul_iff ξ d _ _ q p hk
  refine kltIsolationMinimizerData_of_eq_nsmul cY fY d D L m₀ x (m₀ • j • L) (m₀ * j)
    (smul_smul m₀ j L) (dvd_mul_right m₀ j) (fun i => cartierSectionPower (j • L) (s i) m₀) hs'
    X π hπ cX ξ y (fun i => c i / m₀) (fun i => (m₀ : ℝ) * q i) hinj hξ hsnc hBsupp ?_ hy ?_ ?_
    ((hpolyiff y).mpr hqy) ?_ (fun p hp hpq => hcentre p hp ((hpolyiff p).mp hpq)) ?_
  · intro i z hz
    rw [hzero i, cartierCoefficient_nsmul, hDsupp i z hz, mul_zero]
  · exact fun i => div_pos (hc i) hk'
  · rw [← hcq]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · intro p hp hpq k hkp
    have h := hpoly p hp ((hpolyiff p).mp hpq) k hkp
    calc ∑ i, c i / m₀ * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m₀ • j • L) (cartierSectionPower (j • L) (s i) m₀) (hs' i))) (ξ k) : ℝ)
        = ∑ i, c i * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoef i]
          field_simp
      _ ≤ _ := h
  · have heq : ((d * (m₀ * j) : ℕ) : ℝ) * ∑ i, c i / m₀ = ((d * j : ℕ) : ℝ) * ∑ i, c i := by
      rw [← Finset.sum_div]
      push_cast
      field_simp
    rw [heq]
    exact hbudget

end Data

end MixedFujita
