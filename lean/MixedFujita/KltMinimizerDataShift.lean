/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneMinimizerSequence
public import MixedFujita.CartierBigDefinition

/-!
The data of the minimizer for a divisor A with a multiple linearly equivalent to L, from a
minimizing profile datum of L (steps 11 and 14).

Let l A = L + div φ. Multiplication by φ^j identifies the sections of j L with those of
j L + div φ^j = (l j) A, and the zero divisor of a section does not change under this principal
shift. So a minimal profile datum of a tuple of sections of j L with the point-centre property,
at a parameter t with d l t < 1, gives the data of the minimizer for A at the degree l j: the
same model, weights, vector c and profile q, with budget d (l j) Σ c_i = d l t < 1, where
j Σ c_i = t comes from the first-order conditions of the minimizer. The factor l in the budget is
why the hyperplane class J has to be treated with t < 1/l when J = l A up to a principal divisor.

For the hyperplane class this gives the data of the minimizer for every such A and every m₀ ≥ 1
from the minimizing profile datum of
`projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence` when l b ≤ 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Shift

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The principal shift of a nonzero section is nonzero. -/
theorem cartierPrincipalShiftLinear_ne_zero (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) (hs : s ≠ 0) :
    cartierPrincipalShiftLinear (K := K) D g s ≠ 0 := fun h =>
  hs ((cartierPrincipalShiftLinear_bijective (K := K) D g).1 (h.trans (map_zero _).symm))

/-- The zero divisor of g s as a section of D is the zero divisor of s as a section of
D + div g. -/
theorem cartierSectionZeroDivisor_principalShift (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionZeroDivisor D (cartierPrincipalShiftLinear (K := K) D g s)
        (cartierPrincipalShiftLinear_ne_zero D g s hs) =
      cartierSectionZeroDivisor (D + principalCartierDivisor Y g) s hs := by
  unfold cartierSectionZeroDivisor
  have hunit : cartierSectionUnit D (cartierPrincipalShiftLinear (K := K) D g s)
      (cartierPrincipalShiftLinear_ne_zero D g s hs) =
      g * cartierSectionUnit (D + principalCartierDivisor Y g) s hs := by
    apply Units.ext
    rw [Units.val_mul, cartierSectionUnit_val, cartierSectionUnit_val,
      cartierPrincipalShiftLinear_rational]
  rw [hunit, principalCartierDivisor_mul, add_assoc]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- Equal sections have equal zero divisors. -/
theorem cartierSectionZeroDivisor_eq_of_eq {D : CartierDivisor Y} {s s' : Γ(D.sheaf, ⊤)}
    (h : s = s') (hs : s ≠ 0) (hs' : s' ≠ 0) :
    cartierSectionZeroDivisor D s hs = cartierSectionZeroDivisor D s' hs' := by
  subst h
  rfl

end Shift

section Data

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer for a divisor A with l A = L + div φ from a minimal profile datum
of a tuple of sections of j L with the point-centre property, when d l t < 1: the principal shifts
of the sections are sections of (l j) A with the same zero divisors, and the budget
d (l j) Σ c_i = d l t is smaller than 1. -/
theorem kltIsolationMinimizerData_of_minimal_sncWeightProfile_shift
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (L A : CartierDivisor Y) {l : ℕ} (φ : Y.functionFieldˣ)
    (hlA : l • A = L + principalCartierDivisor Y φ) (x : Y)
    (j : ℕ) (hj : 1 ≤ j) {N : ℕ} (hN : 0 < N)
    (s : Fin N → Γ((j • L).sheaf, ⊤)) {t : ℝ} (ht : 0 < t) (hdt : (d : ℝ) * l * t < 1)
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ (j • L) x s)
    (hmin : ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • L) x s,
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j))
    (hlt : (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N)
    (hpc : SNCWeightProfileHasPointCentre cY fY d D₀ (j • L) x s p) :
    KltIsolationMinimizerData cY fY d D₀ A 1 x := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y, hy, hwy⟩, hA, hv⟩ := hp
  have hXprop : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
  -- the objective of the weight is the objective of its datum
  have hL : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  -- the weight is a minimizer on its model
  have hwmin : ∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
      (∃ p' ∈ π ⁻¹' ({x} : Set Y), ∀ k, w' k ≠ 0 → p' ∈ closure ({ξ k} : Set X)) →
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w' := by
    intro w' hw'0 hw'Φ
    have h := hmin (∑ k, w' k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d),
      fun i => ∑ k, w' k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ))
      ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w', hinj, hξ, hsnc, hBsupp,
        hGsupp, hw'0, hw'Φ, rfl, fun i => rfl⟩
    rw [hL]
    exact h
  -- the weight is not zero
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : p.1 = 0 := by
      rw [hA]
      simp [hall]
    have hv0 : ∀ i, p.2 i = 0 := fun i => by
      rw [hv i]
      simp [hall]
    simp only [h0, hv0, zero_div, sub_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hc, hcq, hqy, hpoly, hsum⟩ := isolation_data_of_sncWeight_minimizer hN ξ d hd _ hb
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
    (π ⁻¹' ({x} : Set Y)) ht j hj w hw0 y hy hwy hwne hwmin
  have hcentre := hpc hs X π hπ cX r ξ w hinj hξ hsnc hBsupp hGsupp hw0 ⟨y, hy, hwy⟩ hA hv
  have hq : (fun i => p.2 i / p.1) = fun i => (∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) /
      ∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) := by
    funext i
    rw [hv i, hA]
  rw [hq] at hcentre
  -- the sections of (l j) A: the principal shifts of the sections of j L
  have hE : (l * j) • A = j • L + principalCartierDivisor Y (φ ^ j) := by
    rw [mul_comm, ← smul_smul, hlA, smul_add, principalCartierDivisor_power]
  set s' : Fin N → Γ((j • L + principalCartierDivisor Y (φ ^ j)).sheaf, ⊤) := fun i =>
    (cartierPrincipalShiftEquiv (K := K) (j • L) (φ ^ j)).symm (s i) with hs'def
  have hs' : ∀ i, s' i ≠ 0 := fun i => (LinearEquiv.map_ne_zero_iff _).mpr (hs i)
  have hZ : ∀ i, cartierSectionZeroDivisor (j • L + principalCartierDivisor Y (φ ^ j)) (s' i)
      (hs' i) = cartierSectionZeroDivisor (j • L) (s i) (hs i) := by
    intro i
    rw [← cartierSectionZeroDivisor_principalShift (K := K) (j • L) (φ ^ j) (s' i) (hs' i)]
    exact cartierSectionZeroDivisor_eq_of_eq
      ((cartierPrincipalShiftEquiv (K := K) (j • L) (φ ^ j)).apply_symm_apply (s i)) _ _
  refine kltIsolationMinimizerData_of_eq_nsmul cY fY d D₀ A 1 x _ (l * j) hE.symm (one_dvd _) s'
    hs' X π hπ cX ξ y _ _ hinj hξ hsnc hBsupp ?_ hy hc hcq ?_ ?_ ?_ ?_
  · intro i z hz
    rw [hZ i]
    exact hGsupp i z hz
  · simp only [hZ]
    exact hqy
  · simp only [hZ]
    exact hpoly
  · simp only [hZ]
    exact hcentre
  · have hcast : ((d * (l * j) : ℕ) : ℝ) = (d : ℝ) * l * (j : ℝ) := by push_cast; ring
    rw [hcast, mul_assoc, hsum]
    exact hdt

end Data

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer at x for a divisor A with l A = J + div φ, for every m₀ ≥ 1, from
the hypotheses of `projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence` for the
hyperplane class J when l b ≤ 1. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_shift_of_degree_sequence
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal) {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ)
    (hs : 1 ≤ s) (hsb : (s : ℝ) * b = m + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ m ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      ∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ)
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b → ∀ w : Y, w ⤳ x → w ≠ x →
      ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
        ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ G → w ⤳ y →
        sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) x
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j ≤
          sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) y
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j)
    (A : CartierDivisor Y) {l : ℕ} (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (hlb : (l : ℝ) * b ≤ 1) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  obtain ⟨t, -, ht, htb, j, hj1, hN, B, p, hp, hmin, hlt, hpc⟩ :=
    projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence e g hg hggen he hm cY x hxc
      hgx hb s hs hsb ht₀ hδ hδ1 hdim hdeg hclosed hstart h6
  have hdt : ((1 : ℕ) : ℝ) * l * t < 1 := by
    rw [Nat.cast_one, one_mul]
    rcases (Nat.cast_nonneg l : (0 : ℝ) ≤ l).lt_or_eq with hl | hl
    · calc (l : ℝ) * t < l * b := mul_lt_mul_of_pos_left htb hl
        _ ≤ 1 := hlb
    · rw [← hl, zero_mul]
      norm_num
  have hdata := kltIsolationMinimizerData_of_minimal_sncWeightProfile_shift cY
    (1 : Y.functionFieldˣ) 1 le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) hklt
    (projectiveHyperplaneCartier e g hg hggen) A φ hlA x j hj1 hN (fun i => B i) ht hdt hp hmin hlt
    hpc
  exact kltIsolationMinimizerData_of_kltIsolationMinimizerData cY _ 1 _ _ x hdata m₀ hm₀

end Hyperplane

end MixedFujita
