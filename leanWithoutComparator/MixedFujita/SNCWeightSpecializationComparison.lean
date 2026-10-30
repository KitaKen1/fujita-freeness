/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneMinimizerNumerical
public import MixedFujita.SpecializationComparison

/-!
The specialization comparison (6) of section 2.3 for the weights on simple normal crossing models,
from the closedness of the realization sets in the point (steps 9 and 11).

For a point y let Q(y) be the set of normalized profiles realized at y: the vectors q for which
some basis and some profile datum p at y have p₁ > 0 and q_i p₁ ≤ p₂,ᵢ for all i, that is,
v(s_i) ≥ q_i A(v). The profile data at y form a cone: scaling the weight scales the datum. On a
klt pair the log discrepancies of the members are positive, so a datum with p₁ = 0 is zero.

* If every rational point of Q(y) lies in Q(x), then the infimum of the objective at x is at most
  the infimum at y. A datum p at y with p₁ > 0 gives q = p₂/p₁ in Q(y). A rational q' slightly
  below q lies in Q(y), hence in Q(x) (the approximation step `specialization_approximation`),
  and the datum at x realizing q', rescaled to first coordinate p₁, has objective close to that
  of p. The datum zero is handled separately.
* If the realization sets R_α = {y | α ∈ Q(y)} of the rational vectors α are closed, the
  countably many R_α not containing w are closed sets not containing w. Outside them, a rational
  vector realized at y is realized at w, hence at every specialization x of w, so (6) holds there:
  this is the form of (6) at very general points used by section 5.
* For the hyperplane class with zero boundary, the data of the minimizer exist at x for every
  m₀ ≥ 1 from the numerical hypothesis for J, the closedness of the realization sets in the
  tuple (Lemma 3 at x) and in the point (the sets R_α), and the interior condition (7).

The closedness of the sets R_α is the content of section 2.2 of the manuscript (the threshold of
the ideal of α is semicontinuous and the flag variety is proper); it is a hypothesis here.
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

section Profiles

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The normalized profiles realized at y by the bases of N sections of D: the vectors q for which
some basis and some profile datum p at y have p₁ > 0 and q_i p₁ ≤ p₂,ᵢ for all i. -/
def sncWeightNormalizedProfiles (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (N : ℕ) (y : Y) : Set (Fin N → ℝ) :=
  {q | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤), ∃ p ∈ sncWeightProfiles cY fY d D₀ D y B,
    0 < p.1 ∧ ∀ i, q i * p.1 ≤ p.2 i}

/-- The normalized profiles are downward closed. -/
theorem sncWeightNormalizedProfiles_down (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor Y) (N : ℕ) (y : Y) :
    ∀ q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y, ∀ q', q' ≤ q →
      q' ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  rintro q ⟨B, p, hp, hp1, hq⟩ q' hq'
  exact ⟨B, p, hp, hp1, fun i => (mul_le_mul_of_nonneg_right (hq' i) hp1.le).trans (hq i)⟩

/-- Scaling the weight scales the profile datum. -/
theorem sncWeightProfiles_scale (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D y s) {c : ℝ} (hc : 0 < c) :
    (c * p.1, fun i => c * p.2 i) ∈ sncWeightProfiles cY fY d D₀ D y s := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y', hy', hy'w⟩, hA, hv⟩ := hp
  refine ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, fun k => c * w k, hinj,
    hξ, hsnc, hBsupp, hGsupp, fun k => mul_nonneg hc.le (hw0 k),
    ⟨y', hy', fun k hk => hy'w k fun h => hk (by simp only [h, mul_zero])⟩, ?_, fun i => ?_⟩
  · change c * p.1 = _
    rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · change c * p.2 i = _
    rw [hv i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The zero datum is realized wherever some datum is. -/
theorem sncWeightProfiles_zero (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D y s) :
    ((0 : ℝ), fun _ => (0 : ℝ)) ∈ sncWeightProfiles cY fY d D₀ D y s := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y', hy', -⟩, -, -⟩ := hp
  refine ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, fun _ => 0, hinj, hξ, hsnc,
    hBsupp, hGsupp, fun _ => le_rfl, ⟨y', hy', fun k hk => absurd rfl hk⟩, ?_, fun i => ?_⟩
  · change (0 : ℝ) = _
    simp
  · change (0 : ℝ) = _
    simp

/-- On a klt pair the first coordinate of a profile datum is not negative, and a datum with first
coordinate zero is zero. -/
theorem sncWeightProfiles_fst_nonneg (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ D : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (y : Y) {N : ℕ}
    (s : Fin N → Γ(D.sheaf, ⊤)) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ sncWeightProfiles cY fY d D₀ D y s) :
    0 ≤ p.1 ∧ (p.1 = 0 → ∀ i, p.2 i = 0) := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, -, hA, hv⟩ := hp
  have hApos : ∀ k, 0 < ((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d := by
    intro k
    have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
    have h2 : ((cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k) : ℤ) : ℝ) <
        (d : ℝ) := by exact_mod_cast h1
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    exact div_pos (by linarith) hd'
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) :=
    fun k _ => mul_nonneg (hw0 k) (hApos k).le
  refine ⟨by rw [hA]; exact Finset.sum_nonneg hterm, fun h0 i => ?_⟩
  rw [hA] at h0
  have hw : ∀ k, w k = 0 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0 k (Finset.mem_univ k)
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (hApos k).ne'
  rw [hv i]
  exact Finset.sum_eq_zero fun k _ => by rw [hw k, zero_mul]

/-- The specialization comparison from the transfer of rational profiles: if every rational
normalized profile realized at y is realized at x, the infimum at x is at most the infimum at y. -/
theorem sncWeightInfimum_le_of_rational (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ D : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) {N : ℕ}
    (hN : 0 < N) {j : ℕ} (hj : 0 < j) (t : ℝ) {x y : Y}
    (hrat : ∀ α : Fin N → ℚ,
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y →
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N x)
    (hne : (sncWeightObjectiveValues cY fY d D₀ D y N t j).Nonempty) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤ sncWeightInfimum cY fY d D₀ D y N t j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  apply le_csInf hne
  rintro val ⟨B, p, hp, rfl⟩
  obtain ⟨hp1, hp0⟩ := sncWeightProfiles_fst_nonneg cY fY hd D₀ D hklt y B hp
  rcases hp1.lt_or_eq with hp1 | hp1
  · -- a datum with positive first coordinate: approximation by rational profiles
    apply le_of_forall_pos_le_add
    intro ε hε
    have hq : (fun i => p.2 i / p.1) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y :=
      ⟨B, p, hp, hp1, fun i => by rw [div_mul_cancel₀ _ hp1.ne']⟩
    obtain ⟨q', hq', hle⟩ := specialization_approximation hj t
      (sncWeightNormalizedProfiles cY fY d D₀ D N y) (sncWeightNormalizedProfiles cY fY d D₀ D N x)
      (sncWeightNormalizedProfiles_down cY fY d D₀ D N y) hrat hp1 hq (div_pos hε hNr)
    obtain ⟨B', p', hp', hp'1, hq'p'⟩ := hq'
    have hc : 0 < p.1 / p'.1 := div_pos hp1 hp'1
    have h1 := sncWeightInfimum_le cY fY d D₀ D x t j B' (sncWeightProfiles_scale cY fY d D₀ D x
      B' hp' hc)
    -- the rescaled datum has values at least p₁ q'
    have h2 : (∑ i, Real.exp (p.1 / p'.1 * p'.1 / t - p.1 / p'.1 * p'.2 i / j)) ≤
        ∑ i, Real.exp (p.1 / t - p.1 * q' i / j) := by
      refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
      rw [div_mul_cancel₀ _ hp'1.ne']
      have h3 : p.1 * q' i ≤ p.1 / p'.1 * p'.2 i := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hp'1]
        have := mul_le_mul_of_nonneg_left (hq'p' i) hp1.le
        linarith
      have h4 : p.1 * q' i / j ≤ p.1 / p'.1 * p'.2 i / j := div_le_div_of_nonneg_right h3 hjr.le
      linarith
    have h5 : (∑ i, Real.exp (p.1 / t - p.1 * q' i / j)) =
        N * minimizationFunctional j t p.1 (fun i => p.1 * q' i) := by
      unfold minimizationFunctional
      field_simp
    have h6 : N * minimizationFunctional j t p.1 (fun i => p.1 * (p.2 i / p.1)) =
        ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
      unfold minimizationFunctional
      have : ∀ i, p.1 * (p.2 i / p.1) = p.2 i := fun i => by field_simp
      simp only [this]
      field_simp
    calc sncWeightInfimum cY fY d D₀ D x N t j
        ≤ ∑ i, Real.exp ((p.1 / p'.1 * p'.1) / t - (p.1 / p'.1 * p'.2 i) / j) := h1
      _ ≤ ∑ i, Real.exp (p.1 / t - p.1 * q' i / j) := h2
      _ = N * minimizationFunctional j t p.1 (fun i => p.1 * q' i) := h5
      _ ≤ N * (minimizationFunctional j t p.1 (fun i => p.1 * (p.2 i / p.1)) + ε / N) :=
        mul_le_mul_of_nonneg_left hle hNr.le
      _ = ∑ i, Real.exp (p.1 / t - p.2 i / j) + ε := by
        rw [mul_add, h6, mul_div_cancel₀ _ hNr.ne']
  · -- the zero datum: the infimum at x is at most N
    have hp2 := hp0 hp1.symm
    have hval : (∑ i, Real.exp (p.1 / t - p.2 i / j)) = ∑ _i : Fin N, Real.exp 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hp1, hp2 i, zero_div, zero_div, sub_zero]
    rw [hval]
    by_cases hxne : (sncWeightObjectiveValues cY fY d D₀ D x N t j).Nonempty
    · obtain ⟨_, B₀, p₀, hp₀, -⟩ := hxne
      have h0 := sncWeightInfimum_le cY fY d D₀ D x t j B₀
        (sncWeightProfiles_zero cY fY d D₀ D x B₀ hp₀)
      refine h0.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      simp
    · rw [Set.not_nonempty_iff_eq_empty] at hxne
      unfold sncWeightInfimum
      rw [hxne, Real.sInf_empty]
      exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

/-- The specialization comparison (6) at very general points from the closedness of the
realization sets in the point: for w specializing to x there are countably many closed sets not
containing w outside which the infimum at x is at most the infimum at every point with a profile
datum. -/
theorem sncWeight_specialization_comparison_of_closed (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ D : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : 0 < j) (t : ℝ)
    (hcl : ∀ α : Fin N → ℚ, IsClosed {y : Y |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y})
    {w x : Y} (hwx : w ⤳ x) :
    ∃ Z : ℕ → Set Y, (∀ i, IsClosed (Z i)) ∧ (∀ i, w ∉ Z i) ∧
      ∀ y : Y, (sncWeightObjectiveValues cY fY d D₀ D y N t j).Nonempty → (∀ i, y ∉ Z i) →
        sncWeightInfimum cY fY d D₀ D x N t j ≤ sncWeightInfimum cY fY d D₀ D y N t j := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (Fin N → ℚ)
  set R : (Fin N → ℚ) → Set Y := fun α =>
    {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} with hR
  refine ⟨fun k => if w ∈ R (f k) then ∅ else R (f k), fun k => ?_, fun k => ?_,
    fun y hne hyZ => ?_⟩
  · dsimp only
    split_ifs
    · exact isClosed_empty
    · exact hcl (f k)
  · dsimp only
    split_ifs with h
    · exact Set.notMem_empty w
    · exact h
  · refine sncWeightInfimum_le_of_rational cY fY hd D₀ D hklt hN hj t (fun α hα => ?_) hne
    obtain ⟨k, rfl⟩ := hf α
    have hw : w ∈ R (f k) := by
      by_contra hw
      apply hyZ k
      dsimp only
      simp only [hw, ↓reduceIte]
      exact hα
    exact hwx.mem_closed (hcl (f k)) hw

end Profiles

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer at x for the hyperplane class with zero boundary, for every m₀ ≥ 1,
from the numerical hypothesis for J, the closedness of the realization sets in the tuple and in
the point, and the interior condition (7), at all large degrees. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_of_realizationClosed
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal) {t₀ δ : ℝ} (ht₀ : t₀ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen)
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) y})
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < 1 →
      ∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (projectiveHyperplaneCartier e g hg hggen) m₀ x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  -- the spaces of sections are not zero
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  refine projectiveHyperplane_kltIsolationMinimizerData_of_restrictedGrowth e g hg hggen he hm cY
    x hxc hgx ht₀ hδ hδ1 hgrow hclosed hstart ?_ m₀ hm₀
  filter_upwards [hclosedPt, eventually_ge_atTop 1] with j hj hj1
  intro t _ _ w hwx _
  obtain ⟨Z, hZ, hwZ, hZ6⟩ := sncWeight_specialization_comparison_of_closed cY
    (1 : Y.functionFieldˣ) le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
    (j • projectiveHyperplaneCartier e g hg hggen) hklt (hNpos j) hj1 t hj hwx
  refine ⟨Z, hZ, hwZ, fun y hyc hyZ _ => hZ6 y ?_ hyZ⟩
  -- a profile datum at the closed point y
  have := hfin j
  obtain ⟨p, hp, -⟩ := exists_sncWeightProfile_le_of_smooth_point hm cY
    (j • projectiveHyperplaneCartier e g hg hggen)
    (fun i => Module.finBasis K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) i)
    (fun i => (Module.finBasis K _).ne_zero i) y hyc one_pos (j := (j : ℝ)) (by positivity)
    (le_refl (0 : ℝ))
  exact ⟨_, Module.finBasis K _, p, hp, rfl⟩

end Hyperplane

end MixedFujita
