/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightLemmaTwo
public import MixedFujita.ProjectiveSubspaceBound

/-!
The uniform bounds of section 3.1 of the manuscript for the weights of simple normal crossing
models, for the hyperplane class J of a smooth closed subvariety Y of projective space with zero
boundary (step 11): the bound (8) in its final form, the lower bound κ ≤ f and the upper end a^* of
the discrepancy interval (10).

Fix b > 0. With c the constant of Lemma 1, θ = min(1, 1/(2 c b)) and q = ⌊θ j⌋, the section
σ₀ = X_k^(j − q) of (j − q) J does not vanish at a point x with X_k(x) ≠ 0, the bound of
`cartierIsAmpleProj_weightExponentialObjective_ge` has c q/j ≤ 1/(2 b) ≤ 1/(2 t) for t ≤ b, and
h⁰(q J)/h⁰(j J) → θ^d by the leading Hilbert coefficient. Hence there is κ ∈ (0, 1) such that for all
large j, every point x, every basis of the sections of j J, every simple normal crossing model of
Y and of the zero divisors of the basis, every t ∈ (0, b] and every weight w ≥ 0 over the fibre of
x,

  F(w) ≥ κ N exp(A(w)/(2 t)),   N = h⁰(j J).

Consequences: F(w) ≥ κ N for every such weight (so the infimum of the normalized objective is at
least κ), and F(w) ≤ N (1 − δ) with δ ≥ 0 forces A(w) ≤ 2 b log(1/κ). The constants do not depend
on the degree, the point, the basis, the model, t or the weight.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Analysis

/-- From the bound (8), the objective is at least κ N. -/
theorem weight_objective_ge_of_exp_bound {κ Nr A t F : ℝ} (hκ : 0 ≤ κ) (hN : 0 ≤ Nr)
    (hA : 0 ≤ A) (ht : 0 < t) (h : κ * Nr * Real.exp (A / (2 * t)) ≤ F) : κ * Nr ≤ F := by
  have h1 : (1 : ℝ) ≤ Real.exp (A / (2 * t)) := Real.one_le_exp (div_nonneg hA (by positivity))
  calc κ * Nr = κ * Nr * 1 := (mul_one _).symm
    _ ≤ κ * Nr * Real.exp (A / (2 * t)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hκ hN)
    _ ≤ F := h

/-- From the bound (8), the upper end of the discrepancy interval: an objective at most N (1 − δ)
with δ ≥ 0 forces A ≤ 2 b log(1/κ) for t ≤ b. -/
theorem weight_logDiscrepancy_le_of_exp_bound {κ Nr A t b F δ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hN : 0 < Nr) (ht : 0 < t) (htb : t ≤ b) (hδ : 0 ≤ δ)
    (h : κ * Nr * Real.exp (A / (2 * t)) ≤ F) (hF : F ≤ Nr * (1 - δ)) :
    A ≤ 2 * b * Real.log (1 / κ) := by
  have h1 : κ * Real.exp (A / (2 * t)) ≤ 1 - δ := by
    have h2 : Nr * (κ * Real.exp (A / (2 * t))) ≤ Nr * (1 - δ) := by
      calc Nr * (κ * Real.exp (A / (2 * t))) = κ * Nr * Real.exp (A / (2 * t)) := by ring
        _ ≤ Nr * (1 - δ) := h.trans hF
    exact le_of_mul_le_mul_left h2 hN
  have h3 : Real.exp (A / (2 * t)) ≤ 1 / κ := by
    rw [le_div_iff₀ hκ]
    calc Real.exp (A / (2 * t)) * κ = κ * Real.exp (A / (2 * t)) := mul_comm _ _
      _ ≤ 1 - δ := h1
      _ ≤ 1 := by linarith
  have h4 : A / (2 * t) ≤ Real.log (1 / κ) := by
    have h5 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h5
  have hlog : 0 < Real.log (1 / κ) := Real.log_pos (by rw [lt_div_iff₀ hκ]; linarith)
  have h6 : A ≤ 2 * t * Real.log (1 / κ) := by
    rw [div_le_iff₀ (by positivity)] at h4
    linarith
  calc A ≤ 2 * t * Real.log (1 / κ) := h6
    _ ≤ 2 * b * Real.log (1 / κ) := by
        apply mul_le_mul_of_nonneg_right _ hlog.le
        linarith

end Analysis

section Hyperplane

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [Y.Over (Spec (CommRingCat.of K))] [IsClosedImmersion e] in
/-- Every multiple of the hyperplane class has a section which does not vanish at a given point:
a power of a coordinate. -/
theorem projectiveHyperplane_exists_section_nonvanishing (x : Y) (a : ℕ) :
    ∃ σ₀ : Γ((a • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • projectiveHyperplaneCartier e g hg hggen) σ₀ := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hxk : x ∈ projectivePullbackCoordinateOpen e j.val := hk
  have hf := projectiveHyperplane_isLocalEquationAt e g hg hggen j x hxk
  refine ⟨projectiveFormSection e g hg hggen j a (X k ^ a) (isHomogeneous_X_pow k a), ?_⟩
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x _
      (cartierLocalEquation_pow _ x _ hf a),
    projectiveFormSection_localCoefficient e g hg hggen j j x hxk a (X k ^ a) _,
    projectivePullbackHomogeneousEquation_eq_affine, map_pow, projectiveDehomogenize_X_self,
    one_pow, map_one, map_one]
  exact isUnit_one

/-- The hyperplane class of a closed immersion into projective space is ample. -/
theorem projectiveHyperplaneCartier_isAmpleProj
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) :
    CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) :=
  ⟨1, le_rfl, n, e, inferInstance, he, g, hg, hggen, 1, by
    rw [one_nsmul, principalCartierDivisor_one, add_zero]⟩

end Hyperplane

section Interval

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]

/-- The log discrepancy of a prime divisor of a smooth birational model for the zero boundary,
written with the crepant boundary of the model, is nonnegative. -/
theorem smooth_zeroBoundary_logDiscrepancy_nonneg {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension m (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
    (cY : EtaleChart K Y m) (cX : EtaleChart K X m) (z : CodimensionOnePoint X) :
    (0 : ℝ) ≤ (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
      (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
        principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (z : X)) /
      ((1 : ℕ) : ℝ) := by
  have hB : cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
      etaleCharts_cover) (z : X) =
      -cartierCoefficient (birationalRelativeCanonicalDivisor m π hπ cY etaleCharts_cover cX
        etaleCharts_cover) (z : X) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg,
      logDiscrepancyDivisor_boundary_zero π hπ cY (1 : Y.functionFieldˣ) 1 cX, one_nsmul]
  obtain ⟨x, -, -, hK0, -⟩ := exists_closedPoint_cartierPullback_coefficient_le π hπ cY cX z
  have hK0' : (0 : ℝ) ≤ (cartierCoefficient (birationalRelativeCanonicalDivisor m π hπ cY
      etaleCharts_cover cX etaleCharts_cover) (z : X) : ℝ) := by exact_mod_cast hK0
  rw [hB]
  push_cast
  rw [div_one]
  linarith

variable (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The bound (8) for the weights in its final form: for b > 0 there is κ ∈ (0, 1) such that for
all large j, every point x, every basis of the sections of j J, every simple normal crossing model
of the smooth variety with zero boundary and of the zero divisors of the basis, every t ∈ (0, b]
and every weight w ≥ 0 over the fibre of x, F(w) ≥ κ N exp(A(w)/(2 t)). -/
theorem projectiveHyperplane_weightExponentialObjective_ge
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y,
      ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        [X.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension m (X ↘ Spec (CommRingCat.of K))]
        (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
        (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
        (cY : EtaleChart K Y m) (cX : EtaleChart K X m) {r : ℕ} (ξ : Fin r → X),
        Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K m ξ →
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            cX etaleCharts_cover) (z : X) = 0) →
        ∀ {N : ℕ} (B : Module.Basis (Fin N) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
            (j • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (z : X) = 0) →
        ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        ∀ {t : ℝ}, 0 < t → t ≤ b →
          κ * (N : ℝ) * Real.exp ((∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
                (1 • (smoothCanonicalDivisor cY +
                  principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover)
                (ξ k)) / ((1 : ℕ) : ℝ))) / (2 * t)) ≤
            weightExponentialObjective
              (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
                (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
                  principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover)
                (ξ k)) / ((1 : ℕ) : ℝ))
              (fun i k => (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
                (j • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (ξ k) : ℝ))
              t j w := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  obtain ⟨c, hc1, hc⟩ := cartierIsAmpleProj_weightExponentialObjective_ge (K := K) (n := m) hn hd
    (projectiveHyperplaneCartier_isAmpleProj e g hg hggen he)
  obtain ⟨r₀, hr₀, hfin, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
  set θ : ℝ := min 1 (1 / (2 * c * b)) with hθdef
  have hθ : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθc : θ ≤ 1 / (2 * c * b) := min_le_right _ _
  have hℓ : (0 : ℝ) < r₀ / d.factorial := by
    have : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
    positivity
  have hratio := tendsto_ratio_floor_of_tendsto_div_pow hℓ hlim hθ
  have hκ1 : θ ^ d / 2 < 1 := by
    have h1 : θ ^ d ≤ 1 := pow_le_one₀ hθ.le hθ1
    linarith
  refine ⟨θ ^ d / 2, by positivity, hκ1, ?_⟩
  have hev1 := hratio.eventually (lt_mem_nhds (half_lt_self (pow_pos hθ d)))
  have hev2 : ∀ᶠ j : ℕ in atTop, 1 ≤ ⌊θ * j⌋₊ :=
    (tendsto_nat_floor_mul_atTop θ hθ).eventually (eventually_ge_atTop 1)
  filter_upwards [hev1, hev2] with j h1 h2
  have hfloor : (⌊θ * (j : ℝ)⌋₊ : ℝ) ≤ θ * j := Nat.floor_le (by positivity)
  have hqj : ⌊θ * (j : ℝ)⌋₊ ≤ j := by
    have h : (⌊θ * (j : ℝ)⌋₊ : ℝ) ≤ j :=
      hfloor.trans (mul_le_of_le_one_left (Nat.cast_nonneg j) hθ1)
    exact_mod_cast h
  generalize ⌊θ * (j : ℝ)⌋₊ = q at h1 h2 hfloor hqj
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hqj
  intro x X _ _ _ _ π _ _ hπ cY cX r ξ hinj hξ hsnc hBsupp N B hGsupp w hw0 hwΦ t ht htb
  obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x a
  have hjpos : (0 : ℝ) < ((a + q : ℕ) : ℝ) := by
    have : 0 < a + q := by omega
    exact_mod_cast this
  have hmain := hc x a q h2 σ₀ hσ₀ X π hπ cY cX ξ hinj hξ hsnc hBsupp B hGsupp w hw0 hwΦ (t := t)
    hjpos
  set A : ℝ := ∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
      etaleCharts_cover) (ξ k)) / ((1 : ℕ) : ℝ)) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hw0 k) (smooth_zeroBoundary_logDiscrepancy_nonneg π hπ cY cX ⟨ξ k, hξ k⟩)
  -- the dimension of the sections is N
  have hNeq : Module.finrank K
      Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) = N := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  -- κ N ≤ h⁰(q J)
  have hrank : θ ^ d / 2 * (N : ℝ) ≤
      (Module.finrank K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
    rw [hNeq] at h1
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      rcases (Nat.cast_nonneg (α := ℝ) N).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1
        have : (0 : ℝ) < θ ^ d / 2 := by positivity
        linarith
    have h1' := (lt_div_iff₀ hNpos).mp h1
    linarith
  -- c q / j ≤ 1/(2 t)
  have hcq : ((c * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) ≤ 1 / (2 * t) := by
    have hbt : 1 / (2 * b) ≤ 1 / (2 * t) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    refine le_trans ?_ hbt
    rw [div_le_div_iff₀ hjpos (by positivity)]
    push_cast at hfloor ⊢
    have h3 : (q : ℝ) ≤ 1 / (2 * c * b) * ((a : ℝ) + q) :=
      hfloor.trans (mul_le_mul_of_nonneg_right hθc (by positivity))
    have h4 : (c : ℝ) * q * (2 * b) ≤ (a : ℝ) + q := by
      have h5 : (c : ℝ) * q * (2 * b) ≤ (c : ℝ) * (1 / (2 * c * b) * ((a : ℝ) + q)) * (2 * b) := by
        gcongr
      have h6 : (c : ℝ) * (1 / (2 * c * b) * ((a : ℝ) + q)) * (2 * b) = (a : ℝ) + q := by
        field_simp
      linarith
    linarith
  have hexp : Real.exp (A / (2 * t)) ≤
      Real.exp (A * (1 / t - ((c * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h7 : 1 / (2 * t) ≤ 1 / t - ((c * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ) := by
      have h8 : 1 / t - 1 / (2 * t) = 1 / (2 * t) := by
        field_simp
        ring
      linarith
    calc A / (2 * t) = A * (1 / (2 * t)) := by ring
      _ ≤ A * (1 / t - ((c * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h7 hA0
  calc θ ^ d / 2 * (N : ℝ) * Real.exp (A / (2 * t))
      ≤ (Module.finrank K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) *
          Real.exp (A * (1 / t - ((c * q : ℕ) : ℝ) / ((a + q : ℕ) : ℝ))) :=
        mul_le_mul hrank hexp (Real.exp_pos _).le (Nat.cast_nonneg _)
    _ ≤ _ := hmain

end Interval

end MixedFujita
