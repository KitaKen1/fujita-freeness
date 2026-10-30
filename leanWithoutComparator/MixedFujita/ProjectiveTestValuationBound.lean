/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricJacobianBound
public import MixedFujita.ProjectiveSubspaceBound

/-!
Lemma 1 and Lemma 2 of the manuscript for monomial test valuations, on a smooth projective variety
over an algebraically closed field of characteristic zero. A test valuation is a morphism
ρ : T' → Y over the base field, a point p of T' over a closed point of Y, completion coordinates at
ρ(p) and at p with the same number of variables, and natural weights w; its log discrepancy over
Y is A(v) = Σ w + v(det J) for the Jacobian J of the completed stalk map. Lemma 1: one constant c
gives v(ρ^* s) ≤ A(v) c j for every nonzero section s of j J, or of j A with A ample, at every
closed centre. Lemma 2: for every ε > 0 there is κ > 0, independent of the closed point x, such
that for all large j some subspace of Γ(j J) of dimension at least κ h^0(j J) has ord_x(s) ≤ ⌊ε j⌋
and v(ρ^* s) ≤ A(v) ⌊ε j⌋ for every nonzero s in it and every test valuation over x; the factor
X_k^(j-q) used to build the subspace has a unit coefficient at x, so it does not change v. With
ε = 1/(2b) and t ≤ b this gives the bound v(s) ≤ j A(v)/(2t) of the manuscript.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Lemma 1 for test valuations and the multiples of an ample divisor. -/
theorem cartierIsAmpleProj_lemma1_testValuation {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {A : CartierDivisor Y}
    (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
      [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), IsClosed {ρ p} → ∀ {m : ℕ}
      (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
        (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (w : Fin m → ℕ) (j : ℕ), 1 ≤ j → ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
        cartierPullbackMonomialValuation (j • A) ρ p ep w s ≤
          (((∑ i, w i : ℕ) : ℕ∞) +
              (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w) *
            ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := cartierIsAmpleProj_vanishingOrder_le (K := K) hn hd hA
  refine ⟨c, fun T' _ ρ _ p hp m ez ep w j hj s hs => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) (ρ p)
  exact (cartierPullbackMonomialValuation_le (j • A) ρ p ez ep w hs).trans
    (mul_le_mul_right (hc (ρ p) hp j hj s hs) _)

variable (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- Lemma 1 for test valuations and the multiples of the hyperplane class. -/
theorem projectiveHyperplane_lemma1_testValuation
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ c : ℕ, ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
      [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), IsClosed {ρ p} → ∀ {m : ℕ}
      (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
        (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (w : Fin m → ℕ) (j : ℕ), 1 ≤ j →
        ∀ s : Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), s ≠ 0 →
          cartierPullbackMonomialValuation (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w s ≤
            (((∑ i, w i : ℕ) : ℕ∞) +
                (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w) *
              ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := projectiveHyperplane_cartierOrder_le e g hg hggen he hn hd
  refine ⟨c, fun T' _ ρ _ p hp m ez ep w j hj s hs => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) (ρ p)
  exact (cartierPullbackMonomialValuation_le _ ρ p ez ep w hs).trans
    (mul_le_mul_right (hc (ρ p) hp j hj s hs) _)

/-- The subspace of Lemma 2 also bounds every test valuation over x. -/
theorem projectiveHyperplane_subspace_valuation_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ a q : ℕ, 1 ≤ q →
      ∃ U : Submodule K Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        Module.finrank K U =
          Module.finrank K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ∧
        ∀ s ∈ U, s ≠ 0 →
          cartierSectionVanishingOrder ((a + q) • projectiveHyperplaneCartier e g hg hggen) x s ≤
              ((c * q : ℕ) : ℕ∞) ∧
            ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
              [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
              (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
                (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
                (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (w : Fin m → ℕ),
                cartierPullbackMonomialValuation ((a + q) • projectiveHyperplaneCartier e g hg hggen)
                    ρ p ep w s ≤
                  (((∑ i, w i : ℕ) : ℕ∞) +
                      (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w) *
                    ((c * q : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := projectiveHyperplane_cartierOrder_le e g hg hggen he hn hd
  refine ⟨c, fun x hx a q hq => ?_⟩
  set J := projectiveHyperplaneCartier e g hg hggen with hJ
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hxk : x ∈ projectivePullbackCoordinateOpen e j.val := hk
  let σ := projectiveFormSection e g hg hggen j a (X k ^ a) (isHomogeneous_X_pow k a)
  have hf := projectiveHyperplane_isLocalEquationAt e g hg hggen j x hxk
  set f := projectiveHyperplaneUnit e g hg hggen j with hfdef
  have hσunit : IsUnit (cartierLocalCoefficient (a • J) x (f ^ a)
      (cartierLocalEquation_pow J x f hf a) σ) := by
    rw [projectiveFormSection_localCoefficient e g hg hggen j j x hxk a (X k ^ a) _,
      projectivePullbackHomogeneousEquation_eq_affine, map_pow, projectiveDehomogenize_X_self,
      one_pow, map_one, map_one]
    exact isUnit_one
  have hσ0 : σ ≠ 0 :=
    (cartierLocalCoefficient_ne_zero_iff _ x _ (cartierLocalEquation_pow J x f hf a) σ).mp
      hσunit.ne_zero
  obtain ⟨u, hu⟩ := hσunit
  refine ⟨LinearMap.range (cartierNsmulProductLinear (K := K) J a q σ),
    LinearMap.finrank_range_of_inj (cartierNsmulProduct_injective J a q σ hσ0), ?_⟩
  rintro _ ⟨t, rfl⟩ hs
  have ht : t ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  have hcoef : cartierLocalCoefficient ((a + q) • J) x (f ^ (a + q))
      (cartierLocalEquation_pow J x f hf (a + q)) (cartierNsmulProductLinear (K := K) J a q σ t) =
        (u : Y.presheaf.stalk x) *
          cartierLocalCoefficient (q • J) x (f ^ q) (cartierLocalEquation_pow J x f hf q) t := by
    rw [cartierNsmulProductLinear_apply, cartierNsmulProduct_localCoefficient J a q x f hf σ t, hu]
  refine ⟨?_, ?_⟩
  · rw [cartierSectionVanishingOrder_eq_localCoefficient _ x (f ^ (a + q))
      (cartierLocalEquation_pow J x f hf (a + q)), hcoef, localAdicOrder_unit_mul,
      ← cartierSectionVanishingOrder_eq_localCoefficient]
    exact hc x hx q hq t ht
  · intro T' _ ρ _ p hpx m ez ep w
    subst hpx
    have := smoothScheme_stalk_isNoetherianRing (K := K) (ρ p)
    have hval : cartierPullbackMonomialValuation ((a + q) • J) ρ p ep w
        (cartierNsmulProductLinear (K := K) J a q σ t) =
          cartierPullbackMonomialValuation (q • J) ρ p ep w t := by
      rw [cartierPullbackMonomialValuation_eq _ ρ p ep w _ (f ^ (a + q))
          (cartierLocalEquation_pow J (ρ p) f hf (a + q)),
        cartierPullbackMonomialValuation_eq _ ρ p ep w t (f ^ q)
          (cartierLocalEquation_pow J (ρ p) f hf q),
        cartierStalkPullbackCoefficient_apply, cartierStalkPullbackCoefficient_apply, hcoef,
        map_mul, map_mul, map_mul, MvPowerSeries.weightedOrder_mul,
        weightedOrder_eq_zero_of_isUnit w (((u.isUnit.map _).map _).map _), zero_add]
    rw [hval]
    exact (cartierPullbackMonomialValuation_le (q • J) ρ p ez ep w ht).trans
      (mul_le_mul_right (hc (ρ p) hx q hq t ht) _)

/-- Lemma 2 for test valuations: for every ε > 0 there is κ > 0, independent of the closed point
x, such that for all large j a subspace of Γ(j·J) of dimension at least κ h^0(j·J) has
ord_x ≤ ⌊ε j⌋ and v ≤ A(v) ⌊ε j⌋ for every test valuation over x on all its nonzero
elements. -/
theorem projectiveHyperplane_lemma2_testValuation
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ x : Y, IsClosed {x} → ∀ᶠ j : ℕ in atTop,
      ∃ U : Submodule K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        κ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤
          Module.finrank K U ∧
        ∀ s ∈ U, s ≠ 0 →
          cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x s ≤
              (⌊ε * j⌋₊ : ℕ∞) ∧
            ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
              [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
              (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
                (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
                (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (w : Fin m → ℕ),
                cartierPullbackMonomialValuation (j • projectiveHyperplaneCartier e g hg hggen)
                    ρ p ep w s ≤
                  (((∑ i, w i : ℕ) : ℕ∞) +
                      (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w) *
                    (⌊ε * j⌋₊ : ℕ∞) := by
  intro ε hε
  obtain ⟨c, hc⟩ := projectiveHyperplane_subspace_valuation_le e g hg hggen he hn hd
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  set θ : ℝ := min 1 (ε / ((c : ℝ) + 1)) with hθdef
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hθ : 0 < θ := lt_min one_pos (div_pos hε hc1)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθc : ((c : ℝ) + 1) * θ ≤ ε := by
    have h := min_le_right 1 (ε / ((c : ℝ) + 1))
    rw [← hθdef] at h
    calc ((c : ℝ) + 1) * θ ≤ ((c : ℝ) + 1) * (ε / ((c : ℝ) + 1)) := by gcongr
      _ = ε := by field_simp
  have hℓ : (0 : ℝ) < r / d.factorial := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hratio := tendsto_ratio_floor_of_tendsto_div_pow hℓ hlim hθ
  refine ⟨θ ^ d / 2, by positivity, fun x hx => ?_⟩
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
  obtain ⟨U, hU, hUval⟩ := hc x hx a q h2
  have h3 : ((c * q : ℕ) : ℝ) ≤ ε * ((a + q : ℕ) : ℝ) := by
    push_cast at hfloor ⊢
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have haq : (0 : ℝ) ≤ (a : ℝ) + q := by positivity
    calc (c : ℝ) * q ≤ ((c : ℝ) + 1) * q := by nlinarith
      _ ≤ ((c : ℝ) + 1) * (θ * ((a : ℝ) + q)) := by gcongr
      _ = (((c : ℝ) + 1) * θ) * ((a : ℝ) + q) := by ring
      _ ≤ ε * ((a : ℝ) + q) := by gcongr
  have h4 : ((c * q : ℕ) : ℕ∞) ≤ (⌊ε * ((a + q : ℕ) : ℝ)⌋₊ : ℕ∞) := by
    exact_mod_cast Nat.le_floor h3
  refine ⟨U, ?_, ?_⟩
  · rw [hU]
    have hNpos : (0 : ℝ) < (Module.finrank K
        Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
      rcases (Nat.cast_nonneg (α := ℝ) (Module.finrank K
        Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1
        have : (0 : ℝ) < θ ^ d / 2 := by positivity
        linarith
    have h1' := (lt_div_iff₀ hNpos).mp h1
    linarith
  · intro s hs hs0
    obtain ⟨hord, hval⟩ := hUval s hs hs0
    refine ⟨hord.trans h4, fun T' _ ρ _ p hpx m ez ep w => ?_⟩
    exact (hval T' ρ p hpx ez ep w).trans (mul_le_mul_right h4 _)

end MixedFujita
