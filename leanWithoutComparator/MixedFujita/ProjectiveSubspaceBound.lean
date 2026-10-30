/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHilbertAsymptotics
public import MixedFujita.ProjectiveSectionOrderBound

/-!
Lemma 2 of the manuscript in multiplicity form. On an actual smooth integral closed subscheme of
polynomial projective space over an algebraically closed field, fix ε > 0. There is κ > 0 such
that for every closed point x and all large j some subspace U ⊆ Γ(j·J) has dim U ≥ κ dim Γ(j·J)
and every nonzero s ∈ U has ord_x(s) ≤ ⌊ε j⌋. Take q = ⌊θ j⌋ with θ = min(1, ε/(c+1)), where c is
the uniform order constant, and U = σ · Γ(q·J) for the section σ = X_k^(j-q) of (j-q)·J, which
does not vanish at x when X_k(x) ≠ 0. Multiplication by σ is injective and keeps the order, and
h^0(q J)/h^0(j J) → θ^d by the leading Hilbert coefficient. The constant κ does not depend on x.
The bound for test valuations v(s) ≤ A(v) ord_x(s) is the Jacobian inequality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- If h(D)/D^d → ℓ > 0, then h(⌊θ j⌋)/h(j) → θ^d. -/
theorem tendsto_ratio_floor_of_tendsto_div_pow {d : ℕ} {h : ℕ → ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun D : ℕ => (h D : ℝ) / (D : ℝ) ^ d) atTop (nhds ℓ)) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun j : ℕ => (h ⌊θ * j⌋₊ : ℝ) / (h j : ℝ)) atTop (nhds (θ ^ d)) := by
  have hq : Tendsto (fun j : ℕ => ⌊θ * j⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop θ hθ
  have h1 := hlim.comp hq
  have h2 : Tendsto (fun j : ℕ => (⌊θ * (j : ℝ)⌋₊ : ℝ) / (j : ℝ)) atTop (nhds θ) :=
    (tendsto_nat_floor_mul_div_atTop hθ.le).comp tendsto_natCast_atTop_atTop
  have h3 := hlim.inv₀ hℓ.ne'
  have hprod := (h1.mul (h2.pow d)).mul h3
  have hlimit : ℓ * θ ^ d * ℓ⁻¹ = θ ^ d := by field_simp
  rw [hlimit] at hprod
  refine hprod.congr' ?_
  have hpos : ∀ᶠ j : ℕ in atTop, ℓ / 2 < (h j : ℝ) / (j : ℝ) ^ d :=
    hlim.eventually (lt_mem_nhds (half_lt_self hℓ))
  filter_upwards [hpos, hq.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with
    j hj hqj hj1
  have hhj : (h j : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hj
    linarith
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hq0 : ((⌊θ * (j : ℝ)⌋₊ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show ⌊θ * (j : ℝ)⌋₊ ≠ 0 by omega)
  simp only [Function.comp, div_pow]
  field_simp

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Multiplying Γ(q·J) by a section of a·J nonvanishing at x gives a copy of Γ(q·J) in
Γ((a+q)·J) with ord_x ≤ c q. -/
theorem projectiveHyperplane_subspace_order_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ a q : ℕ, 1 ≤ q →
      ∃ U : Submodule K Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        Module.finrank K U =
          Module.finrank K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ∧
        ∀ s ∈ U, s ≠ 0 →
          cartierSectionVanishingOrder ((a + q) • projectiveHyperplaneCartier e g hg hggen) x s ≤
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
  refine ⟨LinearMap.range (cartierNsmulProductLinear (K := K) J a q σ), ?_, ?_⟩
  · exact LinearMap.finrank_range_of_inj (cartierNsmulProduct_injective J a q σ hσ0)
  · rintro _ ⟨t, rfl⟩ hs
    have ht : t ≠ 0 := by
      rintro rfl
      exact hs (map_zero _)
    rw [cartierNsmulProductLinear_apply,
      cartierSectionVanishingOrder_eq_localCoefficient _ x (f ^ (a + q))
        (cartierLocalEquation_pow J x f hf (a + q)),
      cartierNsmulProduct_localCoefficient J a q x f hf σ t]
    obtain ⟨u, hu⟩ := hσunit
    rw [← hu, localAdicOrder_unit_mul, ← cartierSectionVanishingOrder_eq_localCoefficient]
    exact hc x hx q hq t ht

/-- Lemma 2 in multiplicity form: for every ε > 0 there is κ > 0, independent of the closed
point x, such that for all large j a subspace of Γ(j·J) of dimension at least κ h^0(j·J) has
ord_x ≤ ⌊ε j⌋ on all its nonzero elements. -/
theorem projectiveHyperplane_lemma2_multiplicity
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ x : Y, IsClosed {x} → ∀ᶠ j : ℕ in atTop,
      ∃ U : Submodule K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        κ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤
          Module.finrank K U ∧
        ∀ s ∈ U, s ≠ 0 →
          cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x s ≤
            (⌊ε * j⌋₊ : ℕ∞) := by
  intro ε hε
  obtain ⟨c, hc⟩ := projectiveHyperplane_subspace_order_le e g hg hggen he hn hd
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
  obtain ⟨U, hU, hUord⟩ := hc x hx a q h2
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
    refine (hUord s hs hs0).trans ?_
    have h3 : ((c * q : ℕ) : ℝ) ≤ ε * ((a + q : ℕ) : ℝ) := by
      push_cast at hfloor ⊢
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      have haq : (0 : ℝ) ≤ (a : ℝ) + q := by positivity
      calc (c : ℝ) * q ≤ ((c : ℝ) + 1) * q := by nlinarith
        _ ≤ ((c : ℝ) + 1) * (θ * ((a : ℝ) + q)) := by gcongr
        _ = (((c : ℝ) + 1) * θ) * ((a : ℝ) + q) := by ring
        _ ≤ ε * ((a : ℝ) + q) := by gcongr
    exact_mod_cast Nat.le_floor h3

end MixedFujita
