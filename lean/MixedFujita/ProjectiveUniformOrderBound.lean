/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneSections
public import MixedFujita.ProjectiveJetSurjectivity
public import MixedFujita.CartierGradedSections
public import MixedFujita.CompletionJetApproximation
public import MixedFujita.GeometricSmoothTaylor
public import MixedFujita.SmoothSchemeCoordinates

/-!
A Bertini-free uniform vanishing-order bound for the hyperplane class of an
actual smooth integral closed subscheme of projective space over an
algebraically closed field. Two-sided Hilbert bounds for the actual section
spaces of D·J give one constant c, independent of the point, such that every
nonzero actual section of D·J with D ≥ 1 vanishes to order at most c D at every
closed point. Jets at the point are realized by actual pulled-back forms,
completion coordinates turn them into coefficient-box jets, and the dimension
comparison of JetHilbertBound concludes. No Bertini flag, curve, intersection
number or ambient cohomology window is used. The Hilbert bounds and finite
dimensionality of the section spaces are explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Uniform linear vanishing-order bound from two-sided Hilbert bounds. For the
hyperplane divisor J of an actual smooth integral closed subscheme of dimension d,
every nonzero actual section of D·J (D ≥ 1) has order at most ⌈c⌉₊ D at every closed
point, with c = jetHilbertConstant d a C (d^d) independent of the point. -/
theorem projectiveHyperplane_cartierOrder_le_of_hilbert
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    [∀ D : ℕ, FiniteDimensional K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hH : ∀ D : ℕ, |(Module.finrank K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) - a * (D : ℝ) ^ d| ≤
      C * ((D : ℝ) + 1) ^ (d - 1))
    (x : Y) (hx : IsClosed {x}) {D : ℕ} (hD : 1 ≤ D)
    (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionVanishingOrder (D • projectiveHyperplaneCartier e g hg hggen) x s ≤
      ((⌈jetHilbertConstant d a C ((d : ℝ) ^ d)⌉₊ * D : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hJx := projectiveHyperplane_isLocalEquationAt e g hg hggen j x hk
  let := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨_, _, coords, _, _⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d hn
    (projectiveHyperplaneCartier e g hg hggen) x hx
  let J := projectiveHyperplaneCartier e g hg hggen
  let u := projectiveHyperplaneUnit e g hg hggen j
  let T : ∀ D' : ℕ, Γ((D' • J).sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin d) K := fun D' =>
    cartierTaylorCoordinates (D' • J) x (u ^ D') (cartierLocalEquation_pow J x u hJx D') coords
  have hTorder : ∀ D' (t : Γ((D' • J).sheaf, ⊤)),
      (T D' t).order = cartierSectionVanishingOrder (D' • J) x t := fun D' t =>
    cartierTaylorCoordinates_order_eq_vanishingOrder (D' • J) x (u ^ D')
      (cartierLocalEquation_pow J x u hJx D') coords t
  refine gradedSection_order_le_of_jets_hilbert (K := K)
    (fun D' => Γ((D' • J).sheaf, ⊤))
    (fun j' k' t => cartierNsmulProductLinear (K := K) J j' k' t)
    (fun j' k' t ht => cartierNsmulProduct_injective J j' k' t ht)
    (fun m => (Fin d → Fin ((m - 1) / d + 1)) → K)
    (fun D' m => (powerSeriesBoxJet d ((m - 1) / d)).comp (T D'))
    ?_ (fun D' t => cartierSectionVanishingOrder (D' • J) x t) ?_ hd (b := (d : ℝ) ^ d)
    (by positivity) ?_ ha hC hH hD s hs
  · -- Every box jet is realized by an actual section of D'·J when m ≤ D' + 1.
    intro D' m hm hmD v
    obtain ⟨y, hy⟩ := completionCoordinates_exists_approx coords.toRingEquiv
      (powerSeriesOfBox d ((m - 1) / d) v) m
    obtain ⟨F, hF, hFy⟩ := polynomialProjective_closedImmersion_jet_realized e k x hk hx
      (m := m - 1) (D := D') (by omega) y
    refine ⟨projectiveFormSection e g hg hggen j D' F hF, ?_⟩
    change powerSeriesBoxJet d ((m - 1) / d) (T D' (projectiveFormSection e g hg hggen j D' F hF)) = v
    rw [← powerSeriesBoxJet_ofBox d ((m - 1) / d) v]
    apply powerSeriesBoxJet_eq_of_le_order_sub d m hm
    have hT : T D' (projectiveFormSection e g hg hggen j D' F hF) =
        coords (algebraMap (Y.presheaf.stalk x)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x))
          (Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D' F hF))) := by
      change cartierTaylorCoordinates (D' • J) x (u ^ D')
        (cartierLocalEquation_pow J x u hJx D') coords
          (projectiveFormSection e g hg hggen j D' F hF) = _
      rw [cartierTaylorCoordinates_apply,
        projectiveFormSection_localCoefficient e g hg hggen j j x hk D' F hF]
    rw [hT]
    have hmem : Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D' F hF) - y ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ m := by
      have h' := neg_mem hFy
      rw [neg_sub, Nat.sub_add_cancel hm] at h'
      exact h'
    have h1 := completionCoordinates_order_ge_of_mem_pow coords.toRingEquiv hmem
    rw [map_sub, map_sub] at h1
    have h2 : (m : ℕ∞) ≤ (coords.toRingEquiv (algebraMap (Y.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x)) y) -
          powerSeriesOfBox d ((m - 1) / d) v).order := by
      rw [← MvPowerSeries.order_neg, neg_sub]
      exact hy
    have h3 := (le_min h1 h2).trans MvPowerSeries.min_order_le_add
    rw [sub_add_sub_cancel] at h3
    exact h3
  · -- Box jets kill products with a section of order at least m.
    intro j' k' m t₁ t₂ hm hord
    change powerSeriesBoxJet d ((m - 1) / d) (T (j' + k') (cartierNsmulProduct J j' k' t₁ t₂)) = 0
    apply powerSeriesBoxJet_eq_zero_of_le_order d m hm
    have hprod : T (j' + k') (cartierNsmulProduct J j' k' t₁ t₂) = T j' t₁ * T k' t₂ :=
      cartierTaylorCoordinates_nsmulProduct J j' k' x u hJx coords t₁ t₂
    rw [hprod]
    calc (m : ℕ∞) ≤ (T j' t₁).order := by rw [hTorder]; exact hord
      _ ≤ (T j' t₁).order + (T k' t₂).order := le_self_add
      _ ≤ _ := MvPowerSeries.le_order_mul
  · -- The box of side (m-1)/d + 1 has at least m^d / d^d points.
    intro m hm
    have hcard : Module.finrank K ((Fin d → Fin ((m - 1) / d + 1)) → K) =
        ((m - 1) / d + 1) ^ d := by
      simp only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin]
    rw [hcard, Nat.cast_pow]
    exact pow_le_pow_mul_boxSide d m hd

end MixedFujita
