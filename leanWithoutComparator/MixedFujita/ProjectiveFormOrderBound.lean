/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.ProjectiveChartNullstellensatz
public import MixedFujita.ProjectiveLinearSystemExistence
public import MixedFujita.JetIncrementBound
public import MixedFujita.ProjectiveJetSurjectivity
public import MixedFujita.CompletionJetApproximation
public import MixedFujita.GeometricSmoothTaylor
public import MixedFujita.SmoothSchemeCoordinates

/-!
The uniform linear vanishing-order bound without Hilbert input, for sections given by
forms. Let Y be an actual smooth integral closed subscheme of dimension d ≥ 1 of
polynomial projective space over an algebraically closed field, embedded over the base
field, and J the hyperplane divisor of a degree-one form g avoiding the generic point.
There is one constant c such that, for every D ≥ 1, every nonzero actual section of D·J
given by a degree-D form vanishes to order at most c D at every closed point. The
Hilbert increment comes from a linear system of parameters through the chart
Nullstellensatz and the graded coordinate ring, and the jets come from the forms
themselves. No Hilbert polynomial, Bertini flag, curve or cohomology window is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Noetherian

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

/-- An actual closed subscheme of projective space of finite type over the base field is a
Noetherian space. -/
theorem polynomialProjective_closedImmersion_noetherianSpace
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) :
    NoetherianSpace Y := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  have := polynomialProjectiveToBase_isProper n K
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  have : AlgebraicGeometry.IsNoetherian Y := AlgebraicGeometry.IsNoetherian.mk
  infer_instance

end Noetherian

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The Hilbert increment of the form-section spaces, from a linear system of parameters. -/
theorem projectiveFormSectionSpace_finrank_increment
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ∃ C : ℕ, ∀ k j : ℕ,
      (Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he (k + j)) : ℝ) -
          Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he k) ≤
        (C : ℝ) * j * ((k : ℝ) + j + 1) ^ (d - 1) := by
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨y, -, hyh, hynz, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  have hdim : ∀ D, Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) =
      linearSystemQuotientDim ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y 0 D := by
    intro D
    rw [projectiveFormSectionSpace_finrank]
    unfold linearSystemQuotientDim
    rw [linearSystemFiltration_zero]
  refine ⟨linearSystemConstant (Fin n) K t, fun k j => ?_⟩
  rw [hdim, hdim]
  exact linearSystem_hilbert_increment hyh hynz hd ht k j

/-- One constant bounds the order of every nonzero section of D·J given by a degree-D form,
at every closed point and in every degree D ≥ 1. -/
theorem projectiveFormSection_cartierOrder_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ D : ℕ, 1 ≤ D →
      ∀ s ∈ projectiveFormSectionSpace e g hg hggen j₀ he D, s ≠ 0 →
        cartierSectionVanishingOrder (D • projectiveHyperplaneCartier e g hg hggen) x s ≤
          ((c * D : ℕ) : ℕ∞) := by
  obtain ⟨C, hΔ⟩ := projectiveFormSectionSpace_finrank_increment e g hg hggen he hn hd j₀
  refine ⟨⌈jetIncrementConstant d (C : ℝ) ((d : ℝ) ^ d)⌉₊, ?_⟩
  intro x hx D hD s hs hs0
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let jx : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hJx := projectiveHyperplane_isLocalEquationAt e g hg hggen jx x hk
  let := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨_, _, coords, _, _⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d hn
    (projectiveHyperplaneCartier e g hg hggen) x hx
  let J := projectiveHyperplaneCartier e g hg hggen
  let u := projectiveHyperplaneUnit e g hg hggen jx
  let V : ∀ D' : ℕ, Submodule K Γ((D' • J).sheaf, ⊤) := fun D' =>
    projectiveFormSectionSpace e g hg hggen j₀ he D'
  let T : ∀ D' : ℕ, Γ((D' • J).sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin d) K := fun D' =>
    cartierTaylorCoordinates (D' • J) x (u ^ D') (cartierLocalEquation_pow J x u hJx D') coords
  have hTorder : ∀ D' (t : Γ((D' • J).sheaf, ⊤)),
      (T D' t).order = cartierSectionVanishingOrder (D' • J) x t := fun D' t =>
    cartierTaylorCoordinates_order_eq_vanishingOrder (D' • J) x (u ^ D')
      (cartierLocalEquation_pow J x u hJx D') coords t
  let mulV : ∀ j' k', V j' → V k' →ₗ[K] V (j' + k') := fun j' k' s' =>
    ((cartierNsmulProductLinear (K := K) J j' k' s'.1).domRestrict (V k')).codRestrict
      (V (j' + k')) (fun t' => projectiveFormSectionSpace_mul_mem e g hg hggen j₀ he j' k' s'.2 t'.2)
  have hmulV : ∀ j' k' (s' : V j'), s' ≠ 0 → Function.Injective (mulV j' k' s') := by
    intro j' k' s' hs' t₁ t₂ h
    have hs'' : s'.1 ≠ 0 := fun hz => hs' (Subtype.ext hz)
    apply Subtype.ext
    apply cartierNsmulProduct_injective J j' k' s'.1 hs''
    exact congrArg Subtype.val h
  refine gradedSection_order_le_of_jets_increment (K := K)
    (fun D' => V D') mulV hmulV
    (fun m => (Fin d → Fin ((m - 1) / d + 1)) → K)
    (fun D' m => (powerSeriesBoxJet d ((m - 1) / d)).comp ((T D').domRestrict (V D')))
    ?_ (fun D' t => cartierSectionVanishingOrder (D' • J) x t.1) ?_ hd (b := (d : ℝ) ^ d)
    (by positivity) ?_ (C := (C : ℝ)) (by positivity) hΔ hD ⟨s, hs⟩
    (fun h0 => hs0 (congrArg Subtype.val h0))
  · -- Every box jet is realized by the section of a degree-D' form when m ≤ D' + 1.
    intro D' m hm hmD v
    obtain ⟨yy, hyy⟩ := completionCoordinates_exists_approx coords.toRingEquiv
      (powerSeriesOfBox d ((m - 1) / d) v) m
    obtain ⟨F, hF, hFy⟩ := polynomialProjective_closedImmersion_jet_realized e k x hk hx
      (m := m - 1) (D := D') (by omega) yy
    refine ⟨⟨projectiveFormSection e g hg hggen j₀ D' F hF, ⟨F, hF⟩, rfl⟩, ?_⟩
    change powerSeriesBoxJet d ((m - 1) / d)
      (T D' (projectiveFormSection e g hg hggen j₀ D' F hF)) = v
    rw [← powerSeriesBoxJet_ofBox d ((m - 1) / d) v]
    apply powerSeriesBoxJet_eq_of_le_order_sub d m hm
    have hT : T D' (projectiveFormSection e g hg hggen j₀ D' F hF) =
        coords (algebraMap (Y.presheaf.stalk x)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x))
          (Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D' F hF))) := by
      change cartierTaylorCoordinates (D' • J) x (u ^ D')
        (cartierLocalEquation_pow J x u hJx D') coords
          (projectiveFormSection e g hg hggen j₀ D' F hF) = _
      rw [cartierTaylorCoordinates_apply,
        projectiveFormSection_localCoefficient e g hg hggen j₀ jx x hk D' F hF]
    rw [hT]
    have hmem : Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D' F hF) - yy ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ m := by
      have h' := neg_mem hFy
      rw [neg_sub, Nat.sub_add_cancel hm] at h'
      exact h'
    have h1 := completionCoordinates_order_ge_of_mem_pow coords.toRingEquiv hmem
    rw [map_sub, map_sub] at h1
    have h2 : (m : ℕ∞) ≤ (coords.toRingEquiv (algebraMap (Y.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x)) yy) -
          powerSeriesOfBox d ((m - 1) / d) v).order := by
      rw [← MvPowerSeries.order_neg, neg_sub]
      exact hyy
    have h3 := (le_min h1 h2).trans MvPowerSeries.min_order_le_add
    rw [sub_add_sub_cancel] at h3
    exact h3
  · -- Box jets kill products with a section of order at least m.
    intro j' k' m t₁ t₂ hm hord
    change powerSeriesBoxJet d ((m - 1) / d)
      (T (j' + k') (cartierNsmulProduct J j' k' t₁.1 t₂.1)) = 0
    apply powerSeriesBoxJet_eq_zero_of_le_order d m hm
    have hprod : T (j' + k') (cartierNsmulProduct J j' k' t₁.1 t₂.1) = T j' t₁.1 * T k' t₂.1 :=
      cartierTaylorCoordinates_nsmulProduct J j' k' x u hJx coords t₁.1 t₂.1
    rw [hprod]
    calc (m : ℕ∞) ≤ (T j' t₁.1).order := by rw [hTorder]; exact hord
      _ ≤ (T j' t₁.1).order + (T k' t₂.1).order := le_self_add
      _ ≤ _ := MvPowerSeries.le_order_mul
  · -- The box of side (m-1)/d + 1 has at least m^d / d^d points.
    intro m hm
    have hcard : Module.finrank K ((Fin d → Fin ((m - 1) / d + 1)) → K) =
        ((m - 1) / d + 1) ^ d := by
      simp only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin]
    rw [hcard, Nat.cast_pow]
    exact pow_le_pow_mul_boxSide d m hd

end MixedFujita
