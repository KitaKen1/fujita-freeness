/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemRankIncrement
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.NumericalBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Lemma 4 of the manuscript for the restricted forms. Let W be an actual integral closed subscheme
of dimension d ≥ 1 of polynomial projective space over an infinite field, and r its degree, the
leading coefficient of h^0(D·J) = r D^d / d! + o(D^d). The actual sections of q·J on W that
are restrictions of degree-q forms have dimension at least min(r, D₀) · C(q + 1 - D₀ + d, d)
for every D₀ ≤ q + 1. The bound depends only on D₀, q and d, not on W, its degree beyond D₀,
or its singularities. If r ≥ s^d, then d! · dim ≥ s^d (q + 1 - s^d)^d, that is
(d! I_W(q))^(1/d) ≥ s (q + 1 - s^d), the inequality (13) in the hyperplane embedding. The rank
increment over the parameters replaces the generic finite projection, the separable generic
fibre and the choice of points on it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Asymptotics
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [Infinite K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Lemma 4 for the restricted forms: one bound for every integral closed subscheme, in terms of
its degree. -/
theorem projective_restrictedForms_uniform_lower
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
        atTop (nhds ((r : ℝ) / d.factorial)) ∧
      ∀ (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D₀ q : ℕ),
        D₀ ≤ q + 1 →
          min r D₀ * (q + 1 - D₀ + d).choose d ≤
            Module.finrank K (projectiveFormSectionSpace e g hg hggen j he q) := by
  have := polynomialProjectiveToBase_isProper n K
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨y, hy0, hyh, -, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  set P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal with hP
  have hPprime : P.IsPrime := (e (genericPoint Y)).isPrime
  have hpar : ∀ (Φ : MvPolynomial (Fin (d + 1)) K) (k : ℕ), Φ.IsHomogeneous k → Φ ≠ 0 →
      aeval y Φ ∉ P := fun Φ k hΦ hΦ0 =>
    projective_linearSystem_relation_not_mem_integral e hn hd y hyh ht hΦ hΦ0
  obtain ⟨B, δR, k₀, hδR, hδR0, hBind, hBlow, hspan⟩ :=
    linearSystem_exists_commonDenominator (P := P) y hyh ht
  have hδP : aeval y δR ∉ P := hpar δR k₀ hδR hδR0
  obtain ⟨δ', k₀', hδ', hδ'P, hcond⟩ :=
    projectiveSection_exists_conductor_integral e g hg hggen he hn hd j₀
  have hfin := projectiveHyperplaneSections_finiteDimensional_integral e g hg hggen he hn hd
  -- dimensions of the form images
  have hdimV : ∀ (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) D,
      Module.finrank K (projectiveFormSectionSpace e g hg hggen j he D) =
        Module.finrank K (linearSystemFormImage (P := P) D) := by
    intro j D
    rw [projectiveFormSectionSpace_finrank, ← linearSystemQuotientDim_eq_finrank_formImage y D]
    unfold linearSystemQuotientDim
    rw [linearSystemFiltration_zero]
  -- sections between the form images
  have hlowΓ : ∀ D, Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) ≤
      Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
    fun D => Submodule.finrank_le _
  have hupΓ : ∀ D, Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
      Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he (k₀' + D)) := by
    intro D
    let f := ((cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀' D
      (projectiveFormSection e g hg hggen j₀ k₀' δ' hδ'))).codRestrict
        (projectiveFormSectionSpace e g hg hggen j₀ he (k₀' + D))
        (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ' hcond D)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
    intro s s' hss
    exact cartierNsmulProduct_injective _ k₀' D _
      (projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ' hδ'P) (congrArg Subtype.val hss)
  -- the free-part bounds
  have hlow : ∀ m, B.card * (m + d).choose d ≤
      Module.finrank K (linearSystemFormImage (P := P) (m + t)) := by
    intro m
    refine le_trans ?_ (linearSystem_freePart_le y hyh hBind (m + t))
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_le_sum fun b hb => ?_
    have hbt : b.degree < t := hBlow b hb
    rw [one_mul, ite_eq_left (show b.degree ≤ m + t by omega)]
    exact Nat.choose_le_choose d (by omega)
  have hup : ∀ D, Module.finrank K (linearSystemFormImage (P := P) D) ≤
      B.card * (D + k₀ + d).choose d := by
    intro D
    refine (linearSystem_formImage_le_freePart y hδP hspan D).trans ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [one_mul]
    split_ifs
    · exact Nat.choose_le_choose d (by omega)
    · exact Nat.zero_le _
  refine ⟨B.card, ?_, hfin, ?_, ?_⟩
  · -- r ≥ 1: otherwise the form images vanish, against the growth along a chain
    rcases Nat.eq_zero_or_pos B.card with hB0 | hpos
    swap
    · exact hpos
    exfalso
    have hgrowth := projective_formImage_growth e (d := d) hn.ge
    rw [← hP] at hgrowth
    obtain ⟨c, hc, D₀, hD₀⟩ := hgrowth
    have h1 := hD₀ (D₀ + 1) (by omega)
    have h2 := hup (D₀ + 1)
    rw [hB0, zero_mul] at h2
    have h3 : Module.finrank K (linearSystemFormImage (P := P) (D₀ + 1)) = 0 := by omega
    rw [h3, Nat.cast_zero] at h1
    have h4 : (0 : ℝ) < c * ((D₀ + 1 : ℕ) : ℝ) ^ d := by positivity
    linarith
  · apply tendsto_div_pow_of_choose_bounds (t := t) (c := t + k₀' + k₀)
      (h := fun D => Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    · intro m
      exact (hlow m).trans ((hdimV j₀ (m + t)).symm.le.trans (hlowΓ (m + t)))
    · intro m
      refine (hupΓ (m + t)).trans ?_
      rw [hdimV]
      refine (hup (k₀' + (m + t))).trans ?_
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose d (by omega))
  · intro j D₀ q hq
    rw [hdimV j q]
    exact linearSystem_formImage_uniform_lower y hyh ht hpar hBind hq

/-- The inequality (13) of Lemma 4 in the hyperplane embedding: if the degree is at least s^d,
then (d! I_W(q))^(1/d) ≥ s (q + 1 - s^d) for the restricted forms. -/
theorem projective_restrictedForms_root_lower
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
        atTop (nhds ((r : ℝ) / d.factorial)) ∧
      ∀ (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (s q : ℕ),
        s ^ d ≤ r → s ^ d ≤ q + 1 →
          s ^ d * (q + 1 - s ^ d) ^ d ≤
              d.factorial * Module.finrank K (projectiveFormSectionSpace e g hg hggen j he q) ∧
            (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ d) ≤
              ((d.factorial * Module.finrank K
                (projectiveFormSectionSpace e g hg hggen j he q) : ℕ) : ℝ) ^ ((1 : ℝ) / d) := by
  obtain ⟨r, hr, hfin, hlim, hunif⟩ := projective_restrictedForms_uniform_lower e g hg hggen he hn hd
  refine ⟨r, hr, hfin, hlim, fun j s q hsr hsq => ?_⟩
  set I := Module.finrank K (projectiveFormSectionSpace e g hg hggen j he q) with hI
  have hcount := hunif j (s ^ d) q hsq
  rw [min_eq_right hsr] at hcount
  have hnat : s ^ d * (q + 1 - s ^ d) ^ d ≤ d.factorial * I :=
    restriction_count_power_bound I (s ^ d) (q + 1 - s ^ d) d hcount
  refine ⟨hnat, ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hcast : ((q + 1 - s ^ d : ℕ) : ℝ) = (q : ℝ) + 1 - (s : ℝ) ^ d := by
    rw [Nat.cast_sub hsq]
    push_cast
    ring
  have hx : (0 : ℝ) ≤ (s : ℝ) * ((q + 1 - s ^ d : ℕ) : ℝ) := by positivity
  have hpow : ((s : ℝ) * ((q + 1 - s ^ d : ℕ) : ℝ)) ^ d ≤ ((d.factorial * I : ℕ) : ℝ) := by
    rw [mul_pow]
    exact_mod_cast hnat
  have hroot := Real.rpow_le_rpow (pow_nonneg hx d) hpow (by positivity : (0 : ℝ) ≤ 1 / d)
  rw [one_div, Real.pow_rpow_inv_natCast hx (by omega)] at hroot
  rw [← hcast, one_div]
  exact hroot

end MixedFujita
