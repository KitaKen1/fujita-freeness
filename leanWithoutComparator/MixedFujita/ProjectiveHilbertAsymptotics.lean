/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSectionOrderBound
public import MixedFujita.LinearSystemFreePart

/-!
The leading Hilbert coefficient of the hyperplane class without a Hilbert polynomial. For an
actual smooth integral closed subscheme Y of dimension d ≥ 1 of polynomial projective space,
there is a positive integer r with h^0(D·J) / D^d → r / d!. The image V_D of the forms
contains V_D ⊆ Γ(D·J), the conductor form embeds Γ(D·J) into V_(D+k₀), and the free part
over the parameters gives r · dim R_(D-t) ≤ dim V_D ≤ r · dim R_(D+k₀) with r the number of
independent low monomials. The binomial asymptotics of dim R_m and a squeeze finish; r ≥ 1
because the jets at a closed point make dim V_D grow. The integer r is the degree of Y.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Asymptotics
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- A squeeze for the shifted binomial bounds. -/
theorem tendsto_div_pow_of_choose_bounds {d : ℕ} {r t c : ℕ} {h : ℕ → ℕ}
    (hlow : ∀ m, r * (m + d).choose d ≤ h (m + t))
    (hup : ∀ m, h (m + t) ≤ r * (m + c + d).choose d) :
    Tendsto (fun D : ℕ => (h D : ℝ) / (D : ℝ) ^ d) atTop (nhds ((r : ℝ) / d.factorial)) := by
  have hz : ∀ᶠ m : ℕ in atTop, ((m : ℝ) ^ d / d.factorial) ≠ 0 :=
    eventually_atTop.mpr ⟨1, fun m hm => div_ne_zero (pow_ne_zero _ (by exact_mod_cast
      (show m ≠ 0 by omega))) (by exact_mod_cast d.factorial_ne_zero)⟩
  have hfact : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  -- the two binomial bounds divided by m^d tend to r / d!
  have hb : ∀ c' : ℕ, Tendsto (fun m : ℕ => (r : ℝ) * ((m + c' + d).choose d : ℝ) / (m : ℝ) ^ d)
      atTop (nhds ((r : ℝ) / d.factorial)) := by
    intro c'
    have h1 := (isEquivalent_iff_tendsto_one hz).mp (isEquivalent_choose_shift d c')
    have h2 := h1.const_mul ((r : ℝ) / d.factorial)
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (m : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show m ≠ 0 by omega))
    simp only [Pi.div_apply]
    field_simp
  have h0 := hb 0
  simp only [add_zero] at h0
  have hc := hb c
  have hshift : Tendsto (fun m : ℕ => (h (m + t) : ℝ) / (m : ℝ) ^ d) atTop
      (nhds ((r : ℝ) / d.factorial)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 hc ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by exact_mod_cast hm) _
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlow m) hpos.le
    · filter_upwards [eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by exact_mod_cast hm) _
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hup m)) hpos.le
  -- shift back: h D / D^d = (h ((D - t) + t) / (D - t)^d) * ((D - t)^d / D^d)
  have hsub := hshift.comp (tendsto_sub_atTop_nat t)
  have hratio : Tendsto (fun D : ℕ => ((D - t : ℕ) : ℝ) ^ d / (D : ℝ) ^ d) atTop (nhds 1) := by
    have h1 : Tendsto (fun D : ℕ => ((D - t : ℕ) : ℝ) / (D : ℝ)) atTop (nhds 1) := by
      have h2 := (tendsto_natCast_div_add_atTop (t : ℝ)).comp (tendsto_sub_atTop_nat t)
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop t] with D hD
      simp only [Function.comp, Nat.cast_sub hD, sub_add_cancel]
    have h3 := h1.pow d
    rw [one_pow] at h3
    refine h3.congr' ?_
    filter_upwards with D
    rw [div_pow]
  have hprod := hsub.mul hratio
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (t + 1)] with D hD
  have hDt : D - t + t = D := Nat.sub_add_cancel (by omega)
  have hne : ((D - t : ℕ) : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show D - t ≠ 0 by omega))
  have hD0 : (D : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show D ≠ 0 by omega))
  simp only [Function.comp, hDt]
  field_simp

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The leading Hilbert coefficient of the hyperplane class. -/
theorem projectiveHyperplane_hilbert_leading
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
        atTop (nhds ((r : ℝ) / d.factorial)) := by
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨y, hy0, hyh, -, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  set P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal with hP
  have hPprime : P.IsPrime := (e (genericPoint Y)).isPrime
  obtain ⟨B, δR, k₀, hδR, hδR0, hBind, hBlow, hspan⟩ :=
    linearSystem_exists_commonDenominator (P := P) y hyh ht
  have hδP : aeval y δR ∉ P :=
    projective_linearSystem_relation_not_mem e g hg hggen he hn hd j₀ y hyh ht hδR hδR0
  have hδ : (aeval y δR).IsHomogeneous k₀ := by
    have h := hδR.aeval y hyh
    rwa [one_mul] at h
  obtain ⟨δ', k₀', hδ', hδ'P, hcond⟩ := projectiveSection_exists_conductor e g hg hggen he hn hd j₀
  have hfin := projectiveHyperplaneSections_finiteDimensional e g hg hggen he hn hd
  -- dimensions of the form images
  have hdimV : ∀ D, Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) =
      Module.finrank K (linearSystemFormImage (P := P) D) := by
    intro D
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
  refine ⟨B.card, ?_, hfin, ?_⟩
  · -- r ≥ 1: otherwise the form images vanish, against the jet lower bound
    rcases Nat.eq_zero_or_pos B.card with hB0 | hpos
    swap
    · exact hpos
    exfalso
    obtain ⟨x, hx⟩ := polynomialProjective_closedImmersion_exists_closedPoint e he
    have hjet := projectiveFormSectionSpace_finrank_lower e g hg hggen he hn hd j₀ x hx 0
    have hzero : Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he 0) = 0 := by
      rw [hdimV]
      have := hup 0
      rw [hB0, zero_mul] at this
      omega
    rw [hzero] at hjet
    norm_num at hjet
  · apply tendsto_div_pow_of_choose_bounds (t := t) (c := t + k₀' + k₀)
      (h := fun D => Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    · intro m
      exact (hlow m).trans ((hdimV (m + t)).symm.le.trans (hlowΓ (m + t)))
    · intro m
      refine (hupΓ (m + t)).trans ?_
      rw [hdimV]
      refine (hup (k₀' + (m + t))).trans ?_
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose d (by omega))

end MixedFujita
