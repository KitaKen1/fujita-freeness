/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveIntegralHilbert

/-!
The Hilbert growth of the restricted forms of an actual integral closed subscheme of polynomial
projective space (step 4). The conductor embeds the sections of D·J into the form sections of
degree k₀ + D, and the form sections of degree D are sections of D·J. So the image V_D of the
forms of degree D has the same leading term as the sections: if h^0(D·J)/D^d tends to ρ, then
dim V_D / D^d tends to ρ. The limit for the sections is a hypothesis here, so that one number
serves both sequences; it exists, with ρ = r/d! for the degree r, by
`projectiveHyperplane_hilbert_leading_integral`. The mixed bound (13) counts restricted forms, and
this is how the degree enters it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- A sequence b with a(D) ≤ b(k₀ + D) and b(D) ≤ a(D) has the leading term of a. -/
theorem tendsto_div_pow_of_shift_squeeze {a b : ℕ → ℕ} {d k₀ : ℕ} {ρ : ℝ}
    (hlow : ∀ D, a D ≤ b (k₀ + D)) (hup : ∀ D, b D ≤ a D)
    (ha : Tendsto (fun D : ℕ => (a D : ℝ) / (D : ℝ) ^ d) atTop (nhds ρ)) :
    Tendsto (fun D : ℕ => (b D : ℝ) / (D : ℝ) ^ d) atTop (nhds ρ) := by
  have h1 : Tendsto (fun D : ℕ => (a (D - k₀) : ℝ) / ((D - k₀ : ℕ) : ℝ) ^ d) atTop (nhds ρ) :=
    ha.comp (tendsto_sub_atTop_nat k₀)
  have h3 : Tendsto (fun D : ℕ => ((D - k₀ : ℕ) : ℝ) / (D : ℝ)) atTop (nhds 1) := by
    have h4 : Tendsto (fun D : ℕ => (1 : ℝ) - (k₀ : ℝ) / (D : ℝ)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k₀ : ℝ))
    rw [sub_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop (max k₀ 1)] with D hD
    have hD1 : 1 ≤ D := le_trans (le_max_right _ _) hD
    have hD0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_sub (le_trans (le_max_left _ _) hD), sub_div, div_self hD0]
  have h2 : Tendsto (fun D : ℕ => (((D - k₀ : ℕ) : ℝ) / (D : ℝ)) ^ d) atTop (nhds 1) := by
    have h := h3.pow d
    rwa [one_pow] at h
  have hlowlim : Tendsto (fun D : ℕ => (a (D - k₀) : ℝ) / (D : ℝ) ^ d) atTop (nhds ρ) := by
    have h5 := h1.mul h2
    rw [mul_one] at h5
    refine h5.congr' ?_
    filter_upwards [eventually_gt_atTop k₀] with D hD
    have hpos : ((D - k₀ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_pow, div_mul_div_comm, mul_comm ((a (D - k₀) : ℝ)) _,
      mul_div_mul_left _ _ (pow_ne_zero d hpos)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim ha ?_ ?_
  · filter_upwards [eventually_ge_atTop k₀] with D hD
    have h := hlow (D - k₀)
    rw [Nat.add_sub_cancel' hD] at h
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
  · exact Eventually.of_forall fun D =>
      div_le_div_of_nonneg_right (by exact_mod_cast hup D) (by positivity)

variable {K : Type u} [Field K] [Infinite K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The sections of D·J embed in the form sections of degree k₀ + D, for one k₀. -/
theorem projectiveHyperplaneSections_finrank_le_formSpace
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ∃ k₀ : ℕ, ∀ D : ℕ,
      Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
        Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he (k₀ + D)) := by
  obtain ⟨δ, k₀, hδ, hδP, hcond⟩ :=
    projectiveSection_exists_conductor_integral e g hg hggen he hn hd j₀
  refine ⟨k₀, fun D => ?_⟩
  let f := ((cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀ D
    (projectiveFormSection e g hg hggen j₀ k₀ δ hδ))).codRestrict
      (projectiveFormSectionSpace e g hg hggen j₀ he (k₀ + D))
      (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ hcond D)
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  intro s s' hss
  exact cartierNsmulProduct_injective _ k₀ D _
    (projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ hδP) (congrArg Subtype.val hss)

/-- The restricted forms have the leading Hilbert term of the sections. -/
theorem projectiveFormSectionSpace_tendsto
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) {ρ : ℝ}
    (hlim : Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
      atTop (nhds ρ)) :
    Tendsto (fun D : ℕ => (Module.finrank K
        (projectiveFormSectionSpace e g hg hggen j₀ he D) : ℝ) / (D : ℝ) ^ d)
      atTop (nhds ρ) := by
  obtain ⟨k₀, hk₀⟩ := projectiveHyperplaneSections_finrank_le_formSpace e g hg hggen he hn hd j₀
  have hfin := projectiveHyperplaneSections_finiteDimensional_integral e g hg hggen he hn hd
  exact tendsto_div_pow_of_shift_squeeze
    (a := fun D => Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    (b := fun D => Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D)) hk₀
    (fun D => by
      have := hfin D
      exact Submodule.finrank_le _) hlim

end MixedFujita
