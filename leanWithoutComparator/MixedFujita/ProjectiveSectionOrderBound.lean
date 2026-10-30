/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSectionDenominators
public import MixedFujita.ProjectiveParameterIndependence
public import MixedFujita.LinearSystemCommonDenominator

/-!
The uniform linear vanishing-order bound for all actual sections of D·J. One form δ avoiding
the generic point multiplies every actual section of D·J into the image of the forms of
degree k₀ + D. Multiply the section by y_0^N and y_1^N to make it a form on both sides, clear
the common denominator over the parameters and compare the two sides over the independent
monomials: Y_0^N divides the coefficients. The bound for form sections then bounds every
section with a constant independent of the closed point, because the order of a product is
the sum of the orders. No Serre theorem, cohomology, normalization or Bertini is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
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

omit [IsAlgClosed K] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  [IsClosedImmersion e] in
theorem projectiveFormRatio_sub_mem_of_eq
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    {F G : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D)
    (h : projectiveFormRatio e g hg hggen j D F hF = projectiveFormRatio e g hg hggen j D G hG) :
    F - G ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
  apply (projectiveFormRatio_eq_zero_iff e g hg hggen j D (F - G) (hF.sub hG)).mp
  have hadd := projectiveFormRatio_add e g hg hggen j D (F - G) G (hF.sub hG) hG
  rw [projectiveFormRatio_congr_poly e g hg hggen j rfl (sub_add_cancel F G) _ hF, h] at hadd
  linear_combination -hadd

omit [IsAlgClosed K] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  [IsClosedImmersion e] in
theorem projectiveFormRatio_mul_three
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) {D₁ D₂ D₃ : ℕ}
    {F₁ F₂ F₃ : MvPolynomial (Fin n) K} (h₁ : F₁.IsHomogeneous D₁) (h₂ : F₂.IsHomogeneous D₂)
    (h₃ : F₃.IsHomogeneous D₃) :
    projectiveFormRatio e g hg hggen j (D₁ + (D₂ + D₃)) (F₁ * (F₂ * F₃)) (h₁.mul (h₂.mul h₃)) =
      projectiveFormRatio e g hg hggen j D₁ F₁ h₁ *
        (projectiveFormRatio e g hg hggen j D₂ F₂ h₂ * projectiveFormRatio e g hg hggen j D₃ F₃ h₃) := by
  rw [projectiveFormRatio_mul e g hg hggen j D₁ (D₂ + D₃) F₁ (F₂ * F₃) h₁ (h₂.mul h₃),
    projectiveFormRatio_mul e g hg hggen j D₂ D₃ F₂ F₃ h₂ h₃]

/-- One conductor form for all actual sections: δ times any section of D·J is the section of a
form of degree k₀ + D. -/
theorem projectiveSection_exists_conductor
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ∃ (δ : MvPolynomial (Fin n) K) (k₀ : ℕ) (hδ : δ.IsHomogeneous k₀),
      δ ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
      ∀ (D : ℕ) (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        IsProjectiveFormRatio e g hg hggen j₀ (k₀ + D)
          (projectiveFormRatio e g hg hggen j₀ k₀ δ hδ *
            cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨y, hy0, hyh, -, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  obtain ⟨B, δR, k₀, hδR, hδR0, hBind, -, hspan⟩ :=
    linearSystem_exists_commonDenominator (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal)
      y hyh ht
  have hδ : (aeval y δR).IsHomogeneous k₀ := by
    have h := hδR.aeval y hyh
    rwa [one_mul] at h
  refine ⟨aeval y δR, k₀, hδ,
    projective_linearSystem_relation_not_mem e g hg hggen he hn hd j₀ y hyh ht hδR hδR0, fun D s => ?_⟩
  set r := cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s
  obtain ⟨N, hN⟩ := projectiveSection_form_mul_isFormRatio e g hg hggen he j₀ D s
  set i₁ : Fin (d + 1) := ⟨1, by omega⟩
  have hy0N : (y 0 ^ N).IsHomogeneous N := by simpa using (hyh 0).pow N
  have hy1N : (y i₁ ^ N).IsHomogeneous N := by simpa using (hyh i₁).pow N
  obtain ⟨a₀, ha₀, hr₀⟩ := hN N le_rfl (y 0 ^ N) hy0N
  obtain ⟨a₁, ha₁, hr₁⟩ := hN N le_rfl (y i₁ ^ N) hy1N
  have hs₀ := hspan (N + D) a₀ ha₀
  have hs₁ := hspan (N + D) a₁ ha₁
  rw [show N + D + k₀ = N + (D + k₀) by omega] at hs₀ hs₁
  -- The two sides agree as rational functions.
  have hcross : y i₁ ^ N * (aeval y δR * a₀) - y 0 ^ N * (aeval y δR * a₁) ∈
      (e (genericPoint Y)).asHomogeneousIdeal.toIdeal := by
    have hL := projectiveFormRatio_mul_three e g hg hggen j₀ hy1N hδ ha₀
    have hR := projectiveFormRatio_mul_three e g hg hggen j₀ hy0N hδ ha₁
    apply projectiveFormRatio_sub_mem_of_eq e g hg hggen j₀ (N + (k₀ + (N + D)))
      (hy1N.mul (hδ.mul ha₀)) (hy0N.mul (hδ.mul ha₁))
    rw [hL, hR, ← hr₀, ← hr₁]
    ring
  obtain ⟨G, hG, hGP⟩ := linearSystem_intersection y hyh hd hBind hs₀ hs₁ hcross
  have hG' : G.IsHomogeneous (k₀ + D) := by rwa [Nat.add_comm k₀ D]
  refine ⟨G, hG', ?_⟩
  have hL : projectiveFormRatio e g hg hggen j₀ (k₀ + (N + D)) (aeval y δR * a₀) (hδ.mul ha₀) =
      projectiveFormRatio e g hg hggen j₀ k₀ (aeval y δR) hδ *
        (projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N * r) := by
    rw [projectiveFormRatio_mul e g hg hggen j₀ k₀ (N + D) _ _ hδ ha₀, ← hr₀]
  have hY : (y 0 ^ N * G).IsHomogeneous (k₀ + (N + D)) := by
    have h := hy0N.mul hG'
    rwa [show N + (k₀ + D) = k₀ + (N + D) by omega] at h
  have hR : projectiveFormRatio e g hg hggen j₀ (k₀ + (N + D)) (y 0 ^ N * G) hY =
      projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N *
        projectiveFormRatio e g hg hggen j₀ (k₀ + D) G hG' := by
    rw [projectiveFormRatio_congr_poly e g hg hggen j₀ (show k₀ + (N + D) = N + (k₀ + D) by omega)
      rfl hY (hy0N.mul hG'), projectiveFormRatio_mul e g hg hggen j₀ N (k₀ + D) _ _ hy0N hG']
  have heq := projectiveFormRatio_eq_of_sub_mem e g hg hggen j₀ (k₀ + (N + D)) (hδ.mul ha₀) hY hGP
  rw [hL, hR] at heq
  have hne : projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N ≠ 0 := by
    intro h0
    have hmem := (projectiveFormRatio_eq_zero_iff e g hg hggen j₀ N _ hy0N).mp h0
    rw [hy0] at hmem
    exact hggen ((e (genericPoint Y)).isPrime.mem_of_pow_mem N hmem)
  have hzero : projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N *
      (projectiveFormRatio e g hg hggen j₀ k₀ (aeval y δR) hδ * r -
        projectiveFormRatio e g hg hggen j₀ (k₀ + D) G hG') = 0 := by
    linear_combination heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hne)

omit [IsAlgClosed K] [Smooth (Y ↘ Spec (CommRingCat.of K))] [IsClosedImmersion e] in
/-- Multiplying by the section of the conductor form lands in the form sections. -/
theorem projectiveSection_conductor_mul_mem
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {δ : MvPolynomial (Fin n) K} {k₀ : ℕ} (hδ : δ.IsHomogeneous k₀)
    (hcond : ∀ (D : ℕ) (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
      IsProjectiveFormRatio e g hg hggen j₀ (k₀ + D)
        (projectiveFormRatio e g hg hggen j₀ k₀ δ hδ *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s))
    (D : ℕ) (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) k₀ D
        (projectiveFormSection e g hg hggen j₀ k₀ δ hδ) s ∈
      projectiveFormSectionSpace e g hg hggen j₀ he (k₀ + D) := by
  obtain ⟨G, hG, hGr⟩ := hcond D s
  refine ⟨⟨G, hG⟩, ?_⟩
  rw [projectiveFormSectionLinear_apply]
  apply cartierSectionRational_injective
  rw [projectiveFormSection_rational, cartierNsmulProduct_rational, projectiveFormSection_rational]
  exact hGr.symm

omit [IsAlgClosed K] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  [IsClosedImmersion e] in
theorem projectiveFormSection_ne_zero_of_not_mem
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {δ : MvPolynomial (Fin n) K} {k₀ : ℕ} (hδ : δ.IsHomogeneous k₀)
    (hδP : δ ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    projectiveFormSection e g hg hggen j₀ k₀ δ hδ ≠ 0 := by
  intro h0
  have h := congrArg (cartierSectionRational (k₀ • projectiveHyperplaneCartier e g hg hggen)) h0
  rw [projectiveFormSection_rational, map_zero] at h
  exact hδP ((projectiveFormRatio_eq_zero_iff e g hg hggen j₀ k₀ δ hδ).mp h)

/-- The actual sections of D·J are finite-dimensional: the conductor embeds them into the form
sections of degree k₀ + D. -/
theorem projectiveHyperplaneSections_finiteDimensional
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (D : ℕ) :
    FiniteDimensional K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨δ, k₀, hδ, hδP, hcond⟩ := projectiveSection_exists_conductor e g hg hggen he hn hd j₀
  let f := ((cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀ D
    (projectiveFormSection e g hg hggen j₀ k₀ δ hδ))).codRestrict
      (projectiveFormSectionSpace e g hg hggen j₀ he (k₀ + D))
      (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ hcond D)
  have hf : Function.Injective f := by
    intro s t hst
    exact cartierNsmulProduct_injective _ k₀ D _
      (projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ hδP) (congrArg Subtype.val hst)
  exact Module.Finite.of_injective f hf

/-- One constant bounds the order of every nonzero actual section of D·J, D ≥ 1, at every
closed point. -/
theorem projectiveHyperplane_cartierOrder_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ D : ℕ, 1 ≤ D →
      ∀ s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), s ≠ 0 →
        cartierSectionVanishingOrder (D • projectiveHyperplaneCartier e g hg hggen) x s ≤
          ((c * D : ℕ) : ℕ∞) := by
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨δ, k₀, hδ, hδP, hcond⟩ := projectiveSection_exists_conductor e g hg hggen he hn hd j₀
  obtain ⟨c, hc⟩ := projectiveFormSection_cartierOrder_le e g hg hggen he hn hd j₀
  refine ⟨c * (k₀ + 1), fun x hx D hD s hs => ?_⟩
  have hσδ := projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ hδP
  have hp0 : cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) k₀ D
      (projectiveFormSection e g hg hggen j₀ k₀ δ hδ) s ≠ 0 := by
    intro h0
    apply hs
    have h00 : cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) k₀ D
        (projectiveFormSection e g hg hggen j₀ k₀ δ hδ) 0 = 0 :=
      map_zero (cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀ D
        (projectiveFormSection e g hg hggen j₀ k₀ δ hδ))
    exact cartierNsmulProduct_injective _ k₀ D _ hσδ (h0.trans h00.symm)
  have hpbound := hc x hx (k₀ + D) (by omega) _
    (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ hcond D s) hp0
  have hle : cartierSectionVanishingOrder (D • projectiveHyperplaneCartier e g hg hggen) x s ≤
      cartierSectionVanishingOrder ((k₀ + D) • projectiveHyperplaneCartier e g hg hggen) x
        (cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) k₀ D
          (projectiveFormSection e g hg hggen j₀ k₀ δ hδ) s) := by
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
    let jx : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
    have hJx := projectiveHyperplane_isLocalEquationAt e g hg hggen jx x hk
    let := smoothScheme_stalk_isNoetherianRing (K := K) x
    obtain ⟨_, _, coords, _, _⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d hn
      (projectiveHyperplaneCartier e g hg hggen) x hx
    rw [← cartierTaylorCoordinates_order_eq_vanishingOrder _ x _
        (cartierLocalEquation_pow _ x _ hJx D) coords s,
      ← cartierTaylorCoordinates_order_eq_vanishingOrder _ x _
        (cartierLocalEquation_pow _ x _ hJx (k₀ + D)) coords,
      cartierTaylorCoordinates_nsmulProduct (projectiveHyperplaneCartier e g hg hggen)
        k₀ D x (projectiveHyperplaneUnit e g hg hggen jx) hJx coords,
      powerSeries_order_mul_exact]
    exact le_add_self
  calc cartierSectionVanishingOrder (D • projectiveHyperplaneCartier e g hg hggen) x s
      ≤ ((c * (k₀ + D) : ℕ) : ℕ∞) := hle.trans hpbound
    _ ≤ ((c * (k₀ + 1) * D : ℕ) : ℕ∞) := by
        apply Nat.cast_le.mpr
        calc c * (k₀ + D) ≤ c * ((k₀ + 1) * D) :=
            Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_left k₀ hD; nlinarith)
          _ = c * (k₀ + 1) * D := by ring

end MixedFujita
