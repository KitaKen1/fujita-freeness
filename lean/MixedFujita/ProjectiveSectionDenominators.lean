/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.ProjectiveHomogenization

/-!
Every actual section of D·J becomes the section of a form after multiplying by a form of
high degree. On a nonempty chart the rational function of the section times the D-th
power of the chart equation is regular on the chart, hence the pullback of a
polynomial; homogenizing it in degree M gives X_k^M s = σ_G with deg G = M + D. On an
empty chart X_k vanishes at the generic point. By pigeonhole, every form of degree
at least the sum of the chart exponents multiplies s into the forms. Everything is
stated through rational functions, so no degree casts between section spaces occur.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K)
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

theorem projectiveFormRatio_congr_degree
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) {D D' : ℕ} (h : D = D')
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) (hF' : F.IsHomogeneous D') :
    projectiveFormRatio e g hg hggen j D F hF = projectiveFormRatio e g hg hggen j D' F hF' := by
  subst h
  rfl

theorem projectiveFormRatio_congr_poly
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) {D D' : ℕ} (hD : D = D')
    {F G : MvPolynomial (Fin n) K} (hFG : F = G) (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D') :
    projectiveFormRatio e g hg hggen j D F hF = projectiveFormRatio e g hg hggen j D' G hG := by
  subst hD
  subst hFG
  rfl

theorem projectiveFormRatio_eq_of_sub_mem
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    {F G : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D)
    (h : F - G ∈ (e (genericPoint Y)).asHomogeneousIdeal) :
    projectiveFormRatio e g hg hggen j D F hF = projectiveFormRatio e g hg hggen j D G hG := by
  have hsub : (F - G).IsHomogeneous D := hF.sub hG
  have h0 := (projectiveFormRatio_eq_zero_iff e g hg hggen j D (F - G) hsub).mpr h
  have hadd := projectiveFormRatio_add e g hg hggen j D (F - G) G hsub hG
  simp only [sub_add_cancel, h0, zero_add] at hadd
  exact hadd

theorem projectiveFormRatio_zero
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ) :
    projectiveFormRatio e g hg hggen j D 0 (isHomogeneous_zero _ _ _) = 0 :=
  (projectiveFormRatio_eq_zero_iff e g hg hggen j D 0 _).mpr (Ideal.zero_mem _)

/-- On a nonempty chart the rational function of a section times the D-th power of the chart
equation is regular. -/
theorem cartierSectionRational_chart_regular
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    ∃ a : Γ(Y, projectivePullbackCoordinateOpen e k.val),
      Y.germToFunctionField _ a =
        ((projectiveHyperplaneUnit e g hg hggen k ^ D : Y.functionFieldˣ) : Y.functionField) *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s := by
  have : Nonempty (projectivePullbackCoordinateOpen e k.val) := k.2
  apply exists_germToFunctionField_eq_of_forall_mem_range
  intro x hx
  have hloc := cartierLocalEquation_pow (projectiveHyperplaneCartier e g hg hggen) x _
    (projectiveHyperplane_isLocalEquationAt e g hg hggen k x hx) D
  exact (CartierDivisor.mem_sections.mp
    ((D • projectiveHyperplaneCartier e g hg hggen).sheafι_app_mem ⊤ s)) x (Opens.mem_top x) _ hloc

/-- Membership of a rational function in the image of degree-D forms. -/
def IsProjectiveFormRatio (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (D : ℕ) (r : Y.functionField) : Prop :=
  ∃ (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous D),
    r = projectiveFormRatio e g hg hggen j D G hG

theorem isProjectiveFormRatio_mul (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {D D' : ℕ} {r r' : Y.functionField} (hr : IsProjectiveFormRatio e g hg hggen j D r)
    (hr' : IsProjectiveFormRatio e g hg hggen j D' r') :
    IsProjectiveFormRatio e g hg hggen j (D + D') (r * r') := by
  obtain ⟨G, hG, rfl⟩ := hr
  obtain ⟨G', hG', rfl⟩ := hr'
  exact ⟨G * G', hG.mul hG', (projectiveFormRatio_mul e g hg hggen j D D' G G' hG hG').symm⟩

theorem isProjectiveFormRatio_add (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {D : ℕ} {r r' : Y.functionField} (hr : IsProjectiveFormRatio e g hg hggen j D r)
    (hr' : IsProjectiveFormRatio e g hg hggen j D r') :
    IsProjectiveFormRatio e g hg hggen j D (r + r') := by
  obtain ⟨G, hG, rfl⟩ := hr
  obtain ⟨G', hG', rfl⟩ := hr'
  exact ⟨G + G', hG.add hG', (projectiveFormRatio_add e g hg hggen j D G G' hG hG').symm⟩

theorem isProjectiveFormRatio_zero (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (D : ℕ) : IsProjectiveFormRatio e g hg hggen j D 0 :=
  ⟨0, isHomogeneous_zero _ _ _, (projectiveFormRatio_zero e g hg hggen j D).symm⟩

theorem isProjectiveFormRatio_congr (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {D D' : ℕ} (h : D = D') {r : Y.functionField} (hr : IsProjectiveFormRatio e g hg hggen j D r) :
    IsProjectiveFormRatio e g hg hggen j D' r := by
  subst h
  exact hr

theorem isProjectiveFormRatio_chart (j j' : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {D : ℕ} {r : Y.functionField} (hr : IsProjectiveFormRatio e g hg hggen j D r) :
    IsProjectiveFormRatio e g hg hggen j' D r := by
  obtain ⟨G, hG, rfl⟩ := hr
  exact ⟨G, hG, projectiveFormRatio_chart_independent e g hg hggen j j' D G hG⟩

theorem isProjectiveFormRatio_form (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    {D : ℕ} (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) :
    IsProjectiveFormRatio e g hg hggen j D (projectiveFormRatio e g hg hggen j D F hF) :=
  ⟨F, hF, rfl⟩

section BaseRatio

variable [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

theorem isProjectiveFormRatio_smul
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) {D : ℕ} (c : K)
    {r : Y.functionField} (hr : IsProjectiveFormRatio e g hg hggen j D r) :
    IsProjectiveFormRatio e g hg hggen j D (algebraMap Γ(Y, ⊤) Y.functionField
      (algebraMap K Γ(Y, ⊤) c) * r) := by
  obtain ⟨G, hG, rfl⟩ := hr
  refine ⟨c • G, Submodule.smul_mem (homogeneousSubmodule (Fin n) K D) c hG, ?_⟩
  rw [projectiveFormRatio_smul e g hg hggen j he D c G hG, Algebra.smul_def]

end BaseRatio

variable [IsClosedImmersion e]

/-- On a nonempty chart k, X_k^M times a section of D·J is the section of a form of degree
M + D. -/
theorem projectiveSection_coordinatePow_mul_eq_form
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    ∃ (M : ℕ) (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous (M + D)),
      projectiveFormRatio e g hg hggen k M (X k.val ^ M) (isHomogeneous_X_pow k.val M) *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s =
        projectiveFormRatio e g hg hggen k (M + D) G hG := by
  obtain ⟨a, ha⟩ := cartierSectionRational_chart_regular e g hg hggen k D s
  obtain ⟨B, rfl⟩ := projectivePullbackAffinePolynomialMap_surjective e k.val a
  refine ⟨B.totalDegree, projectiveHomogenize k.val B.totalDegree B * X k.val ^ D,
    (projectiveHomogenize_isHomogeneous k.val B le_rfl).mul (isHomogeneous_X_pow k.val D), ?_⟩
  unfold projectiveFormRatio
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectivePullbackHomogeneousEquation_eq_affine]
  simp only [map_pow, map_mul, projectiveDehomogenize_X_self, one_pow, mul_one, map_one,
    projectiveDehomogenize_homogenize, one_mul]
  rw [ha]
  set u := projectiveHyperplaneUnit e g hg hggen k
  set r := cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s
  have hunit : u ^ D * u⁻¹ ^ (B.totalDegree + D) = u⁻¹ ^ B.totalDegree := by
    rw [pow_add, mul_left_comm, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rw [mul_comm (((u ^ D : Y.functionFieldˣ) : Y.functionField)) r, mul_assoc, ← Units.val_mul, hunit,
    mul_comm]

/-- Every monomial of degree at least N times a section of D·J is the section of a form. -/
theorem projectiveSection_monomial_mul_isFormRatio
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    ∃ N, ∀ μ : Fin n →₀ ℕ, N ≤ μ.degree →
      IsProjectiveFormRatio e g hg hggen j₀ (μ.degree + D)
        (projectiveFormRatio e g hg hggen j₀ μ.degree (monomial μ 1) (isHomogeneous_monomial 1 rfl) *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
  classical
  have hchart : ∀ k : Fin n, ∃ M : ℕ, 1 ≤ M ∧ ∀ μ : Fin n →₀ ℕ, M ≤ μ k →
      IsProjectiveFormRatio e g hg hggen j₀ (μ.degree + D)
        (projectiveFormRatio e g hg hggen j₀ μ.degree (monomial μ 1) (isHomogeneous_monomial 1 rfl) *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
    intro k
    by_cases hne : Nonempty (projectivePullbackCoordinateOpen e k)
    · let kk : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, hne⟩
      obtain ⟨M, G, hG, hMG⟩ := projectiveSection_coordinatePow_mul_eq_form e g hg hggen kk D s
      refine ⟨M + 1, Nat.le_add_left 1 M, fun μ hμ => ?_⟩
      have hle : Finsupp.single k M ≤ μ := Finsupp.single_le_iff.mpr (by omega)
      set μ' := μ - Finsupp.single k M with hμ'
      have hsum : μ' + Finsupp.single k M = μ := tsub_add_cancel_of_le hle
      have hdeg : μ'.degree + M = μ.degree := by
        rw [← hsum, map_add, Finsupp.degree_single]
      have hmono : monomial μ (1 : K) = monomial μ' 1 * X k ^ M := by
        rw [← hsum, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
      have hsplit : projectiveFormRatio e g hg hggen j₀ μ.degree (monomial μ 1)
          (isHomogeneous_monomial 1 rfl) =
          projectiveFormRatio e g hg hggen j₀ μ'.degree (monomial μ' 1) (isHomogeneous_monomial 1 rfl) *
            projectiveFormRatio e g hg hggen kk M (X k ^ M) (isHomogeneous_X_pow k M) := by
        rw [projectiveFormRatio_chart_independent e g hg hggen kk j₀,
          ← projectiveFormRatio_mul e g hg hggen j₀ μ'.degree M]
        exact projectiveFormRatio_congr_poly e g hg hggen j₀ hdeg.symm hmono _ _
      rw [hsplit, mul_assoc, hMG]
      have h := isProjectiveFormRatio_mul e g hg hggen j₀
        (isProjectiveFormRatio_form e g hg hggen j₀ (monomial μ' 1) (isHomogeneous_monomial 1 rfl))
        (isProjectiveFormRatio_chart e g hg hggen kk j₀ (isProjectiveFormRatio_form e g hg hggen kk G hG))
      exact isProjectiveFormRatio_congr e g hg hggen j₀ (by omega) h
    · refine ⟨1, le_rfl, fun μ hμ => ?_⟩
      have hXk : X k ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
        by_contra h
        exact hne ⟨⟨genericPoint Y, h⟩⟩
      have hmem : monomial μ (1 : K) ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
        have hle : Finsupp.single k 1 ≤ μ := Finsupp.single_le_iff.mpr hμ
        have hsum : μ - Finsupp.single k 1 + Finsupp.single k 1 = μ := tsub_add_cancel_of_le hle
        rw [← hsum, ← mul_one (1 : K), ← monomial_mul_monomial, ← X]
        exact Ideal.mul_mem_left (e (genericPoint Y)).asHomogeneousIdeal.toIdeal _ hXk
      rw [(projectiveFormRatio_eq_zero_iff e g hg hggen j₀ _ _ _).mpr hmem, zero_mul]
      exact isProjectiveFormRatio_zero e g hg hggen j₀ _
  choose M hM1 hM using hchart
  refine ⟨∑ k, (M k - 1) + 1, fun μ hμ => ?_⟩
  have hex : ∃ k, M k ≤ μ k := by
    by_contra h
    simp only [not_exists, not_le] at h
    have hle : μ.degree ≤ ∑ k, (M k - 1) := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.sum_le_sum fun k _ => by have := h k; omega
    omega
  obtain ⟨k, hk⟩ := hex
  exact hM k μ hk

section Base

variable [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Every form of degree at least N times a section of D·J is the section of a form. -/
theorem projectiveSection_form_mul_isFormRatio
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    ∃ N, ∀ N', N ≤ N' → ∀ (q : MvPolynomial (Fin n) K) (hq : q.IsHomogeneous N'),
      IsProjectiveFormRatio e g hg hggen j₀ (N' + D)
        (projectiveFormRatio e g hg hggen j₀ N' q hq *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
  classical
  obtain ⟨N, hN⟩ := projectiveSection_monomial_mul_isFormRatio e g hg hggen j₀ D s
  refine ⟨N, fun N' hN' q hq => ?_⟩
  have hq' : q = ∑ μ ∈ q.support, q.coeff μ • monomial μ (1 : K) := by
    conv_lhs => rw [q.as_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have key : ∀ T : Finset (Fin n →₀ ℕ), T ⊆ q.support →
      ∀ (hT : (∑ μ ∈ T, q.coeff μ • monomial μ (1 : K)).IsHomogeneous N'),
      IsProjectiveFormRatio e g hg hggen j₀ (N' + D)
        (projectiveFormRatio e g hg hggen j₀ N' (∑ μ ∈ T, q.coeff μ • monomial μ (1 : K)) hT *
          cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ hT
      simp only [Finset.sum_empty]
      rw [projectiveFormRatio_zero e g hg hggen j₀ N', zero_mul]
      exact isProjectiveFormRatio_zero e g hg hggen j₀ _
    | insert μ T hμT ih =>
      intro hsub hT
      have hμ : μ ∈ q.support := hsub (Finset.mem_insert_self μ T)
      have hdegμ : μ.degree = N' := by
        have := hq (mem_support_iff.mp hμ)
        rw [Finsupp.degree_eq_weight_one]
        exact this
      have hTsub : T ⊆ q.support := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hmono : (q.coeff μ • monomial μ (1 : K)).IsHomogeneous N' :=
        Submodule.smul_mem (homogeneousSubmodule (Fin n) K N') (q.coeff μ)
          (isHomogeneous_monomial 1 hdegμ)
      have hrest : (∑ x ∈ T, q.coeff x • monomial x (1 : K)).IsHomogeneous N' := by
        apply IsHomogeneous.sum
        intro x hx
        have hx' : x ∈ q.support := hTsub hx
        have := hq (mem_support_iff.mp hx')
        exact Submodule.smul_mem (homogeneousSubmodule (Fin n) K N') _
          (isHomogeneous_monomial 1 (by rw [Finsupp.degree_eq_weight_one]; exact this))
      rw [projectiveFormRatio_congr_poly e g hg hggen j₀ rfl (Finset.sum_insert hμT) hT
        (hmono.add hrest)]
      rw [projectiveFormRatio_add e g hg hggen j₀ N' _ _ hmono hrest, add_mul]
      refine isProjectiveFormRatio_add e g hg hggen j₀ ?_ (ih hTsub hrest)
      rw [projectiveFormRatio_smul e g hg hggen j₀ he N' (q.coeff μ) _
        (isHomogeneous_monomial 1 hdegμ), Algebra.smul_def, mul_assoc]
      have hμN : N ≤ μ.degree := by rw [hdegμ]; exact hN'
      have h := hN μ hμN
      rw [projectiveFormRatio_congr_poly e g hg hggen j₀ hdegμ rfl
        (isHomogeneous_monomial 1 rfl) (isHomogeneous_monomial 1 hdegμ)] at h
      exact isProjectiveFormRatio_smul e g hg hggen he j₀ (q.coeff μ)
        (isProjectiveFormRatio_congr e g hg hggen j₀ (by rw [hdegμ]) h)
  have hsumhom : (∑ μ ∈ q.support, q.coeff μ • monomial μ (1 : K)).IsHomogeneous N' := by
    rw [← hq']
    exact hq
  have := key q.support (Finset.Subset.refl _) hsumhom
  rwa [← projectiveFormRatio_congr_poly e g hg hggen j₀ rfl hq' hq hsumhom] at this

end Base

end MixedFujita
