/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierAmpleDefinition
public import MixedFujita.CartierCurveIntrinsicDegree

/-!
Nef divisors. A Cartier divisor on an integral scheme over a field is nef if its pullback to every
proper smooth integral curve mapping to it over the field has nonnegative degree. Over an
algebraically closed field this is the usual condition D · C ≥ 0 on integral curves C, through the
normalization of C. Nef divisors are closed under sums and multiples and depend only on the line
bundle, so a divisor and its sum with a principal divisor are nef together. Every ample divisor in
the projective sense is nef: a coordinate form not vanishing at a point of the image of the curve
gives a section of the hyperplane divisor that does not vanish there, and principal divisors have
degree zero on curves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Nef: the pullback to every proper smooth integral curve over K mapping to Y over K has
nonnegative degree. -/
def CartierIsNef (D : CartierDivisor Y) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
    topologicalKrullDim C = 1 → ∀ φ : C ⟶ Y,
      φ ≫ (Y ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) →
        0 ≤ cartierCurvePullbackDegree (K := K) D φ

variable {K}

theorem cartierIsNef_zero : CartierIsNef K (0 : CartierDivisor Y) := by
  intro C _ _ _ _ hC φ _
  rw [cartierCurvePullbackDegree_zero (K := K) hC]

theorem cartierIsNef_add {D E : CartierDivisor Y} (hD : CartierIsNef K D) (hE : CartierIsNef K E) :
    CartierIsNef K (D + E) := by
  intro C _ _ _ _ hC φ hφ
  rw [cartierCurvePullbackDegree_add (K := K) hC]
  exact add_nonneg (hD C hC φ hφ) (hE C hC φ hφ)

theorem cartierIsNef_nsmul {D : CartierDivisor Y} (hD : CartierIsNef K D) (j : ℕ) :
    CartierIsNef K (j • D) := by
  intro C _ _ _ _ hC φ hφ
  rw [cartierCurvePullbackDegree_nsmul (K := K) hC]
  exact mul_nonneg (by exact_mod_cast Nat.zero_le j) (hD C hC φ hφ)

/-- Nefness depends only on the line bundle. -/
theorem cartierIsNef_of_iso {D E : CartierDivisor Y} (e : D.sheaf ≅ E.sheaf)
    (hD : CartierIsNef K D) : CartierIsNef K E := by
  intro C _ _ _ _ hC φ hφ
  rw [← cartierCurvePullbackDegree_congr (K := K) D E φ e]
  exact hD C hC φ hφ

/-- The sheaf of a principal divisor is that of the zero divisor. -/
noncomputable def principalCartierSheafIsoZero (f : Y.functionFieldˣ) :
    (principalCartierDivisor Y f).sheaf ≅ (0 : CartierDivisor Y).sheaf :=
  (CartierDivisor.unitIsoSheafPrincipalCartierDivisor Y f).symm ≪≫
    CartierDivisor.unitIsoSheafPrincipalCartierDivisor Y 1 ≪≫
      eqToIso (by rw [principalCartierDivisor_one])

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- Principal divisors have degree zero on curves. -/
theorem cartierCurvePullbackDegree_principal {C : Scheme.{u}} [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1) (φ : C ⟶ Y)
    (f : Y.functionFieldˣ) :
    cartierCurvePullbackDegree (K := K) (principalCartierDivisor Y f) φ = 0 := by
  rw [cartierCurvePullbackDegree_congr (K := K) _ 0 φ (principalCartierSheafIsoZero f),
    cartierCurvePullbackDegree_zero (K := K) hC]

/-- Linearly equivalent divisors are nef together. -/
theorem cartierIsNef_add_principal_iff {D : CartierDivisor Y} (f : Y.functionFieldˣ) :
    CartierIsNef K (D + principalCartierDivisor Y f) ↔ CartierIsNef K D := by
  constructor
  · intro h C _ _ _ _ hC φ hφ
    have := h C hC φ hφ
    rwa [cartierCurvePullbackDegree_add (K := K) hC,
      cartierCurvePullbackDegree_principal (K := K) hC, add_zero] at this
  · intro h C _ _ _ _ hC φ hφ
    rw [cartierCurvePullbackDegree_add (K := K) hC,
      cartierCurvePullbackDegree_principal (K := K) hC, add_zero]
    exact h C hC φ hφ

section Hyperplane

variable {n : ℕ} (e : Y ⟶ polynomialProjectiveScheme n K) (g : MvPolynomial (Fin n) K)
  (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- A coordinate form gives a section of the hyperplane divisor that does not vanish on its chart. -/
theorem projectiveFormSection_X_mem_nonvanishingOpen
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (x : Y) {k : Fin n}
    (hk : x ∈ projectivePullbackCoordinateOpen e k) :
    x ∈ cartierSectionNonvanishingOpen (1 • projectiveHyperplaneCartier e g hg hggen)
      (projectiveFormSection e g hg hggen j₀ 1 (X k) (isHomogeneous_X K k)) := by
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x _
      (cartierLocalEquation_pow _ x _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j x hk) 1),
    projectiveFormSection_localCoefficient e g hg hggen j₀ j x hk 1 (X k) (isHomogeneous_X K k),
    projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_X_self, map_one, map_one]
  exact isUnit_one

end Hyperplane

/-- Every ample divisor in the projective sense is nef. -/
theorem cartierIsAmpleProj_isNef {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    CartierIsNef K A := by
  obtain ⟨m, hm, n, e, _, _, g, hg, hggen, f, hmA⟩ := hA
  intro C _ _ _ _ hC φ _
  have hJ : 0 ≤ cartierCurvePullbackDegree (K := K) (projectiveHyperplaneCartier e g hg hggen) φ := by
    obtain ⟨z⟩ : Nonempty C := inferInstance
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e (φ z))
    let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨φ z, hk⟩⟩⟩
    have h := cartierCurvePullbackDegree_nonneg_of_image_meets_nonvanishingOpen (K := K) hC
      (1 • projectiveHyperplaneCartier e g hg hggen) φ
      (projectiveFormSection e g hg hggen j₀ 1 (X k) (isHomogeneous_X K k))
      ⟨z, projectiveFormSection_X_mem_nonvanishingOpen e g hg hggen j₀ (φ z) hk⟩
    rwa [one_nsmul] at h
  have hdeg := congrArg (fun D => cartierCurvePullbackDegree (K := K) D φ) hmA
  rw [cartierCurvePullbackDegree_nsmul (K := K) hC, cartierCurvePullbackDegree_add (K := K) hC,
    cartierCurvePullbackDegree_principal (K := K) hC, add_zero] at hdeg
  by_contra hneg
  push Not at hneg
  have hpos : (0 : ℤ) < m := by exact_mod_cast hm
  have := mul_neg_of_pos_of_neg hpos hneg
  linarith

end MixedFujita
