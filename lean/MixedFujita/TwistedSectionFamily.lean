/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedSectionExtension
public import MixedFujita.CartierSectionProducts
public import MixedFujita.CartierTauProducts

/-!
Sections of a twisted divisor from forms (step 4). Generating opens of products and of
transported sections; the generating open of the section of m J given by a form Q is the
principal open X_Q. If g_β⁻¹ (F/g^d)^k is a section of A + k d J and A has the equation g_β on
X_F, this section generates on X_F. For a form Q of degree m its product with the section of Q is
a section of A + N J, N = k d + m, with rational function g_β⁻¹ (F/g^d)^k (Q/g^m); when F divides
Q its generating open is X_Q, and the ratio of two such sections is the ratio of the chart
functions of the two forms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- Cancelling the common factors of two twisted sections of the same degree. -/
theorem twisted_ratio_cancel {L : Type*} [Field L] (c p p' w : L) (hc : c ≠ 0) (hw : w ≠ 0) :
    (c * (p * w))⁻¹ * (c * (p' * w)) = p⁻¹ * p' := by
  rw [mul_inv, mul_inv]
  calc c⁻¹ * (p⁻¹ * w⁻¹) * (c * (p' * w)) = (c⁻¹ * c) * (w⁻¹ * w) * (p⁻¹ * p') := by ring
    _ = p⁻¹ * p' := by rw [inv_mul_cancel₀ hc, inv_mul_cancel₀ hw, one_mul, one_mul]

section General

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- A product of sections generates exactly where both factors generate. -/
theorem cartierSectionNonvanishingOpen_product (D E : CartierDivisor X) (s : Γ(D.sheaf, ⊤))
    (t : Γ(E.sheaf, ⊤)) :
    cartierSectionNonvanishingOpen (D + E) (cartierSectionProduct D E s t) =
      cartierSectionNonvanishingOpen D s ⊓ cartierSectionNonvanishingOpen E t := by
  ext x
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  change x ∈ cartierSectionNonvanishingOpen (D + E) (cartierSectionProduct D E s t) ↔
    x ∈ cartierSectionNonvanishingOpen D s ∧ x ∈ cartierSectionNonvanishingOpen E t
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient (D + E) _ x (f * g) (hf.mul hg),
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f hf,
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient E t x g hg,
    cartierSectionProduct_localCoefficient, IsUnit.mul_iff]

/-- Transport along an equality of divisors does not change the generating open. -/
theorem cartierSectionNonvanishingOpen_cast {D E : CartierDivisor X} (h : D = E)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionNonvanishingOpen E (cartierSectionCast h s) =
      cartierSectionNonvanishingOpen D s := by
  subst h
  rfl

end General

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (e : X ⟶ polynomialProjectiveScheme n K)
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- The rational function of a form relative to g, computed in a chart. -/
theorem projectiveFormRatio_eq_chart
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous D) :
    projectiveFormRatio e g hg hggen j₀ D Q hQ =
      X.germToFunctionField (projectivePullbackCoordinateOpen e j.val)
          (projectivePullbackHomogeneousEquation e j.val D Q hQ) *
        ((projectiveHyperplaneUnit e g hg hggen j : X.functionFieldˣ) : X.functionField)⁻¹ ^ D := by
  rw [projectiveFormRatio_chart_independent e g hg hggen j₀ j]
  unfold projectiveFormRatio
  rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]

/-- The section of m J given by a form of degree m ≥ 1 generates on the principal open of the
form. -/
theorem projectiveFormSection_nonvanishingOpen {m : ℕ} (hm : 0 < m)
    (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous m) :
    cartierSectionNonvanishingOpen (m • projectiveHyperplaneCartier e g hg hggen)
        (projectiveFormSection e g hg hggen j₀ m Q hQ) =
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) Q := by
  ext x
  obtain ⟨j, hxj⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  have hne : Nonempty (projectivePullbackCoordinateOpen e j) := ⟨⟨x, hxj⟩⟩
  change x ∈ cartierSectionNonvanishingOpen (m • projectiveHyperplaneCartier e g hg hggen)
      (projectiveFormSection e g hg hggen j₀ m Q hQ) ↔
    x ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) Q
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x
      (projectiveHyperplaneUnit e g hg hggen ⟨j, hne⟩ ^ m)
      (cartierLocalEquation_pow _ x _
        (projectiveHyperplane_isLocalEquationAt e g hg hggen ⟨j, hne⟩ x hxj) m),
    projectiveFormSection_localCoefficient e g hg hggen j₀ ⟨j, hne⟩ x hxj m Q hQ,
    ← X.mem_basicOpen _ x hxj, projectivePullbackHomogeneousEquation_basicOpen e j m Q hQ hm]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hxj, h⟩⟩

variable (A : CartierDivisor X) {d : ℕ} (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
  (gβ : X.functionFieldˣ)

/-- The extended generator g_β⁻¹ (F/g^d)^k generates on the principal open of F. -/
theorem twistedBaseSection_nonvanishingOpen_ge (hd : 0 < d)
    (hβ : ∀ y ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F,
      A.IsLocalEquationAt y gβ) {k : ℕ}
    (hmem : (rationalFunctionsEquiv (X := X) ⊤).symm
        (((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
          projectiveFormRatio e g hg hggen j₀ d F hF ^ k) ∈
        (A + (k * d) • projectiveHyperplaneCartier e g hg hggen).sections ⊤) :
    e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F ≤
      cartierSectionNonvanishingOpen (A + (k * d) • projectiveHyperplaneCartier e g hg hggen)
        (CartierDivisor.sectionMk _ hmem) := by
  intro y hy
  obtain ⟨j, hyj⟩ := polynomialProjective_exists_coordinate_chart n K (e y)
  have hne : Nonempty (projectivePullbackCoordinateOpen e j) := ⟨⟨y, hyj⟩⟩
  have hloc := (hβ y hy).mul
    (cartierLocalEquation_pow (projectiveHyperplaneCartier e g hg hggen) y _
      (projectiveHyperplane_isLocalEquationAt e g hg hggen ⟨j, hne⟩ y hyj) (k * d))
  have hyb : y ∈ X.basicOpen (projectivePullbackHomogeneousEquation e j d F hF) := by
    rw [projectivePullbackHomogeneousEquation_basicOpen e j d F hF hd]
    exact ⟨hyj, hy⟩
  have hunit := (X.mem_basicOpen _ y hyj).mp hyb
  have hc : cartierLocalCoefficient
        (A + (k * d) • projectiveHyperplaneCartier e g hg hggen) y _ hloc
        (CartierDivisor.sectionMk _ hmem) =
      X.presheaf.germ _ y hyj (projectivePullbackHomogeneousEquation e j d F hF) ^ k := by
    apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
    rw [cartierLocalCoefficient_image, cartierSectionRational_sectionMk, map_pow,
      X.algebraMap_germ_eq_germToFunctionField hyj, Units.val_mul, Units.val_pow_eq_pow_val,
      projectiveFormRatio_eq_chart e g hg hggen j₀ ⟨j, hne⟩ d F hF,
      twist_local_identity _ _ _ _ (Units.ne_zero _), Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero gβ), one_mul]
  change y ∈ cartierSectionNonvanishingOpen
    (A + (k * d) • projectiveHyperplaneCartier e g hg hggen) (CartierDivisor.sectionMk _ hmem)
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ y _ hloc, hc]
  exact hunit.pow k

variable {k m N : ℕ} (hN : k * d + m = N)
  (hmem : (rationalFunctionsEquiv (X := X) ⊤).symm
      (((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
        projectiveFormRatio e g hg hggen j₀ d F hF ^ k) ∈
      (A + (k * d) • projectiveHyperplaneCartier e g hg hggen).sections ⊤)

/-- The section of A + N J with rational function g_β⁻¹ (F/g^d)^k (Q/g^m). -/
noncomputable def twistedFormSection (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous m) :
    Γ((A + N • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
  cartierSectionCast
    (show A + (k * d) • projectiveHyperplaneCartier e g hg hggen +
        m • projectiveHyperplaneCartier e g hg hggen =
      A + N • projectiveHyperplaneCartier e g hg hggen by rw [← hN, add_nsmul, add_assoc])
    (cartierSectionProduct _ _ (CartierDivisor.sectionMk _ hmem)
      (projectiveFormSection e g hg hggen j₀ m Q hQ))

theorem twistedFormSection_rational (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous m) :
    cartierSectionRational (A + N • projectiveHyperplaneCartier e g hg hggen)
        (twistedFormSection e g hg hggen j₀ A F hF gβ hN hmem Q hQ) =
      ((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
          projectiveFormRatio e g hg hggen j₀ d F hF ^ k *
        projectiveFormRatio e g hg hggen j₀ m Q hQ := by
  rw [twistedFormSection, cartierSectionCast_rational, cartierSectionProduct_rational,
    projectiveFormSection_rational, cartierSectionRational_sectionMk]

/-- When F divides the form, the twisted section generates exactly on the principal open of the
form. -/
theorem twistedFormSection_nonvanishingOpen (hd : 0 < d)
    (hβ : ∀ y ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F,
      A.IsLocalEquationAt y gβ) (hm : 0 < m)
    (Q₁ : MvPolynomial (Fin n) K) (hQ : (F * Q₁).IsHomogeneous m) :
    cartierSectionNonvanishingOpen (A + N • projectiveHyperplaneCartier e g hg hggen)
        (twistedFormSection e g hg hggen j₀ A F hF gβ hN hmem (F * Q₁) hQ) =
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F ⊓
        e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) Q₁ := by
  rw [twistedFormSection, cartierSectionNonvanishingOpen_cast,
    cartierSectionNonvanishingOpen_product,
    projectiveFormSection_nonvanishingOpen e g hg hggen j₀ hm (F * Q₁) hQ, Proj.basicOpen_mul,
    Scheme.Hom.preimage_inf, ← inf_assoc]
  congr 1
  exact inf_eq_right.mpr
    (twistedBaseSection_nonvanishingOpen_ge e g hg hggen j₀ A F hF gβ hd hβ hmem)

/-- The ratio of two twisted sections is the ratio of the chart functions of the forms. -/
theorem twistedFormSection_ratio
    (hFgen : F ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (i : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (Q Q' : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous m) (hQ' : Q'.IsHomogeneous m) :
    (cartierSectionRational (A + N • projectiveHyperplaneCartier e g hg hggen)
        (twistedFormSection e g hg hggen j₀ A F hF gβ hN hmem Q hQ))⁻¹ *
      cartierSectionRational (A + N • projectiveHyperplaneCartier e g hg hggen)
        (twistedFormSection e g hg hggen j₀ A F hF gβ hN hmem Q' hQ') =
      (X.germToFunctionField (projectivePullbackCoordinateOpen e i.val)
          (projectivePullbackHomogeneousEquation e i.val m Q hQ))⁻¹ *
        X.germToFunctionField (projectivePullbackCoordinateOpen e i.val)
          (projectivePullbackHomogeneousEquation e i.val m Q' hQ') := by
  have hRF : projectiveFormRatio e g hg hggen j₀ d F hF ≠ 0 := fun h =>
    hFgen ((projectiveFormRatio_eq_zero_iff e g hg hggen j₀ d F hF).mp h)
  have hc : ((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
      projectiveFormRatio e g hg hggen j₀ d F hF ^ k ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (pow_ne_zero k hRF)
  have hw : ((projectiveHyperplaneUnit e g hg hggen i : X.functionFieldˣ) :
      X.functionField)⁻¹ ^ m ≠ 0 := pow_ne_zero m (inv_ne_zero (Units.ne_zero _))
  rw [twistedFormSection_rational, twistedFormSection_rational,
    projectiveFormRatio_eq_chart e g hg hggen j₀ i m Q hQ,
    projectiveFormRatio_eq_chart e g hg hggen j₀ i m Q' hQ']
  exact twisted_ratio_cancel _ _ _ _ hc hw

end MixedFujita
