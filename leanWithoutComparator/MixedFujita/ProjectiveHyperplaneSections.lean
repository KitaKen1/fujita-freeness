/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectivePullbackRatios
public import MixedFujita.CartierSectionPowers
public import MixedFujita.CartierSectionDivisor

/-!
Actual sections of the multiples D·J of the hyperplane divisor J cut by one
degree-one form g on an integral source mapped to projective space. A degree-D
form F gives the rational function (F/X_j^D)(g/X_j)^(-D). It does not depend on
the nonempty chart j, because equal-degree chart equations share one explicit
transition unit and the degree-D unit is the D-th power of the degree-one unit.
It is an actual section of D·J whose local coefficient, for the D-th power of the
chart equation of g, is the germ of F/X_j^D. Forms vanishing at the generic point
are allowed; they give the zero section.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ} {R : Type u} [CommRing R] {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n R)

theorem projectivePullbackHomogeneousOverlapUnit_eq_pow (k j : Fin n) (D : ℕ) :
    projectivePullbackHomogeneousOverlapUnit e k j D =
      projectivePullbackHomogeneousOverlapUnit e k j 1 ^ D := by
  simp only [projectivePullbackHomogeneousOverlapUnit, projectiveHomogeneousOverlapUnit,
    pow_one, map_pow]

theorem units_pow_mul_mul_inv_pow {F : Type*} [Field F] (u : Fˣ) (a : F) (D : ℕ) :
    ((u ^ D : Fˣ) : F) * (a * ((u⁻¹ ^ D : Fˣ) : F)) = a := by
  rw [mul_left_comm, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one,
    mul_one]

variable [IsIntegral Y] (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The hyperplane divisor cut by the degree-one form g. -/
noncomputable abbrev projectiveHyperplaneCartier : CartierDivisor Y :=
  projectivePullbackHomogeneousCartier e 1 g hg Nat.one_pos hggen

/-- The chart equation of g, as a rational unit. -/
noncomputable abbrev projectiveHyperplaneUnit
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) : Y.functionFieldˣ :=
  projectivePullbackHomogeneousRationalUnit e j 1 g hg Nat.one_pos hggen

theorem projectiveHyperplane_isLocalEquationAt
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (z : Y) (hz : z ∈ projectivePullbackCoordinateOpen e j.val) :
    (projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt z
      (projectiveHyperplaneUnit e g hg hggen j) :=
  CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
    (projectivePullbackHomogeneousCartier_restrict e 1 g hg Nat.one_pos hggen j).symm hz

/-- The rational function of a degree-D form relative to g^D, computed in chart j. -/
noncomputable def projectiveFormRatio
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) : Y.functionField :=
  Y.germToFunctionField (projectivePullbackCoordinateOpen e j.val)
      (projectivePullbackHomogeneousEquation e j.val D F hF) *
    (((projectiveHyperplaneUnit e g hg hggen j)⁻¹ ^ D : Y.functionFieldˣ) : Y.functionField)

theorem projectiveFormRatio_chart_independent
    (j j' : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) :
    projectiveFormRatio e g hg hggen j D F hF = projectiveFormRatio e g hg hggen j' D F hF := by
  let := integral_opens_inter_nonempty Y (projectivePullbackCoordinateOpen e j.val)
    (projectivePullbackCoordinateOpen e j'.val)
  let W : Y.functionFieldˣ := Units.map (Y.germToFunctionField
    (projectivePullbackCoordinateOpen e j.val ⊓ projectivePullbackCoordinateOpen e j'.val)).hom
      (projectivePullbackHomogeneousOverlapUnit e j.val j'.val 1)
  have hF' : Y.germToFunctionField (projectivePullbackCoordinateOpen e j.val)
        (projectivePullbackHomogeneousEquation e j.val D F hF) =
      (W : Y.functionField) ^ D * Y.germToFunctionField (projectivePullbackCoordinateOpen e j'.val)
        (projectivePullbackHomogeneousEquation e j'.val D F hF) := by
    rw [← germToFunctionField_restrict Y
        (U := projectivePullbackCoordinateOpen e j.val)
        (V := projectivePullbackCoordinateOpen e j.val ⊓ projectivePullbackCoordinateOpen e j'.val)
        inf_le_left,
      ← germToFunctionField_restrict Y
        (U := projectivePullbackCoordinateOpen e j'.val)
        (V := projectivePullbackCoordinateOpen e j.val ⊓ projectivePullbackCoordinateOpen e j'.val)
        inf_le_right,
      projectivePullbackHomogeneousEquation_overlap_explicit e j.val j'.val D F hF, map_mul,
      projectivePullbackHomogeneousOverlapUnit_eq_pow, Units.val_pow_eq_pow_val, map_pow]
    rfl
  have hg' : projectiveHyperplaneUnit e g hg hggen j = W * projectiveHyperplaneUnit e g hg hggen j' :=
    projectivePullbackHomogeneousRationalUnit_overlap e j j' 1 g hg Nat.one_pos hggen
  unfold projectiveFormRatio
  rw [hF', hg']
  have hW : (W : Y.functionField) ≠ 0 := W.ne_zero
  simp only [mul_inv, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp
  rw [one_div, inv_pow, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero D hW), one_mul]

theorem projectiveFormRatio_mem_sections
    (k₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) :
    (rationalFunctionsEquiv (X := Y) ⊤).symm (projectiveFormRatio e g hg hggen k₀ D F hF) ∈
      (D • projectiveHyperplaneCartier e g hg hggen).sections ⊤ := by
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro z _
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n R (e z)
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨z, hk⟩⟩⟩
  have : Nonempty (projectivePullbackCoordinateOpen e k) := ⟨⟨z, hk⟩⟩
  refine ⟨projectiveHyperplaneUnit e g hg hggen j ^ D,
    cartierLocalEquation_pow _ z _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j z hk) D,
    ?_⟩
  rw [LinearEquiv.apply_symm_apply, projectiveFormRatio_chart_independent e g hg hggen k₀ j]
  refine ⟨Y.presheaf.germ (projectivePullbackCoordinateOpen e k) z hk
    (projectivePullbackHomogeneousEquation e k D F hF), ?_⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField hk]
  unfold projectiveFormRatio
  exact (units_pow_mul_mul_inv_pow _ _ D).symm

/-- The actual section of D·J given by a degree-D form. -/
noncomputable def projectiveFormSection
    (k₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) :
    Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (projectiveFormRatio_mem_sections e g hg hggen k₀ D F hF)

theorem projectiveFormSection_rational
    (k₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) :
    cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen)
        (projectiveFormSection e g hg hggen k₀ D F hF) =
      projectiveFormRatio e g hg hggen k₀ D F hF := by
  simp only [projectiveFormSection, cartierSectionRational_apply,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

/-- The local coefficient of the section of a degree-D form, for the D-th power of the
chart equation of g, is the germ of F/X_j^D. -/
theorem projectiveFormSection_localCoefficient
    (k₀ j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (x : Y) (hx : x ∈ projectivePullbackCoordinateOpen e j.val) (D : ℕ)
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous D) :
    cartierLocalCoefficient (D • projectiveHyperplaneCartier e g hg hggen) x
        (projectiveHyperplaneUnit e g hg hggen j ^ D)
        (cartierLocalEquation_pow _ x _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j x hx) D)
        (projectiveFormSection e g hg hggen k₀ D F hF) =
      Y.presheaf.germ _ x hx (projectivePullbackHomogeneousEquation e j.val D F hF) := by
  apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
  rw [cartierLocalCoefficient_image, projectiveFormSection_rational,
    projectiveFormRatio_chart_independent e g hg hggen k₀ j,
    Y.algebraMap_germ_eq_germToFunctionField hx]
  unfold projectiveFormRatio
  exact units_pow_mul_mul_inv_pow _ _ D

end MixedFujita
