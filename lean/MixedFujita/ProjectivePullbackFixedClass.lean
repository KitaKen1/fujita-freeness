/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePullbackRatios
public import MixedFujita.CartierSectionDivisor

/-!
Equal-degree homogeneous forms avoiding the generic point give linearly
equivalent actual Cartier divisors on the integral source. The ratio is
an actual nonzero global section of the reference divisor's module sheaf,
and its zero divisor is exactly the constructed effective Cartier cut.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {n : ℕ} {R : Type u} [CommRing R] {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n R)
  (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (d : ℕ)
  (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d)
  (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous d) (hd : 0 < d)
  (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

theorem projectivePullbackHomogeneousCartier_eq_principalShift :
    projectivePullbackHomogeneousCartier e d f hf hd hfgen =
      projectivePullbackHomogeneousCartier e d g hg hd hggen +
        principalCartierDivisor Y
          (projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen) := by
  obtain ⟨D, _, huniq⟩ := cartierDivisor_existsUnique_of_regularEquations Y
    (projectivePullbackNonemptyCoordinateOpen e)
    (projectivePullbackNonemptyCoordinateOpen_cover e)
    (fun j => projectivePullbackHomogeneousEquation e j.val d f hf)
    (fun j => projectivePullbackHomogeneousEquation_ne_zero e j.val d f hf hd hfgen)
    (fun j l => projectivePullbackHomogeneousEquation_overlap e j.val l.val d f hf)
  have hleft := huniq (projectivePullbackHomogeneousCartier e d f hf hd hfgen)
    (fun j => projectivePullbackHomogeneousCartier_restrict e d f hf hd hfgen j)
  apply hleft.trans
  symm
  apply huniq
  intro j
  rw [map_add]
  change ((projectivePullbackHomogeneousCartier e d g hg hd hggen) |_
      projectivePullbackNonemptyCoordinateOpen e j) +
    ((principalCartierDivisor Y
      (projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen)) |_
        projectivePullbackNonemptyCoordinateOpen e j) = _
  rw [projectivePullbackHomogeneousCartier_restrict,
    principalCartierDivisor_restrict,
    projectivePullbackHomogeneousRatio_chart_independent e k j d f hf g hg hd hfgen hggen]
  change rationalUnitClass Y (projectivePullbackNonemptyCoordinateOpen e j)
      (Additive.ofMul (projectivePullbackHomogeneousRationalUnit e j d g hg hd hggen)) +
      rationalUnitClass Y (projectivePullbackNonemptyCoordinateOpen e j)
        (Additive.ofMul (projectivePullbackHomogeneousRatio e j d f hf g hg hd hfgen hggen)) =
    rationalUnitClass Y (projectivePullbackNonemptyCoordinateOpen e j)
      (Additive.ofMul (projectivePullbackHomogeneousRationalUnit e j d f hf hd hfgen))
  rw [← map_add]
  congr 1
  change Additive.ofMul
      (projectivePullbackHomogeneousRationalUnit e j d g hg hd hggen *
        (projectivePullbackHomogeneousRationalUnit e j d f hf hd hfgen *
          (projectivePullbackHomogeneousRationalUnit e j d g hg hd hggen)⁻¹)) =
    Additive.ofMul (projectivePullbackHomogeneousRationalUnit e j d f hf hd hfgen)
  exact congrArg Additive.ofMul (mul_inv_cancel_comm_assoc
    (projectivePullbackHomogeneousRationalUnit e j d g hg hd hggen)
    (projectivePullbackHomogeneousRationalUnit e j d f hf hd hfgen))

noncomputable def projectivePullbackHomogeneousCartierSheafIso :
    (projectivePullbackHomogeneousCartier e d f hf hd hfgen).sheaf ≅
      (projectivePullbackHomogeneousCartier e d g hg hd hggen).sheaf :=
  eqToIso (congrArg CartierDivisor.sheaf
    (projectivePullbackHomogeneousCartier_eq_principalShift e k d f hf g hg hd hfgen hggen)) ≪≫
      cartierSheafPrincipalShiftIso _ _

theorem projectivePullbackHomogeneousRatio_mem_referenceSections :
    (rationalFunctionsEquiv (X := Y) ⊤).symm
        (projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen : Y.functionField) ∈
      (projectivePullbackHomogeneousCartier e d g hg hd hggen).sections ⊤ := by
  let q := projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen
  let D := projectivePullbackHomogeneousCartier e d g hg hd hggen
  have he : (D + principalCartierDivisor Y q).IsEffective := by
    rw [← projectivePullbackHomogeneousCartier_eq_principalShift e k d f hf g hg hd hfgen hggen]
    exact projectivePullbackHomogeneousCartier_isEffective e d f hf hd hfgen
  have hm := (cartierSections_mem_principalShift D q ⊤ _).mp
    (CartierDivisor.isEffective_iff_one_mem_sections.mp he)
  have hq : Scheme.Modules.Hom.app (rationalFunctionsMul Y (q : Y.functionField)) ⊤
      (Scheme.Modules.Hom.app (toRationalFunctions Y) ⊤ (1 : Γ(Y, ⊤))) =
        (rationalFunctionsEquiv (X := Y) ⊤).symm (q : Y.functionField) := by
    apply (rationalFunctionsEquiv (X := Y) ⊤).injective
    simp only [rationalFunctionsEquiv_rationalFunctionsMul_app,
      rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one,
      LinearEquiv.apply_symm_apply]
  exact hq ▸ hm

noncomputable def projectivePullbackHomogeneousReferenceSection :
    Γ((projectivePullbackHomogeneousCartier e d g hg hd hggen).sheaf, ⊤) :=
  CartierDivisor.sectionMk _
    (projectivePullbackHomogeneousRatio_mem_referenceSections e k d f hf g hg hd hfgen hggen)

theorem projectivePullbackHomogeneousReferenceSection_rational :
    cartierSectionRational (projectivePullbackHomogeneousCartier e d g hg hd hggen)
        (projectivePullbackHomogeneousReferenceSection e k d f hf g hg hd hfgen hggen) =
      (projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen : Y.functionField) := by
  rw [cartierSectionRational_apply, projectivePullbackHomogeneousReferenceSection,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem projectivePullbackHomogeneousReferenceSection_ne_zero :
    projectivePullbackHomogeneousReferenceSection e k d f hf g hg hd hfgen hggen ≠ 0 := by
  intro h
  have hz := projectivePullbackHomogeneousReferenceSection_rational e k d f hf g hg hd hfgen hggen
  rw [h, map_zero] at hz
  exact Units.ne_zero _ hz.symm

theorem projectivePullbackHomogeneousReferenceSection_unit :
    cartierSectionUnit (projectivePullbackHomogeneousCartier e d g hg hd hggen)
        (projectivePullbackHomogeneousReferenceSection e k d f hf g hg hd hfgen hggen)
        (projectivePullbackHomogeneousReferenceSection_ne_zero e k d f hf g hg hd hfgen hggen) =
      projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen := by
  apply Units.ext
  exact projectivePullbackHomogeneousReferenceSection_rational e k d f hf g hg hd hfgen hggen

theorem projectivePullbackHomogeneousReferenceSection_zeroDivisor :
    cartierSectionZeroDivisor (projectivePullbackHomogeneousCartier e d g hg hd hggen)
        (projectivePullbackHomogeneousReferenceSection e k d f hf g hg hd hfgen hggen)
        (projectivePullbackHomogeneousReferenceSection_ne_zero e k d f hf g hg hd hfgen hggen) =
      projectivePullbackHomogeneousCartier e d f hf hd hfgen := by
  rw [cartierSectionZeroDivisor, projectivePullbackHomogeneousReferenceSection_unit]
  exact (projectivePullbackHomogeneousCartier_eq_principalShift e k d f hf g hg hd hfgen hggen).symm

end MixedFujita
