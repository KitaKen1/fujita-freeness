/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.CartierSectionPowers

/-! 実有効Cartier標準切断の全冪による切断外の生成。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The actual canonical section of an effective Cartier divisor. -/
noncomputable def effectiveCartierCanonicalSection {X : Scheme.{u}} [IsIntegral X]
    (G : CartierDivisor X) (hG : G.IsEffective) : Γ(G.sheaf, ⊤) :=
  Scheme.Modules.Hom.app (G.unitToSheaf hG) ⊤ (1 : Γ(X, ⊤))


/-- The effective divisor's canonical section is the rational function one. -/
theorem effectiveCartierCanonicalSection_rational {X : Scheme.{u}} [IsIntegral X]
    (G : CartierDivisor X) (hG : G.IsEffective) :
    cartierSectionRational G (effectiveCartierCanonicalSection G hG) = 1 := by
  rw [cartierSectionRational_apply]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) (G.unitToSheaf_ι hG)) (1 : Γ(X, ⊤))
  change Scheme.Modules.Hom.app G.sheafι ⊤ (effectiveCartierCanonicalSection G hG) =
    Scheme.Modules.Hom.app (toRationalFunctions X) ⊤ (1 : Γ(X, ⊤)) at h
  rw [h, Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one]


/-- Outside the actual Cartier cut, powers of its canonical section give
actual generators of every nonnegative Cartier multiple. -/
theorem effectiveCartier_nsmul_has_generating_section_off_cut {X : Scheme.{u}} [IsIntegral X]
    (G : CartierDivisor X) (hG : G.IsEffective) (m : ℕ) (x : X)
    (hx : x ∉ Set.range (effectiveCartierIdealSheaf G hG).subschemeι) :
    ∃ s : Γ((m • G).sheaf, ⊤), IsUnit (cartierLocalCoefficient (m • G) x
      (Classical.choose ((m • G).exists_isLocalEquationAt x))
      (Classical.choose_spec ((m • G).exists_isLocalEquationAt x)) s) := by
  have hx' : x ∉ (effectiveCartierIdealSheaf G hG).support := by
    intro hxS
    apply hx
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hxS
  obtain ⟨U, hxU, hne, a, ha, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective G hG x
  let : Nonempty U.1 := hne
  have hxa : x ∈ X.basicOpen a := by
    by_contra hn
    apply hx'
    rw [(effectiveCartierIdealSheaf G hG).mem_support_iff_of_mem (U := U) hxU,
      effectiveCartierIdealSheaf_ideal_eq_span G hG U a ha hEq,
      Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    exact hn
  let f := regularEquationRationalUnit X U.1 a ha
  have hf : G.IsLocalEquationAt x f := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxU
  let t := effectiveCartierCanonicalSection G hG
  have hcoef : cartierLocalCoefficient G x f hf t = X.presheaf.germ U.1 x hxU a := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [cartierLocalCoefficient_image, effectiveCartierCanonicalSection_rational, mul_one,
      regularEquationRationalUnit_val, X.algebraMap_germ_eq_germToFunctionField hxU a]
  have ht : IsUnit (cartierLocalCoefficient G x f hf t) := by
    rw [hcoef]
    exact (X.mem_basicOpen a x hxU).mp hxa
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (m • G) x
    (Classical.choose ((m • G).exists_isLocalEquationAt x)) (f ^ m)
    (Classical.choose_spec ((m • G).exists_isLocalEquationAt x)) (cartierLocalEquation_pow G x f hf m)
  refine ⟨cartierSectionPower G t m, ?_⟩
  rw [hv, cartierSectionPower_localCoefficient G x f hf t m]
  exact v.isUnit.mul (ht.pow m)

end MixedFujita
