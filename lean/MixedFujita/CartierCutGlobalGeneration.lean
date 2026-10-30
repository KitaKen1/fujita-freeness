/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePushforwardGlobalSections
public import MixedFujita.EffectiveCartierOffCutGenerators
public import MixedFujita.CartierCutEuler

/-! 実切断上の生成・切断全射・切断外標準切断から元の大域生成。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Global generation along an actual image, together with actual section
surjectivity and generators outside the image, gives original Cartier global generation. -/
theorem cartierIsGloballyGenerated_of_surjective_pushforward_and_off_image
    {X Y : Scheme.{u}} [IsIntegral X] (φ : Y ⟶ X) (D : CartierDivisor X)
    (f : D.sheaf ⟶ (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj D.sheaf))
    (hf : Function.Surjective (Scheme.Modules.Hom.app f ⊤))
    (hN : moduleIsGloballyGenerated ((Scheme.Modules.pullback φ).obj D.sheaf))
    (hoff : ∀ x : X, x ∉ Set.range φ → ∃ s : Γ(D.sheaf, ⊤), IsUnit
      (cartierLocalCoefficient D x (Classical.choose (D.exists_isLocalEquationAt x))
        (Classical.choose_spec (D.exists_isLocalEquationAt x)) s)) :
    CartierIsGloballyGenerated D := by
  intro x
  by_cases hx : x ∈ Set.range φ
  · obtain ⟨y, rfl⟩ := hx
    let C := cartierEquationOpenCover D
    let : Nonempty (C.U (φ y)) := ⟨⟨φ y, C.mem (φ y)⟩⟩
    let e := cartierOpenRestrictFrameIso D (C.U (φ y)) (C.equation (φ y)) (C.equation_eq (φ y))
    obtain ⟨s, hs⟩ := module_generating_section_at_image_of_surjective_pushforward φ D.sheaf f hf hN y
      (C.U (φ y)) (C.mem (φ y)) e
    rw [moduleRestrictFrameGlobalCoefficientGerm_cartier] at hs
    obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D (φ y)
      (Classical.choose (D.exists_isLocalEquationAt (φ y))) (C.equation (φ y))
      (Classical.choose_spec (D.exists_isLocalEquationAt (φ y)))
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (C.equation_eq (φ y)) (C.mem (φ y)))
    exact ⟨s, by rw [hv]; exact v.isUnit.mul hs⟩
  · exact hoff x hx


/-- For an effective Cartier divisor, actual cut generation and the actual
quotient section surjectivity supply original global generation of its multiple. -/
theorem effectiveCartier_nsmul_globallyGenerated_of_cut_surjection
    {X : Scheme.{u}} [IsIntegral X] (G : CartierDivisor X) (hG : G.IsEffective) (m : ℕ)
    (hcut : moduleIsGloballyGenerated
      ((Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj (m • G).sheaf))
    (hsurj : Function.Surjective (Scheme.Modules.Hom.app (cartierCutShortComplex (m • G) G hG).g ⊤)) :
    CartierIsGloballyGenerated (m • G) :=
  cartierIsGloballyGenerated_of_surjective_pushforward_and_off_image
    (effectiveCartierIdealSheaf G hG).subschemeι (m • G) (cartierCutShortComplex (m • G) G hG).g hsurj hcut
      (effectiveCartier_nsmul_has_generating_section_off_cut G hG m)

end MixedFujita
