/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleGlobalSectionMonomorphisms
public import MixedFujita.SGACartierTwistPowers

/-! 一つの実正則切断から全負冪・任意可逆係数の単射。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- One actual regular line section supplies actual structure-sheaf
injections into every natural power, using exact twist equivalences. -/
theorem sga_exists_mono_natural_powers_of_mono_one
    {X : Scheme.{u}} (L : X.LineBundle)
    (h : ∃ f : CohomologyAux.unitModule X ⟶ L.toModules 1, Mono f) :
    ∀ j : ℕ, ∃ f : CohomologyAux.unitModule X ⟶ L.toModules (j : ℤ), Mono f := by
  obtain ⟨f, hf⟩ := h
  let := hf
  intro j
  induction j with
  | zero => exact ⟨(sgaLineBundleZeroPowerIso L).inv, inferInstance⟩
  | succ j ih =>
    obtain ⟨g, hg⟩ := ih
    let := hg
    let a := sgaTwistUnitIso L 1
    let b : L.twist (L.toModules (j : ℤ)) 1 ≅ L.toModules ((j + 1 : ℕ) : ℤ) :=
      (sgaTwistTensorIso L (L.toModules (j : ℤ)) 1).symm ≪≫
        sgaLineBundleTensorPowerIso L 1 j ≪≫
          eqToIso (congrArg L.toModules (by omega))
    exact ⟨f ≫ a.inv ≫ (Scheme.LineBundle.twistFunctor X L 1).map g ≫ b.hom, inferInstance⟩


/-- Twisting the constructed positive-power injection by its inverse
gives an actual injection from every negative natural power to O_X. -/
theorem sga_exists_mono_negative_powers_of_mono_one
    {X : Scheme.{u}} (L : X.LineBundle)
    (h : ∃ f : CohomologyAux.unitModule X ⟶ L.toModules 1, Mono f)
    (j : ℕ) : ∃ f : L.toModules (-(j : ℤ)) ⟶ CohomologyAux.unitModule X, Mono f := by
  obtain ⟨g, hg⟩ := sga_exists_mono_natural_powers_of_mono_one L h j
  let := hg
  let a := sgaTwistUnitIso L (-(j : ℤ))
  let b : L.twist (L.toModules (j : ℤ)) (-(j : ℤ)) ≅ CohomologyAux.unitModule X :=
    (sgaTwistTensorIso L (L.toModules (j : ℤ)) (-(j : ℤ))).symm ≪≫
      sgaLineBundleTensorPowerIso L (-(j : ℤ)) j ≪≫
        eqToIso (congrArg L.toModules (neg_add_cancel (j : ℤ))) ≪≫ sgaLineBundleZeroPowerIso L
  exact ⟨a.inv ≫ (Scheme.LineBundle.twistFunctor X L (-(j : ℤ))).map g ≫ b.hom, inferInstance⟩


/-- Any fixed invertible coefficient preserves those actual injections:
negative twists inject into the unmodified coefficient, for ALL powers. -/
theorem sga_exists_mono_negative_twist_of_mono_one
    {X : Scheme.{u}} (L F : X.LineBundle)
    (h : ∃ f : CohomologyAux.unitModule X ⟶ L.toModules 1, Mono f)
    (n : ℤ) (j : ℕ) :
    ∃ f : L.twist (F.toModules n) (-(j : ℤ)) ⟶ F.toModules n, Mono f := by
  obtain ⟨g, hg⟩ := sga_exists_mono_negative_powers_of_mono_one L h j
  let := hg
  let a : L.twist (F.toModules n) (-(j : ℤ)) ≅ F.twist (L.toModules (-(j : ℤ))) n :=
    (sgaTwistTensorIso L (F.toModules n) (-(j : ℤ))).symm ≪≫
      β_ _ _ ≪≫ sgaTwistTensorIso F (L.toModules (-(j : ℤ))) n
  exact ⟨a.hom ≫ (Scheme.LineBundle.twistFunctor X F n).map g ≫ (sgaTwistUnitIso F n).hom,
    inferInstance⟩


/-- Generated ambient Cartier lines give actual negative-twist injections
on any noetherian source. Both the regular section and all maps are internal. -/
theorem cartier_sga_pullback_exists_mono_negative_twist
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsNoetherian Y]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (F : Y.LineBundle) (n : ℤ) (j : ℕ) :
    ∃ f : ((cartierSGALineBundle H).pullback p).twist (F.toModules n) (-(j : ℤ)) ⟶ F.toModules n,
      Mono f := by
  obtain ⟨s, hs⟩ := cartier_sga_pullback_exists_mono_global_section K p H hH
  exact sga_exists_mono_negative_twist_of_mono_one _ F
    ⟨moduleGlobalSectionHom _ (sgaNaturalSectionToModule _ 1 s), hs⟩ n j

end MixedFujita
