/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAffineSectionAmpleness
public import MixedFujita.SGANaturalGlobalSectionEquivalence
public import MixedFujita.SGACartierTwistPowers

/-! 実直線束表示のSGA amplenessと元の射影Cartier amplenessの同値。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- The usual SGA affine-open ampleness of any ACTUAL line-bundle
presentation is equivalent to the ORIGINAL projective Cartier predicate. -/
theorem cartierIsAmpleProj_iff_sga_of_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L : X.LineBundle) (D : CartierDivisor X) (a : L.toModules 1 ≅ D.sheaf) :
    CartierIsAmpleProj K D ↔ L.IsAmple := by
  constructor
  · intro hD
    refine ⟨QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K)), ?_⟩
    intro x
    obtain ⟨m, hm, t, hxt, ht⟩ := cartierIsAmpleProj_affine_power_section_cover K D hD x
    let b := sgaLineBundleNatPowerCartierIso L D a m
    obtain ⟨s, hs⟩ := (sgaNaturalSectionToModule_bijective L m).surjective
      (Scheme.Modules.Hom.app b.inv ⊤ t)
    have hb : Scheme.Modules.Hom.app b.hom ⊤ (sgaNaturalSectionToModule L m s) = t := by
      rw [hs]
      exact ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) b.inv_hom_id) t
    have hV : L.nonvanishingLocus s = cartierSectionNonvanishingOpen (m • D) t := by
      rw [← sgaNaturalSectionToCartier_nonvanishingOpen L m (m • D) b s, hb]
    exact ⟨m, hm, s, by rw [hV]; exact hxt, by rw [hV]; exact ht⟩
  · intro hL
    apply cartierIsAmpleProj_of_affine_power_section_cover K D
    intro x
    obtain ⟨m, hm, s, hxs, hs⟩ := hL.2 x
    let b := sgaLineBundleNatPowerCartierIso L D a m
    refine ⟨m, hm, Scheme.Modules.Hom.app b.hom ⊤ (sgaNaturalSectionToModule L m s), ?_, ?_⟩
    · rwa [sgaNaturalSectionToCartier_nonvanishingOpen]
    · rwa [sgaNaturalSectionToCartier_nonvanishingOpen]


/-- In particular the canonical actual Cartier SGA presentation preserves
and reflects ampleness, with no separate embedding witness or vanishing input. -/
theorem cartierIsAmpleProj_iff_sga
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) :
    CartierIsAmpleProj K D ↔ (cartierSGALineBundle D).IsAmple :=
  cartierIsAmpleProj_iff_sga_of_iso K (cartierSGALineBundle D) D (cartierSGAModuleIso D).symm


/-- An actual sheaf isomorphism preserves ORIGINAL Cartier ampleness;
no principal-equivalence witness is required as input. -/
theorem cartierIsAmpleProj_iff_of_sheaf_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D E : CartierDivisor X) (a : D.sheaf ≅ E.sheaf) :
    CartierIsAmpleProj K D ↔ CartierIsAmpleProj K E :=
  (cartierIsAmpleProj_iff_sga K D).trans
    (cartierIsAmpleProj_iff_sga_of_iso K (cartierSGALineBundle D) E
      ((cartierSGAModuleIso D).symm ≪≫ a)).symm

end MixedFujita
