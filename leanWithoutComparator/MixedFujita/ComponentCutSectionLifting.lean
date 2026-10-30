/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentSerreClosedCover
public import MixedFujita.CartierPulledCoherentTwist
public import MixedFujita.PulledLineBundlePowerIsomorphisms
public import MixedFujita.EffectiveCutEventualSectionLifting

/-! 実非被約切断の整成分上amplenessから全大冪切断持ち上げ。 See reports/check-237-component-ample-serre-section-lifting.json for the verified scope. Ampleness on actual integral components gives full coherent Serre vanishing on the original possibly nonreduced proper scheme and actual eventual quotient-section lifting on effective Cartier cuts over any field. Component ampleness is an explicit input. The cohomological converse, nonreduced cut global generation, universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Componentwise ampleness gives all-positive-degree eventual vanishing
for the actual pulled original E+mH on a possibly nonreduced source. -/
theorem proper_pulled_cartier_serreVanishing_of_component_ample
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (H E : CartierDivisor X)
    (hH : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents Y →
        (((cartierSGALineBundle H).pullback p).pullback i).IsAmple) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj (E + m • H).sheaf) (q + 1)) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let L := (cartierSGALineBundle H).pullback p
  let M := (Scheme.Modules.pullback p).obj E.sheaf
  let : SheafOfModules.isInvertible Y M := cartierPullbackSheaf_isInvertible E p
  let : M.IsCoherent := invertible_module_isCoherent _
  obtain ⟨m₀, hm₀⟩ := proper_sga_coherent_serreVanishing_of_component_ample K L hH M
  refine ⟨m₀, fun m hm q => ?_⟩
  let := hm₀ m hm q
  exact (actualCohomologyLinearEquivOfIso
    (cartierPulledSGAAffinePowerIso p H E L (cartierPulledSheafSGAPowerOneIso H p).symm m)
    (q + 1)).subsingleton


/-- Ampleness only on the actual integral components of an effective
Cartier cut supplies ALL large actual quotient-section lifts. No projective
power on the nonreduced cut or ambient H1 vanishing is assumed. -/
theorem proper_effectiveCut_eventually_sections_surjective_of_component_ample
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (E G : CartierDivisor X) (hG : G.IsEffective)
    (hcut : ∀ (Z : Scheme.{u})
      (i : Z ⟶ (effectiveCartierIdealSheaf G hG).subscheme)
      [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents (effectiveCartierIdealSheaf G hG).subscheme →
        (((cartierSGALineBundle G).pullback
          (effectiveCartierIdealSheaf G hG).subschemeι).pullback i).IsAmple) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Function.Surjective (Scheme.Modules.Hom.app (cartierSuccessiveCutShortComplex E G hG m).g ⊤) := by
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  apply proper_effectiveCut_eventually_sections_surjective_of_cut_h1_vanish K E G hG
  obtain ⟨m₀, hm₀⟩ := proper_pulled_cartier_serreVanishing_of_component_ample K i G E hcut
  exact ⟨m₀, fun m hm => hm₀ (m + 1) (by omega) 0⟩

end MixedFujita
