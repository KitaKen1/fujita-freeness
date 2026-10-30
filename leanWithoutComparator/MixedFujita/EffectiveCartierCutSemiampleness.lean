/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCutGlobalGeneration
public import MixedFujita.SGAProjectivePowerGlobalGeneration
public import MixedFujita.EffectiveCutEventualSectionLifting

/-! 実切断の正の射影冪表示から源の全大可除倍の生成と元semiampleness。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A degree-one isomorphism of a pulled Cartier bundle gives isomorphisms
for every original natural power on an arbitrary, possibly nonreduced source. -/
noncomputable def cartierPulledSGANatPowerIso {X Y : Scheme.{u}} [IsIntegral X]
    (p : Y ⟶ X) (H : CartierDivisor X) (M : Y.LineBundle)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ M.toModules 1) (j : ℕ) :
    (Scheme.Modules.pullback p).obj (j • H).sheaf ≅ M.toModules (j : ℤ) := by
  let L := (cartierSGALineBundle H).pullback p
  let b : L.toModules 1 ≅ M.toModules 1 :=
    (sgaLineBundlePullbackPowerIso (cartierSGALineBundle H) p 1).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (cartierSGAModuleIso H).symm ≪≫ a
  exact (Scheme.Modules.pullback p).mapIso (cartierSGANatPowerIso H j).symm ≪≫
    sgaLineBundlePullbackPowerIso (cartierSGALineBundle H) p j ≪≫ sgaLineBundleNatPowerIsoOfIso L M b j


/-- One positive hyperplane power on the actual effective cut gives
original global generation for all sufficiently large divisible multiples
on the proper integral ambient scheme. All lifting thresholds are internal. -/
theorem proper_effectiveCartier_eventually_divisible_globallyGenerated_of_cut_projective_power
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective) (d : ℕ) (hd : 0 < d) (r : ℕ)
    (e : (effectiveCartierIdealSheaf G hG).subscheme ⟶ polynomialProjectiveScheme (r + 1) K)
    [IsClosedImmersion e]
    (a : (Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj (d • G).sheaf ≅
      ((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules 1) :
    ∃ j₀ : ℕ, 0 < j₀ ∧ ∀ j : ℕ, j₀ ≤ j → CartierIsGloballyGenerated ((j * d) • G) := by
  obtain ⟨m₀, hm₀⟩ := proper_effectiveCut_eventually_sections_surjective_of_projective_power K 0 G hG d hd r e a
  refine ⟨m₀ + 1, by omega, ?_⟩
  intro j hj
  let q := j * d
  have hq : j ≤ q := by dsimp [q]; nlinarith
  have hqp : 0 < q := by omega
  have hpred : q - 1 + 1 = q := by omega
  have hsurj := hm₀ (q - 1) (by omega)
  change Function.Surjective (Scheme.Modules.Hom.app (cartierCutShortComplex (0 + (q - 1 + 1) • G) G hG).g ⊤) at hsurj
  have hsurj' : Function.Surjective (Scheme.Modules.Hom.app (cartierCutShortComplex (q • G) G hG).g ⊤) := by
    have he : (0 : CartierDivisor X) + (q - 1 + 1) • G = q • G := by rw [zero_add, hpred]
    exact he ▸ hsurj
  apply effectiveCartier_nsmul_globallyGenerated_of_cut_surjection G hG q ?_ hsurj'
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let M := (projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e
  let b : (Scheme.Modules.pullback i).obj (q • G).sheaf ≅ M.toModules (j : ℤ) :=
    (Scheme.Modules.pullback i).mapIso
      (eqToIso (congrArg CartierDivisor.sheaf (show q • G = j • (d • G) by rw [smul_smul]))) ≪≫
        cartierPulledSGANatPowerIso i (d • G) M a j
  exact moduleIsGloballyGenerated_of_iso b.symm
    (moduleIsGloballyGenerated_projective_hyperplane_power K r e j (by omega))


/-- The effective divisor is semiample in the original Cartier definition;
the positive multiple and all section lifts are constructed internally. -/
theorem proper_effectiveCartier_semiample_of_cut_projective_power
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective) (d : ℕ) (hd : 0 < d) (r : ℕ)
    (e : (effectiveCartierIdealSheaf G hG).subscheme ⟶ polynomialProjectiveScheme (r + 1) K)
    [IsClosedImmersion e]
    (a : (Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj (d • G).sheaf ≅
      ((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules 1) :
    ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • G) := by
  obtain ⟨j₀, hj₀, hgen⟩ :=
    proper_effectiveCartier_eventually_divisible_globallyGenerated_of_cut_projective_power K G hG d hd r e a
  exact ⟨j₀ * d, Nat.mul_pos hj₀ hd, hgen j₀ le_rfl⟩

end MixedFujita
