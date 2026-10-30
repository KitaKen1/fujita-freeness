/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentSerreSemiampleness
public import MixedFujita.ComponentCutSectionLifting
public import MixedFujita.EffectiveCartierCutSemiampleness

/-! 実有効Cartier切断の整成分amplenessから元semiampleness。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Component ampleness constructs a positive generated power on the
actual proper source, including all its nilpotents and reducible components. -/
theorem proper_sga_semiample_of_component_ample
    (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (L : Y.LineBundle)
    (hL : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents Y → (L.pullback i).IsAmple) :
    ∃ q : ℕ, 0 < q ∧ moduleIsGloballyGenerated (L.toModules (q : ℤ)) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  apply sga_semiample_of_coherent_serre L
  intro M _
  exact proper_sga_coherent_serreVanishing_of_component_ample K L hL M


/-- Ampleness only on the integral components of the actual effective
Cartier cut constructs a common progression of globally generated ambient
multiples. The cut's positive generated power is constructed internally. -/
theorem proper_effectiveCartier_eventually_divisible_globallyGenerated_of_component_ample
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective)
    (hcut : ∀ (Z : Scheme.{u})
      (i : Z ⟶ (effectiveCartierIdealSheaf G hG).subscheme)
      [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents (effectiveCartierIdealSheaf G hG).subscheme →
        (((cartierSGALineBundle G).pullback
          (effectiveCartierIdealSheaf G hG).subschemeι).pullback i).IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ j₀ : ℕ, 0 < j₀ ∧
      ∀ j : ℕ, j₀ ≤ j → CartierIsGloballyGenerated ((j * d) • G) := by
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let L := (cartierSGALineBundle G).pullback i
  obtain ⟨d, hd, hgen⟩ := proper_sga_semiample_of_component_ample K L hcut
  obtain ⟨m₀, hm₀⟩ := proper_effectiveCut_eventually_sections_surjective_of_component_ample K 0 G hG hcut
  refine ⟨d, hd, m₀ + 1, by omega, ?_⟩
  intro j hj
  let q := j * d
  have hq : j ≤ q := by dsimp [q]; nlinarith
  have hqp : 0 < q := by omega
  have hpred : q - 1 + 1 = q := by omega
  have hsurj := hm₀ (q - 1) (by omega)
  change Function.Surjective (Scheme.Modules.Hom.app
    (cartierCutShortComplex (0 + (q - 1 + 1) • G) G hG).g ⊤) at hsurj
  have hsurj' : Function.Surjective (Scheme.Modules.Hom.app (cartierCutShortComplex (q • G) G hG).g ⊤) := by
    have he : (0 : CartierDivisor X) + (q - 1 + 1) • G = q • G := by rw [zero_add, hpred]
    exact he ▸ hsurj
  apply effectiveCartier_nsmul_globallyGenerated_of_cut_surjection G hG q ?_ hsurj'
  let b : (Scheme.Modules.pullback i).obj (q • G).sheaf ≅ L.toModules (q : ℤ) :=
    cartierPulledSGANatPowerIso i G L (cartierPulledSheafSGAPowerOneIso G i).symm q
  apply moduleIsGloballyGenerated_of_iso b.symm
  simpa only [q, Nat.mul_comm j d] using
    moduleIsGloballyGenerated_sga_positive_multiples L d hgen j (by omega)


/-- Effective Cartier divisors with ample restrictions on the integral
components of their actual cut are semiample in the ORIGINAL definition. -/
theorem proper_effectiveCartier_semiample_of_component_ample
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (G : CartierDivisor X) (hG : G.IsEffective)
    (hcut : ∀ (Z : Scheme.{u})
      (i : Z ⟶ (effectiveCartierIdealSheaf G hG).subscheme)
      [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents (effectiveCartierIdealSheaf G hG).subscheme →
        (((cartierSGALineBundle G).pullback
          (effectiveCartierIdealSheaf G hG).subschemeι).pullback i).IsAmple) :
    ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • G) := by
  obtain ⟨d, hd, j₀, hj₀, hgen⟩ :=
    proper_effectiveCartier_eventually_divisible_globallyGenerated_of_component_ample K G hG hcut
  exact ⟨j₀ * d, Nat.mul_pos hj₀ hd, hgen j₀ le_rfl⟩

end MixedFujita
