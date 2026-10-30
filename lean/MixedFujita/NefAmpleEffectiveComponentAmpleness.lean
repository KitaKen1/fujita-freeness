/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ComponentCutSemiampleness
public import MixedFujita.SemiamplePositiveCurveAmpleness

/-! nef＋ampleの正の有効代表元・切断整成分amplenessから元ampleness。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- An effective representative of a positive nef-plus-ample multiple
needs ampleness only on its integral cut components. Source semiampleness,
generation multiples and finiteness of the section map are all internal. -/
theorem nef_add_ample_isAmpleProj_of_effective_component_ample_representation
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A)
    (m : ℕ) (hm : 0 < m) (G : CartierDivisor X) (hG : G.IsEffective)
    (a : G.sheaf ≅ (m • (N + A)).sheaf)
    (hcut : ∀ (Z : Scheme.{u})
      (i : Z ⟶ (effectiveCartierIdealSheaf G hG).subscheme)
      [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents (effectiveCartierIdealSheaf G hG).subscheme →
        (((cartierSGALineBundle G).pullback
          (effectiveCartierIdealSheaf G hG).subschemeι).pullback i).IsAmple) :
    CartierIsAmpleProj K (N + A) := by
  obtain ⟨q, hq, hgen⟩ := proper_effectiveCartier_semiample_of_component_ample K G hG hcut
  have hgen' : CartierIsGloballyGenerated (q • (m • (N + A))) :=
    (cartierIsGloballyGenerated_iff_module _).mpr
      (moduleIsGloballyGenerated_of_iso (cartierNaturalMultiplesSheafIsoOfIso G _ a q)
        ((cartierIsGloballyGenerated_iff_module _).mp hgen))
  apply nef_add_ample_isAmpleProj_of_semiample K N A hN hA
  exact ⟨q * m, Nat.mul_pos hq hm, by simpa only [smul_smul] using hgen'⟩

end MixedFujita
