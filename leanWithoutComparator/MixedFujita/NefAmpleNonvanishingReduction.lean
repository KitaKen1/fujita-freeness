/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefAmpleEffectiveComponentAmpleness
public import MixedFujita.NefCartierPullbackRepresentatives
public import MixedFujita.AmpleCartierPullbackRepresentatives
public import MixedFujita.EffectiveCartierCutDimension
public import MixedFujita.ZeroDimensionalCartierFreeness
public import MixedFujita.KltPerturbationNefAmple
public import MixedFujita.ProjectiveAllDimensionSectionBounds

/-! 元nef＋ample定理と和の正の倍数の普遍的非零切断存在の同値。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Universal nonvanishing of nef-plus-ample sums suffices for their
ORIGINAL ampleness. Strong dimension induction constructs ample restrictions
on all integral components of an actual effective zero divisor; no general
nef-plus-ample or numerical ampleness theorem is used as a premise. -/
theorem nef_add_ample_isAmpleProj_of_universal_sum_nonvanishing
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (h : ∀ (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
      [IsProper (X ↘ Spec (CommRingCat.of K))] (N A : CartierDivisor X),
      CartierIsNef K N → CartierIsAmpleProj K A →
        ∃ m : ℕ, 0 < m ∧ ∃ s : Γ((m • (N + A)).sheaf, ⊤), s ≠ 0)
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A) :
    CartierIsAmpleProj K (N + A) := by
  have go : ∀ n : ℕ, ∀ (T : Scheme.{u}) [IsIntegral T]
      [T.Over (Spec (CommRingCat.of K))] [IsProper (T ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim T = n → ∀ (P B : CartierDivisor T),
        CartierIsNef K P → CartierIsAmpleProj K B → CartierIsAmpleProj K (P + B) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T _ _ _ hdim P B hP hB
      cases n with
      | zero =>
        apply nef_add_ample_isAmpleProj_of_semiample K P B hP hB
        exact ⟨1, by omega, by simpa only [one_smul] using
          zeroDimensional_cartier_globallyGenerated (by simpa only [Nat.cast_zero] using hdim) (P + B)⟩
      | succ n =>
        obtain ⟨m, hm, s, hs⟩ := h T P B hP hB
        let D := P + B
        let G := cartierSectionZeroDivisor (m • D) s hs
        have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective (m • D) s hs
        let a : G.sheaf ≅ (m • D).sheaf :=
          cartierSheafPrincipalShiftIso (m • D) (cartierSectionUnit (m • D) s hs)
        apply nef_add_ample_isAmpleProj_of_effective_component_ample_representation
          K P B hP hB m hm G hG a
        intro Z i _ _ _
        let cut := (effectiveCartierIdealSheaf G hG).subschemeι
        let j := i ≫ cut
        let : IsClosedImmersion j := inferInstance
        let : Z.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (T ↘ Spec (CommRingCat.of K))⟩
        let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
        let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
          change IsProper (j ≫ (T ↘ Spec (CommRingCat.of K)))
          infer_instance
        obtain ⟨k, hdimZ⟩ : ∃ k : ℕ, topologicalKrullDim Z = k :=
          ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
        have hk : k < n + 1 := by
          have hbound : topologicalKrullDim Z ≤ n :=
            i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
              (effectiveCartierCut_topologicalKrullDim_le G hG n hdim.le)
          rw [hdimZ] at hbound
          have hkn : k ≤ n := by exact_mod_cast hbound
          omega
        obtain ⟨P', ⟨aP⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor P j
        obtain ⟨B', ⟨aB⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor B j
        have hP' : CartierIsNef K P' := cartierIsNef_of_pullback_representative K j P P' aP hP
        have hB' : CartierIsAmpleProj K B' :=
          cartierIsAmpleProj_of_finite_pullback_over K j B B' hB aB
        have hD' : CartierIsAmpleProj K (P' + B') := ih k hk Z hdimZ P' B' hP' hB'
        let b : (Scheme.Modules.pullback j).obj D.sheaf ≅ (P' + B').sheaf :=
          (Scheme.Modules.pullback j).mapIso (cartierTensorSheafIso P B).symm ≪≫
            cartierPullbackTensorIso P j B.sheaf ≪≫ tensorIso aP aB ≪≫ cartierTensorSheafIso P' B'
        let L := ((cartierSGALineBundle G).pullback cut).pullback i
        let c : L.toModules 1 ≅ (m • (P' + B')).sheaf :=
          (sgaLineBundlePullbackPowerIso ((cartierSGALineBundle G).pullback cut) i 1).symm ≪≫
            (Scheme.Modules.pullback i).mapIso (cartierPulledSheafSGAPowerOneIso G cut) ≪≫
              (Scheme.Modules.pullbackComp i cut).app G.sheaf ≪≫
                (Scheme.Modules.pullback j).mapIso a ≪≫
                  cartierPullbackGradedIso D j (P' + B') b m
        exact (cartierIsAmpleProj_iff_sga_of_iso K L (m • (P' + B')) c).mp
          (cartierIsAmpleProj_nsmul hD' (by omega))
  obtain ⟨n, hdim⟩ : ∃ n : ℕ, topologicalKrullDim X = n :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  exact go n X hdim N A hN hA


/-- The unchanged ORIGINAL nef-plus-ample statement is equivalent to
universal existence of ONE nonzero section of ONE positive multiple. The
nonvanishing assertion itself remains the remaining geometric input. -/
theorem nefAddAmpleStatement_iff_sum_nonvanishing :
    NefAddAmpleStatement.{u} ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
        [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
        (N A : CartierDivisor X), CartierIsNef K N → CartierIsAmpleProj K A →
          ∃ m : ℕ, 0 < m ∧ ∃ s : Γ((m • (N + A)).sheaf, ⊤), s ≠ 0 := by
  constructor
  · intro h K _ _ _ X _ _ _ N A hN hA
    obtain ⟨m, hm, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple
      (N + A) (h K X N A hN hA)
    obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgen
    exact ⟨m, by omega, s, hs⟩
  · intro h K _ _ _ X _ _ _ N A hN hA
    let : IsProper (X ↘ Spec (CommRingCat.of K)) :=
      isProper_structureMap_of_exists_ample_cartier ⟨A, hA⟩
    apply nef_add_ample_isAmpleProj_of_universal_sum_nonvanishing K ?_ N A hN hA
    intro T _ _ _ P B hP hB
    exact h K T P B hP hB

end MixedFujita
