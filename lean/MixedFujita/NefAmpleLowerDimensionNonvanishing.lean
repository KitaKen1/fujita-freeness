/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefAmpleNonvanishingReduction

/-! 下の次元のnef＋ampleと一つの非零切断から元ampleness。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Lower-dimensional original nef-plus-ample ampleness and ONE actual
nonzero positive-multiple section imply original ampleness in the next dimension. -/
theorem nef_add_ample_isAmpleProj_of_lower_dimension_and_nonzero_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (hIH : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
      [IsProper (Z ↘ Spec (CommRingCat.of K))], topologicalKrullDim Z ≤ n →
        ∀ (P B : CartierDivisor Z), CartierIsNef K P → CartierIsAmpleProj K B →
          CartierIsAmpleProj K (P + B))
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A)
    (m : ℕ) (hm : 0 < m) (s : Γ((m • (N + A)).sheaf, ⊤)) (hs : s ≠ 0) :
    CartierIsAmpleProj K (N + A) := by
  let D := N + A
  let G := cartierSectionZeroDivisor (m • D) s hs
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective (m • D) s hs
  let a : G.sheaf ≅ (m • D).sheaf :=
    cartierSheafPrincipalShiftIso (m • D) (cartierSectionUnit (m • D) s hs)
  apply nef_add_ample_isAmpleProj_of_effective_component_ample_representation
    K N A hN hA m hm G hG a
  intro Z i _ _ _
  let cut := (effectiveCartierIdealSheaf G hG).subschemeι
  let j := i ≫ cut
  let : IsClosedImmersion j := inferInstance
  let : Z.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    change IsProper (j ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  have hdimZ : topologicalKrullDim Z ≤ n :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (effectiveCartierCut_topologicalKrullDim_le G hG n hdim)
  obtain ⟨N', ⟨aP⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor N j
  obtain ⟨A', ⟨aB⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor A j
  have hN' : CartierIsNef K N' := cartierIsNef_of_pullback_representative K j N N' aP hN
  have hA' : CartierIsAmpleProj K A' :=
    cartierIsAmpleProj_of_finite_pullback_over K j A A' hA aB
  have hD' : CartierIsAmpleProj K (N' + A') := hIH Z hdimZ N' A' hN' hA'
  let b : (Scheme.Modules.pullback j).obj D.sheaf ≅ (N' + A').sheaf :=
    (Scheme.Modules.pullback j).mapIso (cartierTensorSheafIso N A).symm ≪≫
      cartierPullbackTensorIso N j A.sheaf ≪≫ tensorIso aP aB ≪≫ cartierTensorSheafIso N' A'
  let L := ((cartierSGALineBundle G).pullback cut).pullback i
  let c : L.toModules 1 ≅ (m • (N' + A')).sheaf :=
    (sgaLineBundlePullbackPowerIso ((cartierSGALineBundle G).pullback cut) i 1).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (cartierPulledSheafSGAPowerOneIso G cut) ≪≫
        (Scheme.Modules.pullbackComp i cut).app G.sheaf ≪≫
          (Scheme.Modules.pullback j).mapIso a ≪≫
            cartierPullbackGradedIso D j (N' + A') b m
  exact (cartierIsAmpleProj_iff_sga_of_iso K L (m • (N' + A')) c).mp
    (cartierIsAmpleProj_nsmul hD' (by omega))

end MixedFujita
