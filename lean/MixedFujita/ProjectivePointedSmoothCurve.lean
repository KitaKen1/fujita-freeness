/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedOpenHitting

/-! Induction on the ordinary geometric dimension constructs an actual closed immersion of a proper smooth integral curve through the prescribed closed point and meeting any specified nonempty open. No supplied curve or flag is used. A fixed-Cartier-class flag certificate is not asserted. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
theorem polynomialProjective_exists_pointed_proper_smooth_curve
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (x : Y) (hx : IsClosed {x}) (U : Y.Opens) (hU : Nonempty U) :
    ∃ (C : Scheme.{u}) (i : C ⟶ Y), IsClosedImmersion i ∧ IsIntegral C ∧
      Smooth (i ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
      IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
      topologicalKrullDim C = 1 ∧ (∃ c : C, i c = x) ∧ ∃ c : C, i c ∈ U := by
  induction d using Nat.strong_induction_on generalizing Y with
  | h d ih =>
    have := polynomialProjective_closedImmersion_isProper_over_field e he
    by_cases hd1 : d = 1
    · subst d
      obtain ⟨u⟩ := hU
      exact ⟨Y, 𝟙 Y, inferInstance, inferInstance,
        by simpa only [Category.id_comp] using (inferInstance : Smooth (Y ↘ Spec (CommRingCat.of K))),
        by simpa only [Category.id_comp] using (inferInstance : IsProper (Y ↘ Spec (CommRingCat.of K))),
        hdim, ⟨x, rfl⟩, ⟨u.val, u.property⟩⟩
    · have hd2 : 2 ≤ d := by omega
      obtain ⟨F, hgeneric, _, _, _, T, j, hj, hjc, hT, hTs, hTp, hdimT,
          ⟨t, ht⟩, ⟨u, hu⟩⟩ :=
        polynomialProjective_pointed_proper_integral_smooth_component_hits_open e he d hdim
          hd2 x hx U hU ∅ Set.finite_empty (Set.notMem_empty x)
      let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
      let ρ := j ≫ I.subschemeι
      let := hjc
      let := hT
      have : IsClosedImmersion ρ := inferInstance
      let : T.Over (Spec (CommRingCat.of K)) := ⟨ρ ≫ (Y ↘ Spec (CommRingCat.of K))⟩
      have : Smooth (T ↘ Spec (CommRingCat.of K)) := by
        change Smooth (ρ ≫ (Y ↘ Spec (CommRingCat.of K)))
        simpa only [ρ, Category.assoc] using hTs
      have heT : (ρ ≫ e) ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K) := by
        change (ρ ≫ e) ≫ polynomialProjectiveToBase n K = ρ ≫ (Y ↘ Spec (CommRingCat.of K))
        rw [Category.assoc, he]
      have htclosed : IsClosed ({t} : Set T) := by
        have hpre : ρ ⁻¹' {x} = {t} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun hz => ρ.isClosedEmbedding.injective (hz.trans ht.symm), fun hz => hz ▸ ht⟩
        rw [← hpre]
        exact hx.preimage ρ.continuous
      let V := ρ ⁻¹ᵁ U
      have hV : Nonempty V := ⟨⟨u, hu⟩⟩
      obtain ⟨C, i, hic, hC, hCs, hCp, hCd, ⟨c, hcx⟩, ⟨v, hcv⟩⟩ :=
        ih (d - 1) (by omega) (ρ ≫ e) heT hdimT (by omega) t htclosed V hV
      let := hic
      have hs : Smooth ((i ≫ ρ) ≫ (Y ↘ Spec (CommRingCat.of K))) := by
        change Smooth (i ≫ ρ ≫ (Y ↘ Spec (CommRingCat.of K))) at hCs
        simpa only [Category.assoc] using hCs
      have hp : IsProper ((i ≫ ρ) ≫ (Y ↘ Spec (CommRingCat.of K))) := by
        change IsProper (i ≫ ρ ≫ (Y ↘ Spec (CommRingCat.of K))) at hCp
        simpa only [Category.assoc] using hCp
      refine ⟨C, i ≫ ρ, inferInstance, hC, hs, hp, hCd, ⟨c, ?_⟩, ⟨v, hcv⟩⟩
      rw [Scheme.Hom.comp_apply, hcx]
      exact ht

end MixedFujita
