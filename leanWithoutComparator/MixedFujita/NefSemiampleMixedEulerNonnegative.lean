/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefCurveMixedEulerNonnegative
public import MixedFujita.SemiampleMixedPowerIitakaPattern

/-! 全次元の元nef1本と任意semiample族の実混合Euler非負性。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- ONE ORIGINAL curve-test nef factor and ANY original semiample tail
have nonnegative actual top mixed coefficient, even on singular integral
projective sources. No semiample hypothesis is placed on the nef factor. -/
theorem proper_nef_semiample_cartierMixedEuler_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) :
    ∀ (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
      [IsProper (X ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim X ≤ (n + 1 : ℕ) →
      (∃ J : CartierDivisor X, CartierIsAmpleProj K J) →
      ∀ (N : CartierDivisor X), CartierIsNef K N →
      ∀ (D : List (CartierDivisor X)), D.length = n →
        (∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H)) →
        ∀ E : CartierDivisor X, 0 ≤ cartierMixedEulerDifference K (N :: D) E := by
  induction n with
  | zero =>
    intro X _ _ _ hdim hProj N hN D hlen hD E
    have hnil : D = [] := List.eq_nil_of_length_eq_zero hlen
    subst D
    rw [← cartierPulledModuleMixedEulerDifference_id_unit]
    exact proper_dim_le_one_pulled_nef_unit_nonneg K hdim hProj (𝟙 X) N hN E
  | succ n ih =>
    intro X _ _ _ hdim hProj N hN D hlen hD E
    let := properOverField_scheme_isNoetherian (K := K) (X := X)
    cases D with
    | nil => simp at hlen
    | cons H D =>
      have hlenD : D.length = n := by simp only [List.length_cons] at hlen; omega
      have hDtail : ∀ L ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • L) :=
        fun L hL => hD L (List.mem_cons_of_mem _ hL)
      obtain ⟨q, hq, hgen⟩ := hD H (List.mem_cons_self ..)
      obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgen
      let f := cartierSectionUnit (q • H) s hs
      let G := cartierSectionZeroDivisor (q • H) s hs
      have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective (q • H) s hs
      let I := effectiveCartierIdealSheaf G hG
      let W := I.subscheme
      let jW : W ⟶ X := I.subschemeι
      let : W.Over (Spec (CommRingCat.of K)) := ⟨jW ≫ (X ↘ Spec (CommRingCat.of K))⟩
      let : jW.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      let : IsProper (W ↘ Spec (CommRingCat.of K)) := by
        change IsProper (jW ≫ (X ↘ Spec (CommRingCat.of K)))
        infer_instance
      let := properOverField_scheme_isNoetherian (K := K) (X := W)
      let : (CohomologyAux.unitModule W).IsCoherent := invertible_module_isCoherent _
      have hdimW : topologicalKrullDim W ≤ (n + 1 : ℕ) :=
        effectiveCartierCut_topologicalKrullDim_le G hG (n + 1) (by simpa using hdim)
      have hunit : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
          [IsProper (Z ↘ Spec (CommRingCat.of K))]
          (i : Z ⟶ W) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))],
          0 ≤ cartierPulledModuleMixedEulerDifference K (i ≫ jW) (CohomologyAux.unitModule Z) (N :: D) 0 := by
        intro Z _ _ _ i _ _
        let t : Z ⟶ X := i ≫ jW
        obtain ⟨NZ, ⟨aN⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor N t
        have hNZ : CartierIsNef K NZ := cartierIsNef_of_pullback_representative K t N NZ aN hN
        obtain ⟨DZ, hDZ⟩ := exists_cartier_direction_representations t D
        have hDZsem := cartierSemiample_list_of_pullback_representatives t hDZ hDtail
        obtain ⟨J, hJ⟩ := hProj
        obtain ⟨JZ, ⟨aJ⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor J t
        have hJZ := cartierHasHyperplanePower_of_closed_representative K t J JZ aJ
          (cartierHasHyperplanePower_of_isAmpleProj K J hJ)
        have hProjZ := cartierHasHyperplanePower_exists_ample K JZ hJZ
        have hdimZ : topologicalKrullDim Z ≤ (n + 1 : ℕ) :=
          i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdimW
        rw [cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K t (.cons ⟨aN⟩ hDZ) 0 0
          ((Scheme.Modules.pullback t).mapIso (cartierZeroSheafIso X) ≪≫
            Scheme.Modules.pullbackObjUnitIso t ≪≫ (cartierZeroSheafIso Z).symm)]
        exact ih Z hdimZ hProjZ NZ hNZ DZ (hDZ.length_eq.symm.trans hlenD) hDZsem 0
      have hnnCut := proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
        K n hdimW jW (N :: D) (by simp only [List.length_cons, hlenD]; omega) 0 hunit
        (CohomologyAux.unitModule W)
      have hnnG : 0 ≤ cartierMixedEulerDifference K (G :: N :: D) E := by
        rw [proper_cartierMixedEulerDifference_top_eq_effective_cut K (N :: D) G E hG
          (by simpa [List.length_cons, hlenD] using hdim)]
        exact hnnCut
      change 0 ≤ cartierMixedEulerDifference K ((q • H + principalCartierDivisor X f) :: N :: D) E at hnnG
      rw [cartierMixedEulerDifference_direction_principal] at hnnG
      have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K (n + 2) hdim [] (N :: D)
        (by simp [hlenD]) H E q
      simp only [List.nil_append] at hscale
      rw [hscale] at hnnG
      have hnnH := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hnnG
      rw [cartierMixedEulerDifference_perm K (List.Perm.swap H N D) E]
      exact hnnH

end MixedFujita
