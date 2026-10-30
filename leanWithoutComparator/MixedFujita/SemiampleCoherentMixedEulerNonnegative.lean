/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ZeroDimensionalModuleEulerNonnegative
public import MixedFujita.SemiampleCartierRepresentatives
public import MixedFujita.CoherentMixedEulerPositivityReduction
public import MixedFujita.AmpleMixedIntersectionCut
public import MixedFujita.DiscreteGeometricDimension

/-! 任意体・非被約proper源・任意連接係数の元semiample最高次混合非負性。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- All ORIGINAL semiample directions have nonnegative top mixed Euler
coefficients on arbitrary proper, possibly nonreduced sources and arbitrary
coherent coefficients. Every cut, restriction and sign input is internal. -/
theorem proper_semiample_coherentMixedEuler_nonneg
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (p : Y ⟶ X)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (M : Y.Modules) [M.IsCoherent] (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  induction n generalizing X Y D with
  | zero =>
    let := properOverField_scheme_isNoetherian (K := K) (X := Y)
    have hnil : D = [] := List.eq_nil_of_length_eq_zero hlen
    subst D
    exact zeroDimensional_moduleEulerChar_nonneg K hdim ((cartierPullbackTwistFunctor E p).obj M)
  | succ n ih =>
    rw [proper_cartierPulledModuleMixedEulerDifference_top_base_independent K (n + 1)
      hdim p M D hlen E 0]
    apply proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
      K n hdim p D (by omega) 0 ?_ M
    intro Z _ _ _ i _ _
    have hb := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    rcases withBotENat_le_succ_cases (topologicalKrullDim Z) n hb with hs | hZdim
    · let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
      rw [proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hs (i ≫ p)
        (CohomologyAux.unitModule Z) D (by omega) 0]
    · obtain ⟨F, hFlen, hF, hval⟩ := semiample_exists_cartier_representatives K (i ≫ p) D hD
      rw [hval]
      cases F with
      | nil => simp only [List.length_nil] at hFlen; omega
      | cons H F =>
        have htail : F.length = n := by simp only [List.length_cons] at hFlen; omega
        have hFtail : ∀ J ∈ F, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • J) :=
          fun J hJ => hF J (List.mem_cons_of_mem _ hJ)
        obtain ⟨q, hq, hqH⟩ := hF H (List.mem_cons_self ..)
        obtain ⟨f, hf⟩ := cartierIsGloballyGenerated_exists_effective_principal_shift hqH
        let G := q • H + principalCartierDivisor Z f
        have hG : G.IsEffective := hf
        let a : (q • H).sheaf ≅ G.sheaf := (cartierSheafPrincipalShiftIso (q • H) f).symm
        let I := effectiveCartierIdealSheaf G hG
        let W := I.subscheme
        let j : W ⟶ Z := I.subschemeι
        let : W.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (Z ↘ Spec (CommRingCat.of K))⟩
        let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
        let : IsProper (W ↘ Spec (CommRingCat.of K)) := by
          change IsProper (j ≫ (Z ↘ Spec (CommRingCat.of K)))
          infer_instance
        let O : W.Modules := CohomologyAux.unitModule W
        let : O.IsCoherent := invertible_module_isCoherent O
        have hdimW : topologicalKrullDim W ≤ n :=
          effectiveCartierCut_topologicalKrullDim_le G hG n hZdim.le
        have hscaled : (q : ℤ) * cartierMixedEulerDifference K (H :: F) 0 =
            cartierPulledModuleMixedEulerDifference K j O F 0 :=
          proper_cartierMixedIntersection_scaled_effective_cut K F H G hG q a
            (by simpa [htail] using hZdim)
        have hnonneg := ih hdimW j F htail hFtail O 0
        have hmul : 0 ≤ (q : ℤ) * cartierMixedEulerDifference K (H :: F) 0 := by
          rw [hscaled]
          exact hnonneg
        exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hmul

end MixedFujita
