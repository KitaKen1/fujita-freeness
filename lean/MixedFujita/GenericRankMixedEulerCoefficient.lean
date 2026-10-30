/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentGenericFree
public import MixedFujita.MixedEulerFiniteFreeCoefficient
public import MixedFujita.TopMixedEulerGenericInvariance

/-! 一般点での実有限自由階数による全最高次混合係数の比較。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On an actual proper integral source, the top mixed Euler coefficient
of a coherent module is its generic finite-free rank times that of the
unit module. The SAME rank works for every direction and base twist,
and its actual nonempty-open free-sheaf certificate is included. -/
theorem proper_coherent_exists_generic_rank_mixedEuler_formula
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent] :
    ∃ (k : ℕ) (W : Y.Opens), (W : Set Y).Nonempty ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ CohomologyAux.unitBiproduct W.toScheme k) ∧
      ∀ (D : List (CartierDivisor X)), n < D.length → ∀ E : CartierDivisor X,
        cartierPulledModuleMixedEulerDifference K p M D E =
          (k : ℤ) * cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  obtain ⟨W, hW, k, ⟨a⟩⟩ := coherent_exists_nonempty_open_unitBiproduct_iso M
  refine ⟨k, W, hW, ⟨a⟩, ?_⟩
  intro D hlen E
  let : (CohomologyAux.unitBiproduct Y k).IsCoherent := unitBiproduct_isCoherent Y k
  have h := proper_cartierPulledModuleMixedEulerDifference_top_eq_of_open_iso
    K n hdim p D hlen E M (CohomologyAux.unitBiproduct Y k) W hW
    (modulePullbackUnitBiproductIso W.ι k ≪≫ a.symm)
  exact h.trans (proper_cartierPulledModuleMixedEulerDifference_unitBiproduct K p D E k)


/-- Generic rank transfers nonnegativity of the actual top structure
coefficient to EVERY coherent coefficient on an integral proper source. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_unit_nonneg
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (hunit : 0 ≤ cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  obtain ⟨k, W, hW, a, hk⟩ := proper_coherent_exists_generic_rank_mixedEuler_formula K n hdim p M
  rw [hk D hlen E]
  exact mul_nonneg (by exact_mod_cast Nat.zero_le k) hunit


/-- A zero top structure coefficient also kills every coherent coefficient
on the same integral proper source, by the actual generic-rank formula. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_vanish_of_unit_vanish
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (hunit : cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E = 0) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  obtain ⟨k, W, hW, a, hk⟩ := proper_coherent_exists_generic_rank_mixedEuler_formula K n hdim p M
  rw [hk D hlen E, hunit, mul_zero]

end MixedFujita
