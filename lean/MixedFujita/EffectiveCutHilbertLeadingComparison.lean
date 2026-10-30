/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MixedEulerEffectiveCut
public import MixedFujita.PulledModuleEulerPolynomial
public import MixedFujita.CartierEulerPolynomial
public import MixedFujita.EffectiveGeneratedCutSectionBounds

/-! 実Cartier切断とambient Hilbert先頭係数のMorse比較。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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

attribute [local instance] effectiveCartierCutOverField

/-- The strict original mixed Euler inequality is precisely dominance of
the ambient Hilbert leading coefficient over the actual Cartier cut coefficient. -/
theorem effectiveCartierCut_EulerPolynomial_top_coeff_lt
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (H G : CartierDivisor X) (hG : G.IsEffective)
    (hnum : (n + 1 : ℤ) * cartierMixedEulerDifference K (G :: List.replicate n H) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) H) 0) :
    (cartierPulledModuleEulerPolynomial K (effectiveCartierIdealSheaf G hG).subschemeι
      (SheafOfModules.unit (effectiveCartierIdealSheaf G hG).subscheme.ringCatSheaf) n H 0).coeff n <
        (cartierEulerPolynomial K (n + 1) H 0).coeff (n + 1) := by
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have hcut := proper_cartierMixedEulerDifference_top_eq_effective_cut K
    (List.replicate n H) G 0 hG (by simpa only [List.length_replicate] using hdim)
  have hP := cartierEulerPolynomial_coeff_top K (n + 1) H 0
  have hQ := cartierPulledModuleEulerPolynomial_coeff_top K i O n H 0
  have hfac : ((n + 1).factorial : ℚ) = (n + 1 : ℚ) * (n.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ n
  apply (mul_lt_mul_iff_right₀ (show (0 : ℚ) < ((n + 1).factorial : ℚ) by positivity)).mp
  rw [hP, hfac, mul_assoc, hQ]
  rw [hcut] at hnum
  exact_mod_cast hnum

end MixedFujita
