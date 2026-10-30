/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.TopMixedEulerHomogeneity

/-! 元混合Morse不等式の整数斉次性。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Scaling both original directions preserves the strict weak Morse
inequality. Every top-dimensional mixed factor has its actual integer weight. -/
theorem proper_mixed_morse_inequality_nsmul
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ)) (H G : CartierDivisor X)
    (hnum : (n + 1 : ℤ) * cartierMixedEulerDifference K (G :: List.replicate n H) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) H) 0) (q : ℕ) (hq : 0 < q) :
    (n + 1 : ℤ) * cartierMixedEulerDifference K ((q • G) :: List.replicate n (q • H)) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) (q • H)) 0 := by
  have hc : cartierMixedEulerDifference K ((q • G) :: List.replicate n (q • H)) 0 =
      (q : ℤ) ^ (n + 1) * cartierMixedEulerDifference K (G :: List.replicate n H) 0 := by
    simpa only [List.map_cons, List.map_replicate, List.append_nil, List.length_cons,
      List.length_replicate] using proper_cartierMixedEulerDifference_top_nsmul_prefix
        K (n + 1) hdim (G :: List.replicate n H) [] (by simp) 0 q
  rw [hc, proper_cartierMixedEulerDifference_diagonal_nsmul K (n + 1) hdim H 0 q]
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have h := mul_lt_mul_of_pos_left hnum (pow_pos hqZ (n + 1))
  nlinarith only [h]

end MixedFujita
