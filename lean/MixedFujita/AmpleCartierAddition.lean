/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.HyperplaneSumVeryAmple

/-! 元projective ample Cartierの和のampleness。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Ordinary projective ampleness is closed under addition, through the
already constructed finite ample-sum projective embedding. -/
theorem cartierIsAmpleProj_add_of_isAmpleProj
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (D E : CartierDivisor X)
    (hD : CartierIsAmpleProj K D) (hE : CartierIsAmpleProj K E) :
    CartierIsAmpleProj K (D + E) := by
  have h := cartierIsAmpleSum_sum (K := K) (s := 2) (by omega) ![D, E] (by
    intro i
    fin_cases i
    · exact hD
    · exact hE)
  apply cartierIsAmpleProj_of_isAmpleSum
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end MixedFujita
