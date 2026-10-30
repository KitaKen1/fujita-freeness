/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefAmpleIntegerDescent

/-! 元NefAddAmpleStatementの無条件証明と普遍的正倍非消滅。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- The ORIGINAL curve-test nef plus ORIGINAL projective ample divisor is
ample. All-dimensional nonvanishing and the smaller-dimensional restrictions
are proved internally by weak algebraic Morse and finite integer descent. -/
theorem proper_nef_add_ample_isAmpleProj
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A) :
    CartierIsAmpleProj K (N + A) := by
  have go : ∀ d : ℕ, ∀ (T : Scheme.{u}) [IsIntegral T]
      [T.Over (Spec (CommRingCat.of K))] [IsProper (T ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim T = d → ∀ (P B : CartierDivisor T),
        CartierIsNef K P → CartierIsAmpleProj K B → CartierIsAmpleProj K (P + B) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro T _ _ _ hdim P B hP hB
      cases d with
      | zero =>
        apply nef_add_ample_isAmpleProj_of_semiample K P B hP hB
        exact ⟨1, by omega, by simpa only [one_smul] using
          zeroDimensional_cartier_globallyGenerated (by simpa only [Nat.cast_zero] using hdim) (P + B)⟩
      | succ n =>
        apply nef_add_ample_isAmpleProj_of_lower_dimension_by_integer_descent K n hdim ?_ P B hP hB
        intro Z _ _ _ hdimZ P' B' hP' hB'
        obtain ⟨k, hk⟩ : ∃ k : ℕ, topologicalKrullDim Z = k :=
          ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
        have hkn : k ≤ n := by rw [hk] at hdimZ; exact_mod_cast hdimZ
        exact ih k (by omega) Z hk P' B' hP' hB'
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X = d :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  exact go d X hd N A hN hA


/-- The original frozen all-dimensional nef-plus-ample statement holds. -/
theorem nefAddAmpleStatement_holds : NefAddAmpleStatement.{u} := by
  intro K _ _ _ X _ _ _ N A hN hA
  let : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    isProper_structureMap_of_exists_ample_cartier ⟨A, hA⟩
  exact proper_nef_add_ample_isAmpleProj K N A hN hA


/-- Every original nef-plus-ample sum has a nonzero section of an internally
constructed positive multiple; this is now a theorem rather than an input. -/
theorem proper_nef_add_ample_exists_nonzero_multiple
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : Γ((m • (N + A)).sheaf, ⊤), s ≠ 0 := by
  obtain ⟨m, hm, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple
    (N + A) (proper_nef_add_ample_isAmpleProj K N A hN hA)
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgen
  exact ⟨m, hm, s, hs⟩

end MixedFujita
