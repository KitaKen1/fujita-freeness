/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCRoundupSplitArithmetic
public import MixedFujita.NormalCartierCoefficientExt

/-! 実lc SNC roundup分解と臨界Cartier切断の零判定。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Construct the two ACTUAL effective Cartier divisors in ceil(-B/d)=E-S for
any signed lc SNC boundary. S has coefficient one exactly at the coefficient-d primes;
E has coefficient zero there. No rounded divisor, effectivity or cut is supplied. -/
theorem exists_effective_snc_lc_roundup_split
    {K : Type u} [Field K] {n : ℕ} {T : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (B : CartierDivisor T) (d : ℕ) (hd : 1 ≤ d) {r : ℕ}
    (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) ≤ (d : ℤ)) :
    ∃ (E S : CartierDivisor T), E.IsEffective ∧ S.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
        if cartierCoefficient B (t : T) = (d : ℤ) then 1 else 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
        ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉ + cartierCoefficient S (t : T)) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉) := by
  classical
  obtain ⟨F, hF, _, hFc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  let s : Fin r → ℤ := fun i => if cartierCoefficient B (ξ i) = (d : ℤ) then 1 else 0
  let e : Fin r → ℤ := fun i => ⌈-((cartierCoefficient B (ξ i) : ℝ) / (d : ℝ))⌉ + s i
  let E := ∑ i, e i • F i
  let S := ∑ i, s i • F i
  have hE : E.IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro i _
    exact cartierIsEffective_zsmul_nonneg (F i) (hF i) (e i)
      (lc_roundup_positive_part_nonneg _ d hd (hb i))
  have hS : S.IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro i _
    exact cartierIsEffective_zsmul_nonneg (F i) (hF i) (s i) (by dsimp [s]; split_ifs <;> omega)
  have hSc (t : CodimensionOnePoint T) : cartierCoefficient S (t : T) =
      if cartierCoefficient B (t : T) = (d : ℤ) then 1 else 0 := by
    rcases cartierCoefficient_member_combination ξ hinj F hFc s t with
      ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci, hsupport t hti, ite_eq_right (by exact_mod_cast (by omega : (0 : ℕ) ≠ d))]
  have hEc (t : CodimensionOnePoint T) : cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉ + cartierCoefficient S (t : T) := by
    rw [hSc]
    rcases cartierCoefficient_member_combination ξ hinj F hFc e t with
      ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci, hsupport t hti, ite_eq_right (by exact_mod_cast (by omega : (0 : ℕ) ≠ d))]
      norm_num
  refine ⟨E, S, hE, hS, hSc, hEc, fun t => ?_⟩
  rw [cartierCoefficient_sub, hEc, add_sub_cancel_right]


/-- A signed lc SNC split is empty exactly when every original supported coefficient
is strictly below the denominator. Normality detects equality of the ACTUAL Cartier cut. -/
theorem snc_lc_critical_cut_eq_zero_iff_strict
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (B S : CartierDivisor T) (d : ℕ) (hd : 1 ≤ d) {r : ℕ}
    (ξ : Fin r → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) ≤ (d : ℤ))
    (hSc : ∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
      if cartierCoefficient B (t : T) = (d : ℤ) then 1 else 0) :
    S = 0 ↔ ∀ i, cartierCoefficient B (ξ i) < (d : ℤ) := by
  constructor
  · intro h i
    have hc := hSc ⟨ξ i, hξ i⟩
    rw [h, cartierCoefficient_zero] at hc
    have hne : cartierCoefficient B (ξ i) ≠ (d : ℤ) := by
      intro he
      rw [ite_eq_left he] at hc
      omega
    exact lt_of_le_of_ne (hb i) hne
  · intro h
    apply cartierDivisor_eq_of_forall_coefficient_eq hnorm
    intro t
    rw [hSc, cartierCoefficient_zero]
    have hne : cartierCoefficient B (t : T) ≠ (d : ℤ) := by
      by_cases ht : (t : T) ∈ Set.range ξ
      · obtain ⟨i, hi⟩ := ht
        rw [← hi]
        exact (h i).ne
      · rw [hsupport t ht]
        exact_mod_cast (by omega : (0 : ℕ) ≠ d)
    exact ite_eq_right hne

end MixedFujita
