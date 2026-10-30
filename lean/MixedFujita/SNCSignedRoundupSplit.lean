/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCLCRoundupSplit

/-!
Split ceil(-B/d) into effective Cartier divisors E-S for an arbitrary signed SNC
boundary. There is no log-canonicity assumption: coefficients greater than d give
a possibly nonreduced cut S. Its prime support is exactly the non-klt threshold,
whereas E has positive coefficient exactly at the negative boundary coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The negative part of ceil(-b/d) detects b/d >= 1, including b > d. -/
theorem signed_roundup_cut_positive_iff (b : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    0 < max (-⌈-((b : ℝ) / (d : ℝ))⌉) 0 ↔ (d : ℤ) ≤ b := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Int.ceil_neg, neg_neg, lt_max_iff]
  simp only [lt_self_iff_false, or_false]
  rw [Int.lt_iff_add_one_le, zero_add, Int.le_floor, Int.cast_one,
    one_le_div hdpos]
  exact_mod_cast (Iff.rfl : (d : ℤ) ≤ b ↔ (d : ℤ) ≤ b)

/-- The positive part of ceil(-b/d) detects precisely negative coefficients. -/
theorem signed_roundup_exceptional_positive_iff (b : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    0 < max ⌈-((b : ℝ) / (d : ℝ))⌉ 0 ↔ b < 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [lt_max_iff]
  simp only [lt_self_iff_false, or_false]
  rw [Int.lt_ceil, Int.cast_zero, neg_pos, div_lt_iff₀ hdpos, zero_mul]
  exact_mod_cast (Iff.rfl : b < 0 ↔ b < 0)

/-- Nonnegative boundary coefficients contribute nothing to the positive roundup part. -/
theorem signed_roundup_exceptional_eq_zero (b : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : 0 ≤ b) : max ⌈-((b : ℝ) / (d : ℝ))⌉ 0 = 0 := by
  have h := (signed_roundup_exceptional_positive_iff b d hd).not.mpr (not_lt.mpr hb)
  have hnon := le_max_right ⌈-((b : ℝ) / (d : ℝ))⌉ 0
  omega

/-- Construct both actual effective Cartier parts of an arbitrary signed SNC roundup.
The two parts share no prime component, without imposing any upper coefficient bound. -/
theorem exists_effective_snc_signed_roundup_split
    {K : Type u} [Field K] {n : ℕ} {T : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (B : CartierDivisor T) (d : ℕ) {r : ℕ}
    (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient B (t : T) = 0) :
    ∃ (E S : CartierDivisor T), E.IsEffective ∧ S.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
        max ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉ 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
        max (-⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉) 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = 0 ∨
        cartierCoefficient S (t : T) = 0) := by
  classical
  obtain ⟨F, hF, -, hFc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  let q : T → ℤ := fun t => ⌈-((cartierCoefficient B t : ℝ) / (d : ℝ))⌉
  let E := ∑ i, max (q (ξ i)) 0 • F i
  let S := ∑ i, max (-q (ξ i)) 0 • F i
  have heff (a : Fin r → ℤ) (ha : ∀ i, 0 ≤ a i) : (∑ i, a i • F i).IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro i _
    exact cartierIsEffective_zsmul_nonneg (F i) (hF i) (a i) (ha i)
  have hEc (t : CodimensionOnePoint T) : cartierCoefficient E (t : T) = max (q t) 0 := by
    rcases cartierCoefficient_member_combination ξ hinj F hFc (fun i => max (q (ξ i)) 0) t with
      ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci]
      simp [q, hsupport t hti]
  have hSc (t : CodimensionOnePoint T) : cartierCoefficient S (t : T) = max (-q t) 0 := by
    rcases cartierCoefficient_member_combination ξ hinj F hFc (fun i => max (-q (ξ i)) 0) t with
      ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci]
      simp [q, hsupport t hti]
  refine ⟨E, S, heff _ (fun i => le_max_right _ _), heff _ (fun i => le_max_right _ _),
    hEc, hSc, fun t => ?_, fun t => ?_⟩
  · rw [cartierCoefficient_sub, hEc, hSc]
    change max (q t) 0 - max (-q t) 0 = q t
    omega
  · rw [hEc, hSc]
    omega

end MixedFujita
