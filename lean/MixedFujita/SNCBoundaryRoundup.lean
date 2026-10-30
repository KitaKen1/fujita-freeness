/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentCartier
public import MixedFujita.FloorDivisorLifting
public import MixedFujita.RationalIsolationArithmetic

/-!
Construct the actual effective Cartier round-up of the negative of a rational
SNC boundary with coefficients below one. Component divisors are constructed
from the SNC family; neither a rounded divisor nor its effectivity is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A nonnegative integral multiple of an effective Cartier divisor is effective. -/
theorem cartierIsEffective_zsmul_nonneg {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) (hD : D.IsEffective) (a : ℤ) (ha : 0 ≤ a) :
    (a • D).IsEffective := by
  lift a to ℕ using ha
  simp only [natCast_zsmul]
  induction a with
  | zero => simpa only [zero_nsmul] using CartierDivisor.isEffective_zero (X := X)
  | succ a ih => simpa only [succ_nsmul] using ih.add hD

/-- A normalized integral coefficient below one has nonnegative negative round-down. -/
theorem negative_floor_normalized_coefficient_nonneg (b : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : b < (d : ℤ)) : 0 ≤ -⌊(b : ℝ) / (d : ℝ)⌋ := by
  apply isolation_floor_correction_nonneg
  apply (div_lt_one (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast hb

/-- Construct an effective Cartier divisor whose coefficients are exactly
ceil(-B/d), for an actual SNC-supported denominator-cleared boundary B. -/
theorem exists_effective_snc_boundary_roundup {K : Type u} [Field K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (B : CartierDivisor X) (d : ℕ) (hd : 1 ≤ d) {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient B (t : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ)) :
    ∃ E : CartierDivisor X, E.IsEffective ∧ ∀ t : CodimensionOnePoint X,
      cartierCoefficient E (t : X) =
        ⌈-((cartierCoefficient B (t : X) : ℝ) / (d : ℝ))⌉ := by
  classical
  obtain ⟨P, hP, -, hPc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  let a : Fin r → ℤ := fun i => -⌊(cartierCoefficient B (ξ i) : ℝ) / (d : ℝ)⌋
  have ha : ∀ i, 0 ≤ a i := fun i =>
    negative_floor_normalized_coefficient_nonneg _ d hd (hb i)
  refine ⟨∑ i, a i • P i, ?_, ?_⟩
  · apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro i _
    exact cartierIsEffective_zsmul_nonneg (P i) (hP i) (a i) (ha i)
  · intro t
    rcases cartierCoefficient_member_combination ξ hinj P hPc a t with
      ⟨i, hti, hcoeff⟩ | ⟨hnot, hcoeff⟩
    · rw [hcoeff, hti, Int.ceil_neg]
    · rw [hcoeff, hsupport t hnot]
      simp

end MixedFujita
