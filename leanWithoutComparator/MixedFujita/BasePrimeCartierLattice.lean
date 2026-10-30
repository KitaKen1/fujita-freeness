/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierBaseNeighborhoodSections
public import MixedFujita.BasePrimeCartierCoefficientInvariance
public import MixedFujita.FloorDivisorLifting
public import MixedFujita.NormalEffectiveCartierPrime

/-!
Extend a nonnegative integer pole cutoff to arbitrary base Cartier twists.
The pullback order at every prime relevant to a normal base prime depends
only on the base coefficient. No effectivity or SNC support of the tested
Cartier twist is required.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Actual dominant Cartier pullback commutes with every integer multiple. -/
theorem cartierPullback_zsmul {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    (g : T ⟶ Y) [IsDominant g] (L : CartierDivisor Y) (k : ℤ) :
    cartierPullback g (k • L) = k • cartierPullback g L := by
  let pb : CartierDivisor Y →+ CartierDivisor T :=
    { toFun := cartierPullback g
      map_zero' := cartierPullback_zero g
      map_add' := cartierPullback_add g }
  exact map_zsmul pb k L

/-- A normalized reference divisor identifies every actual relevant pullback
coefficient with the base coefficient times the reference pullback order. -/
theorem cartierCoefficient_pullback_eq_base_coefficient_mul
    {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    [IsLocallyNoetherian T] [IsLocallyNoetherian Y]
    (g : T ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
    [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (H : CartierDivisor Y) (hHη : cartierCoefficient H (η : Y) = 1)
    (L : CartierDivisor Y) (t : CodimensionOnePoint T)
    (ht : (η : Y) ∈ closure ({g (t : T)} : Set Y)) :
    cartierCoefficient (cartierPullback g L) (t : T) =
      cartierCoefficient L (η : Y) * cartierCoefficient (cartierPullback g H) (t : T) := by
  have hbase : cartierCoefficient L (η : Y) =
      cartierCoefficient ((cartierCoefficient L (η : Y)) • H) (η : Y) := by
    rw [cartierCoefficient_zsmul, hHη, mul_one]
  have h := cartierCoefficient_pullback_eq_of_base_prime_coefficient_eq g η L
    ((cartierCoefficient L (η : Y)) • H) hbase t ht
  simpa only [cartierPullback_zsmul, cartierCoefficient_zsmul] using h

/-- An integer pole cutoff for one effective normalized reference divisor
determines actual nearby unit sections for every base Cartier divisor. -/
theorem base_prime_cartier_neighborhood_lattice_of_integer_cutoff
    {T Y : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (g : T ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
    [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (H : CartierDivisor Y) (hH : H.IsEffective)
    (hHη : cartierCoefficient H (η : Y) = 1)
    (E : CartierDivisor T) (heff : E.IsEffective) (b : ℤ)
    (hcut : ∀ p : ℕ,
      (∀ t : CodimensionOnePoint T, (η : Y) ∈ closure ({g (t : T)} : Set Y) →
        0 ≤ cartierCoefficient (E - p • cartierPullback g H) (t : T)) ↔ (p : ℤ) ≤ b)
    (L : CartierDivisor Y) :
    (∃ U : Y.Opens, (η : Y) ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) (g ⁻¹ᵁ U)
        (1 : Γ(T, g ⁻¹ᵁ U)) ∈ (E + cartierPullback g L).sections (g ⁻¹ᵁ U)) ↔
      0 ≤ cartierCoefficient L (η : Y) + b := by
  have hb : 0 ≤ b := by
    apply (hcut 0).mp
    intro t _
    simpa only [zero_nsmul, sub_zero] using
      cartierCoefficient_nonneg_of_isEffective E heff (t : T)
  let k : ℤ := cartierCoefficient L (η : Y)
  have hscale (t : CodimensionOnePoint T)
      (ht : (η : Y) ∈ closure ({g (t : T)} : Set Y)) :
      cartierCoefficient (cartierPullback g L) (t : T) =
        k * cartierCoefficient (cartierPullback g H) (t : T) :=
    cartierCoefficient_pullback_eq_base_coefficient_mul g η H hHη L t ht
  by_cases hk : 0 ≤ k
  · have hcoeff : ∀ t : CodimensionOnePoint T,
        (η : Y) ∈ closure ({g (t : T)} : Set Y) →
          0 ≤ cartierCoefficient (E + cartierPullback g L) (t : T) := by
      intro t ht
      rw [cartierCoefficient_add, hscale t ht]
      exact add_nonneg (cartierCoefficient_nonneg_of_isEffective E heff (t : T))
        (mul_nonneg hk (cartierCoefficient_nonneg_of_isEffective _
          (cartierPullback_effective_of_effective g H hH) (t : T)))
    exact iff_of_true
      ((exists_base_neighborhood_one_mem_cartier_sections_iff hnormT g (η : Y) _).mpr hcoeff)
      (add_nonneg hk hb)
  · let p : ℕ := (-k).toNat
    have hkp : k = -(p : ℤ) := by
      dsimp only [p]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have heq :
        (∀ t : CodimensionOnePoint T, (η : Y) ∈ closure ({g (t : T)} : Set Y) →
          0 ≤ cartierCoefficient (E + cartierPullback g L) (t : T)) ↔
        (∀ t : CodimensionOnePoint T, (η : Y) ∈ closure ({g (t : T)} : Set Y) →
          0 ≤ cartierCoefficient (E - p • cartierPullback g H) (t : T)) := by
      apply forall_congr'
      intro t
      apply imp_congr_right
      intro ht
      rw [cartierCoefficient_add, hscale t ht, cartierCoefficient_sub,
        cartierCoefficient_nsmul, hkp]
      simp only [neg_mul, sub_eq_add_neg]
    exact ((exists_base_neighborhood_one_mem_cartier_sections_iff hnormT g (η : Y) _).trans
      heq |>.trans (hcut p)).trans (by change (p : ℤ) ≤ b ↔ 0 ≤ k + b; omega)

end MixedFujita
