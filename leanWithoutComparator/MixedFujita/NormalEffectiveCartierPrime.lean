/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierCoefficientExt
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.LocalBirationalOrders
public import MixedFujita.NormalBirationalPrimeLifts

/-!
A nonzero effective Cartier divisor on a normal integral scheme has an actual
positive prime coefficient. Proper birational pullback supplies a positive prime
upstairs, internally, via the actual normal prime lift and its stalk isomorphism.
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

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- The actual dominant Cartier pullback preserves effectivity at every stalk. -/
theorem cartierPullback_effective_of_effective (π : T ⟶ X) [IsDominant π]
    (H : CartierDivisor X) (hH : H.IsEffective) : (cartierPullback π H).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro t
  obtain ⟨h, hh, a, ha⟩ := CartierDivisor.isEffective_iff_exists.mp hH (π t)
  refine ⟨Units.map (dominantFunctionFieldMap π).hom.toMonoidHom h,
    cartierPullback_isLocalEquationAt π H t hh, π.stalkMap t a, ?_⟩
  rw [← dominantFunctionFieldMap_algebraMap π t a, ha]
  rfl

variable [IsLocallyNoetherian X]

/-- Actual normal Cartier coefficient extensionality supplies a positive prime
for every nonzero effective Cartier divisor. -/
theorem exists_positive_prime_coefficient_of_effective_ne_zero
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (H : CartierDivisor X) (hH : H.IsEffective) (hne : H ≠ 0) :
    ∃ x : CodimensionOnePoint X, 0 < cartierCoefficient H (x : X) := by
  classical
  by_contra h
  apply hne
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm H 0
  intro x
  rw [cartierCoefficient_zero]
  have hn := cartierCoefficient_nonneg_of_isEffective H hH (x : X)
  have hnp : ¬ 0 < cartierCoefficient H (x : X) := fun hx => h ⟨x, hx⟩
  omega

/-- A positive prime survives on an actual proper birational normal model;
no nonzero pullback or prime witness is assumed. -/
theorem proper_birational_effective_pullback_exists_positive_prime [IsLocallyNoetherian T]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (π : T ⟶ X) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (H : CartierDivisor X) (hH : H.IsEffective) (hne : H ≠ 0) :
    ∃ t : CodimensionOnePoint T, 0 < cartierCoefficient (cartierPullback π H) (t : T) := by
  obtain ⟨x, hx⟩ := exists_positive_prime_coefficient_of_effective_ne_zero hnorm H hH hne
  obtain ⟨t, ht, hb⟩ := proper_birational_exists_normal_prime_lift hnorm π hπ x
  have hcoh : Order.coheight (π (t : T)) = 1 := by simpa only [ht] using x.property
  letI := hnorm (π (t : T))
  letI := hnormT (t : T)
  letI := normal_codimensionOne_stalk_DVR (⟨π (t : T), hcoh⟩ : CodimensionOnePoint X)
  letI := normal_codimensionOne_stalk_DVR t
  refine ⟨t, ?_⟩
  rw [cartierCoefficient_pullback_of_stalkMap_bijective π t hcoh hb H, ht]
  exact hx

end MixedFujita
