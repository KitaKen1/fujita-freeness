/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCPositiveCoefficientAtPoint
public import MixedFujita.NormalEffectiveCartierPrime

/-!
Proper dominant maps supply points over the specified base point. A nonunit
base equation remains a nonunit in the upstairs stalk, so its effective SNC
pullback has a positive component through that point. In particular a positive
base-prime coefficient constructs a relevant positive coefficient upstairs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {T Y : Scheme.{u}}
  [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y]
  (g : T ⟶ Y) [IsDominant g] [IsProper g]

/-- An effective pullback has an actual positive SNC component over any base
point where a regular local equation of the base divisor is a nonunit. -/
theorem proper_snc_pullback_exists_positive_coefficient_over_point
    (H : CartierDivisor Y) (hH : H.IsEffective) (η : Y)
    (f : Y.functionFieldˣ) (hf : H.IsLocalEquationAt η f)
    (a : Y.presheaf.stalk η)
    (ha : algebraMap (Y.presheaf.stalk η) Y.functionField a = (f : Y.functionField))
    (hnonunit : ¬ IsUnit a)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback g H) (t : T) = 0) :
    ∃ i, η ∈ closure ({g (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback g H) (ξ i) := by
  obtain ⟨p, rfl⟩ := surjective_of_isProper_of_isDominant g η
  have hmap : algebraMap (T.presheaf.stalk p) T.functionField (g.stalkMap p a) =
      ((Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f : T.functionFieldˣ) :
        T.functionField) := by
    rw [← dominantFunctionFieldMap_algebraMap g p a, ha]
    rfl
  have hnu : ¬ IsUnit (g.stalkMap p a) := by
    intro hu
    exact hnonunit (IsLocalHom.map_nonunit (f := (g.stalkMap p).hom) a hu)
  obtain ⟨i, hi, hpos⟩ := snc_effective_exists_positive_coefficient_through_point
    (cartierPullback g H) (cartierPullback_effective_of_effective g H hH)
    ξ hinj hξ hsnc hsupport p
    (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f)
    (cartierPullback_isLocalEquationAt g H p hf) (g.stalkMap p a) hmap hnu
  exact ⟨i, specializes_iff_mem_closure.mp
    ((specializes_iff_mem_closure.mpr hi).map g.continuous), hpos⟩

/-- Positive order at a base prime supplies the nonunit local equation internally. -/
theorem proper_snc_pullback_exists_positive_coefficient_over_prime [IsLocallyNoetherian Y]
    (H : CartierDivisor Y) (hH : H.IsEffective) (η : CodimensionOnePoint Y)
    (hη : 0 < cartierCoefficient H (η : Y))
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback g H) (t : T) = 0) :
    ∃ i, (η : Y) ∈ closure ({g (ξ i)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback g H) (ξ i) := by
  obtain ⟨f, hf, a, ha⟩ := CartierDivisor.isEffective_iff_exists.mp hH (η : Y)
  have hnonunit : ¬ IsUnit a := by
    intro hu
    have hz : cartierCoefficient H (η : Y) = 0 := by
      rw [cartierCoefficient_eq_ord hf, ← ha]
      exact scheme_ord_stalk_unit (η : Y) hu.unit
    omega
  exact proper_snc_pullback_exists_positive_coefficient_over_point g H hH (η : Y)
    f hf a ha hnonunit ξ hinj hξ hsnc hsupport

end MixedFujita
