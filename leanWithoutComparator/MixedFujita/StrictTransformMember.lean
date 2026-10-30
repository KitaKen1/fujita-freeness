/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NonkltAdjacentMember

/-!
The strict transform as a member of the family of a principalizing model (step 9).

Let ρ : T → Y be a proper birational morphism of smooth schemes and ξ a family of prime divisors
of T supporting the pullback of a Cartier divisor D of Y. Over a prime divisor b of Y where D has
a nonzero coefficient, the unique prime lift of b (with bijective stalk map) is a member ξ_{s₀}
of the family, and the pullback of D has the coefficient of D there
(`exists_snc_member_over_prime`): for D = div(x_0) and b the generic point of the hyperplane this
is the strict transform H' with h = 1. At such a member the crepant boundary of the smooth pair
(Y, 0), minus the relative canonical divisor, has coefficient zero
(`crepantBoundaryCartier_coefficient_eq_zero_of_stalkMap_bijective`): k = 0 along H'. These are
the coefficients h = 1, k = 0 of the strict transform used to find a component meeting it
(check-340).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Member

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ Y) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

include K n in
omit [ρ.IsOver (Spec (CommRingCat.of K))] in
/-- Over a prime divisor b of Y where D has a nonzero coefficient, a proper birational smooth model
whose family supports the pullback of D has a member over b with bijective stalk map, at which the
pullback of D has the coefficient of D at b. -/
theorem exists_snc_member_over_prime [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom) {r : ℕ} (ξ : Fin r → T)
    (b : CodimensionOnePoint Y) (D : CartierDivisor Y) (hDb : cartierCoefficient D (b : Y) ≠ 0)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ D) (t : T) = 0) :
    ∃ s₀, ρ (ξ s₀) = b ∧ Function.Bijective (ρ.stalkMap (ξ s₀)) ∧
      cartierCoefficient (cartierPullback ρ D) (ξ s₀) = cartierCoefficient D (b : Y) := by
  obtain ⟨t, ⟨ht, hbij⟩, -⟩ :=
    proper_birational_existsUnique_smooth_prime_lift (K := K) (n := n) ρ hρ b
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hb1 : Order.coheight (ρ (t : T)) = 1 := ht ▸ b.property
  haveI := smoothOverField_codimensionOne_stalk_DVR (K := K)
    (⟨ρ (t : T), hb1⟩ : CodimensionOnePoint Y)
  haveI := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  have hcoef : cartierCoefficient (cartierPullback ρ D) (t : T) = cartierCoefficient D (b : Y) := by
    rw [cartierCoefficient_pullback_of_stalkMap_bijective ρ t hb1 hbij D, ht]
  have hmem : (t : T) ∈ Set.range ξ := by
    by_contra hnot
    exact hDb (hcoef ▸ hsupp t hnot)
  obtain ⟨s₀, hs₀⟩ := hmem
  refine ⟨s₀, ?_, ?_, ?_⟩
  · rw [hs₀]
    exact ht
  · rw [hs₀]
    exact hbij
  · rw [hs₀]
    exact hcoef

/-- At a member with bijective stalk map, the crepant boundary of the smooth pair (Y, 0) has
coefficient zero: the relative canonical divisor vanishes along the strict transform. -/
theorem crepantBoundaryCartier_coefficient_eq_zero_of_stalkMap_bijective
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cY : EtaleChart K Y n)
    (cT : EtaleChart K T n) (z : CodimensionOnePoint T) (hz : Order.coheight (ρ (z : T)) = 1)
    (hb : Function.Bijective (ρ.stalkMap (z : T))) :
    cartierCoefficient (crepantBoundaryCartier ρ hρ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
      etaleCharts_cover) (z : T) = 0 := by
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  haveI := smoothOverField_codimensionOne_stalk_DVR (K := K)
    (⟨ρ (z : T), hz⟩ : CodimensionOnePoint Y)
  haveI := smoothOverField_codimensionOne_stalk_DVR (K := K) z
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K Y n, ρ (z : T) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸
      Opens.mem_top (ρ (z : T)))
  rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective ρ hρ cY 1 1 _ cT z hz hb c hc,
    one_nsmul, cartierCoefficient_add, cartierCoefficient_principal, Units.val_one,
    Scheme.ord_one, add_zero, one_mul, Nat.cast_one, one_mul]
  change cartierCoefficient (canonicalDivisor n cY etaleCharts_cover) _ - _ = 0
  rw [cartierCoefficient_eq_ord (canonicalDivisor_isLocalEquationAt cY etaleCharts_cover c hc),
    sub_self]

end Member

end MixedFujita
