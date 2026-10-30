/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.NormalEffectiveCartierPrime

/-!
Every normal codimension-one stalk supplies a regular uniformizer on an actual
smaller affine neighbourhood. Its principal divisor on that open is an actual
effective Cartier divisor of coefficient one at the original prime. Neither
the neighbourhood nor the equation or Cartier divisor is supplied as an input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]

/-- A base DVR uniformizer spreads to a nonzero regular function on an affine
neighbourhood inside any prescribed neighbourhood of the prime. -/
theorem normal_base_prime_affine_regular_uniformizer
    (W : Y.Opens) (hηW : (η : Y) ∈ W) :
    ∃ (U : Y.affineOpens), U.1 ≤ W ∧ ∃ (hηU : (η : Y) ∈ U.1)
      (a : Γ(Y, U.1)) (_ : a ≠ 0),
      letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
      Y.ord (Y.germToFunctionField U.1 a) (η : Y) = 1 := by
  letI := normal_codimensionOne_stalk_DVR η
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (η : Y))
  have hne : algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((IsFractionRing.injective (Y.presheaf.stalk (η : Y)) Y.functionField)
      (h.trans (map_zero _).symm))
  have hord : Y.ord (algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField ϖ) (η : Y) = 1 := by
    rw [Y.ord_eq_iff η.property hne]
    simp only [AlgebraicGeometry.Scheme.ordHom]
    rw [Ring.ordFrac_irreducible hϖ, WithZero.exp_eq_coe_ofAdd]
  obtain ⟨V, hVW, hηV, s, hs⟩ := Y.presheaf.exists_le_germ_eq ϖ hηW
  obtain ⟨_, ⟨U, hUa, rfl⟩, hηU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hηV V.isOpen
  let a : Γ(Y, U) := Y.presheaf.map (homOfLE hUV).op s
  have hga : Y.presheaf.germ U (η : Y) hηU a = ϖ := by
    dsimp only [a]
    exact (Y.presheaf.germ_res_apply (homOfLE hUV) (η : Y) hηU s).trans hs
  have ha : a ≠ 0 := by
    intro hz
    apply hϖ.ne_zero
    rw [← hga, hz, map_zero]
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  refine ⟨⟨U, hUa⟩, hUV.trans hVW, hηU, a, ha, ?_⟩
  rw [← Y.algebraMap_germ_eq_germToFunctionField hηU, hga]
  exact hord

/-- Construct the actual effective coefficient-one Cartier divisor on an affine
neighbourhood of a normal base prime. -/
theorem normal_base_prime_effective_cartier_neighborhood
    (W : Y.Opens) (hηW : (η : Y) ∈ W) :
    ∃ (U : Y.affineOpens), U.1 ≤ W ∧ ∃ (hηU : (η : Y) ∈ U.1),
      letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
      ∃ H : CartierDivisor U.1.toScheme, H.IsEffective ∧
        cartierCoefficient H (⟨(η : Y), hηU⟩ : U.1.toScheme) = 1 := by
  obtain ⟨U, hUW, hηU, a, ha, hord⟩ := normal_base_prime_affine_regular_uniformizer η W hηW
  letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
  letI : IsDominant U.1.ι :=
    ⟨U.1.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let f := regularEquationRationalUnit Y U.1 a ha
  let H := cartierPullback U.1.ι (principalCartierDivisor Y f)
  have heff : H.IsEffective := by
    apply CartierDivisor.isEffective_iff_exists.mpr
    intro p
    refine ⟨Units.map (dominantFunctionFieldMap U.1.ι).hom.toMonoidHom f,
      cartierPullback_isLocalEquationAt U.1.ι (principalCartierDivisor Y f) p
        (CartierDivisor.isLocalEquationAt_principalCartierDivisor (U.1.ι p) f),
      U.1.ι.stalkMap p (Y.presheaf.germ U.1 (U.1.ι p) p.property a), ?_⟩
    rw [← dominantFunctionFieldMap_algebraMap]
    change (dominantFunctionFieldMap U.1.ι).hom
      (algebraMap (Y.presheaf.stalk (U.1.ι p)) Y.functionField
        (Y.presheaf.germ U.1 (U.1.ι p) p.property a)) =
      (dominantFunctionFieldMap U.1.ι).hom (Y.germToFunctionField U.1 a)
    exact congrArg (dominantFunctionFieldMap U.1.ι).hom
      (Y.algebraMap_germ_eq_germToFunctionField (x := U.1.ι p) p.property a)
  let p : U.1.toScheme := ⟨(η : Y), hηU⟩
  have hb : Function.Bijective (U.1.ι.stalkMap p) :=
    ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap p)
  letI : IsDiscreteValuationRing (Y.presheaf.stalk (U.1.ι p)) :=
    normal_codimensionOne_stalk_DVR η
  letI : IsDiscreteValuationRing (U.1.toScheme.presheaf.stalk p) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective (U.1.ι.stalkMap p).hom hb)
  have hp : Order.coheight p = 1 :=
    (coheight_eq_of_stalkMap_bijective U.1.ι p hb).trans η.property
  refine ⟨U, hUW, hηU, H, heff, ?_⟩
  change cartierCoefficient (cartierPullback U.1.ι (principalCartierDivisor Y f)) p = 1
  rw [cartierCoefficient_pullback_of_stalkMap_bijective U.1.ι ⟨p, hp⟩ η.property hb,
    cartierCoefficient_principal, regularEquationRationalUnit_val]
  exact hord

end MixedFujita
