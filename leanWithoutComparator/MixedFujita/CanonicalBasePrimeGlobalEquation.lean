/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.DominantOpenBaseRestriction

public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.NormalEffectiveCartierPrime

/-!
A global principal Cartier divisor normalizing a given normal base prime can be chosen
with an effective pullback on an actual affine neighbourhood inside any prescribed open.
Effectivity on such a neighbourhood pulls back to its actual inverse-image neighbourhood.
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

/-- Construct a global principal Cartier divisor of coefficient one which becomes effective
on an actual affine neighbourhood inside the prescribed open. -/
theorem normal_base_prime_global_cartier_with_effective_neighborhood
    (W : Y.Opens) (hηW : (η : Y) ∈ W) :
    ∃ (U : Y.affineOpens), U.1 ≤ W ∧ ∃ (hηU : (η : Y) ∈ U.1),
      letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
      letI : IsDominant U.1.ι :=
        ⟨U.1.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
      ∃ H : CartierDivisor Y, cartierCoefficient H (η : Y) = 1 ∧
        (cartierPullback U.1.ι H).IsEffective := by
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
  letI := normal_codimensionOne_stalk_DVR η
  refine ⟨U, hUW, hηU, principalCartierDivisor Y f, ?_, heff⟩
  rw [cartierCoefficient_principal, regularEquationRationalUnit_val]
  exact hord
/-- Restricting to an actual base neighbourhood preserves the coefficient at its normal
prime, using the actual DVR stalk isomorphism. -/
theorem cartierPullback_base_open_coefficient_at_normal_prime
    (U : Y.Opens) (hηU : (η : Y) ∈ U) (H : CartierDivisor Y) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : IsDominant U.ι :=
      ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    cartierCoefficient (cartierPullback U.ι H) (⟨(η : Y), hηU⟩ : U.toScheme) =
      cartierCoefficient H (η : Y) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let θ : U.toScheme := ⟨(η : Y), hηU⟩
  have hb : Function.Bijective (U.ι.stalkMap θ) := ConcreteCategory.bijective_of_isIso _
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective U.ι θ hb).trans η.property
  letI : IsDiscreteValuationRing (Y.presheaf.stalk (U.ι θ)) := normal_codimensionOne_stalk_DVR η
  letI : IsDiscreteValuationRing (U.toScheme.presheaf.stalk θ) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective (U.ι.stalkMap θ).hom hb)
  exact cartierCoefficient_pullback_of_stalkMap_bijective U.ι ⟨θ, hθ⟩ η.property hb H

/-- Pulling back a Cartier divisor which is effective on a base open gives an effective
Cartier divisor on the actual inverse-image open. -/
theorem cartierPullback_effective_on_preimage_open {B Z : Scheme.{u}}
    [IsIntegral B] [IsIntegral Z] (ρ : B ⟶ Z) [IsDominant ρ]
    (U : Z.Opens) [Nonempty U] (H : CartierDivisor Z) :
    letI : IsDominant U.ι :=
      ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : Nonempty (ρ ⁻¹ᵁ U) := dominant_preimage_nonempty ρ U
    letI : IsDominant (ρ ⁻¹ᵁ U).ι :=
      ⟨(ρ ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    (cartierPullback U.ι H).IsEffective →
      (cartierPullback (ρ ⁻¹ᵁ U).ι (cartierPullback ρ H)).IsEffective := by
  letI : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : Nonempty (ρ ⁻¹ᵁ U) := dominant_preimage_nonempty ρ U
  letI : IsDominant (ρ ⁻¹ᵁ U).ι :=
    ⟨(ρ ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (ρ ∣_ U) := isDominant_morphismRestrict_integral ρ U
  intro heff
  rw [cartierPullback_morphismRestrict ρ U H]
  exact cartierPullback_effective_of_effective (ρ ∣_ U) (cartierPullback U.ι H) heff

end MixedFujita
