/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeLifts
public import Mathlib.RingTheory.KrullDimension.Field

/-!
Codimension-one stalks of an actual normal locally Noetherian integral scheme are
DVRs. A proper birational morphism lifts each such point to a codimension-one
point with a bijective actual stalk map. Smoothness is not required on the source
or the target of the morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X]

/-- Normality and codimension one supply an actual DVR stalk. -/
theorem normal_codimensionOne_stalk_DVR (x : CodimensionOnePoint X)
    [IsIntegrallyClosed (X.presheaf.stalk (x : X))] :
    IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := by
  let := valuationRing_stalk_of_coheight_eq_one (x : X) x.property
  have hdim : ringKrullDim (X.presheaf.stalk (x : X)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, x.property, WithBot.coe_one]
  have hnfield : ¬ IsField (X.presheaf.stalk (x : X)) := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hz
    exact one_ne_zero hz
  have hval : ValuationRing (X.presheaf.stalk (x : X)) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (x : X)) hnfield).out 1 2).mpr hval

/-- Birationality gives a stalk isomorphism above a normal codimension-one point. -/
theorem stalkMap_bijective_of_birational_over_normal_prime
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (ρ : T ⟶ X) [IsDominant ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom) (t : T)
    (hξ : Order.coheight (ρ t) = 1) : Function.Bijective (ρ.stalkMap t) := by
  let := hnorm (ρ t)
  let := valuationRing_stalk_of_coheight_eq_one (ρ t) hξ
  exact stalkMap_bijective_of_birational_valuation_stalk ρ hρ t

/-- Properness supplies an actual prime lift over every normal target prime. -/
theorem proper_birational_exists_normal_prime_lift
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (x : CodimensionOnePoint X) :
    ∃ t : CodimensionOnePoint T, ρ (t : T) = (x : X) ∧
      Function.Bijective (ρ.stalkMap (t : T)) := by
  obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant ρ (x : X)
  have hξ : Order.coheight (ρ t) = 1 := by simpa only [ht] using x.property
  have hb := stalkMap_bijective_of_birational_over_normal_prime hnorm ρ hρ t hξ
  have hcod : Order.coheight t = 1 := (coheight_eq_of_stalkMap_bijective ρ t hb).trans hξ
  exact ⟨⟨t, hcod⟩, ht, hb⟩

end MixedFujita
