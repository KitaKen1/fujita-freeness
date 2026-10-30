/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalHartogs
public import MixedFujita.CartierSectionSNCPerturbation

/-!
On a normal locally Noetherian integral scheme with DVR codimension-one stalks, a rational
unit of order zero on an open neighborhood is the image of an actual local unit. Equal
codimension-one orders therefore identify two rational equations up to a stalk unit.
This uses Hartogs for the function and its inverse, and bypasses local factoriality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The function-field image of an actual stalk unit has order zero. -/
theorem scheme_ord_stalk_unit (x : X) (u : (X.presheaf.stalk x)ˣ) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField u) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    have hne : algebraMap (X.presheaf.stalk x) X.functionField u ≠ 0 :=
      (u.isUnit.map _).ne_zero
    rw [X.ord_eq_iff hx hne]
    exact Ring.ordFrac_of_isUnit u.isUnit
  · exact X.ord_eq_zero_of_coheight_neq_one hx _

/-- Order zero at a DVR point is represented by an actual stalk unit. -/
theorem scheme_ord_zero_exists_stalk_unit (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (f : X.functionFieldˣ) (hf : X.ord (f : X.functionField) (x : X) = 0) :
    ∃ u : (X.presheaf.stalk (x : X))ˣ,
      algebraMap (X.presheaf.stalk (x : X)) X.functionField u = (f : X.functionField) := by
  have hf' : Ring.ordFrac (X.presheaf.stalk (x : X)) (f : X.functionField) = 1 := by
    have h := (X.ord_eq_iff x.property (Units.ne_zero f)).mp hf
    exact h
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := X.presheaf.stalk (x : X))
    (1 : X.functionField) (f : X.functionField) (by simpa using hf'.symm)
  exact ⟨u, by simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hu⟩

/-- Two-sided Hartogs turns zero orders throughout a neighborhood into a unit at its point. -/
theorem normal_scheme_ord_zero_exists_stalk_unit
    [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (x : X) (W : X.Opens) (hx : x ∈ W) (f : X.functionFieldˣ)
    (hf : ∀ z : CodimensionOnePoint X, (z : X) ∈ W → X.ord (f : X.functionField) (z : X) = 0) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField u = (f : X.functionField) := by
  have hreg : (f : X.functionField) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    apply mem_range_stalk_of_codimOne hnorm x W hx
    intro z hz hcod
    obtain ⟨u, hu⟩ := scheme_ord_zero_exists_stalk_unit ⟨z, hcod⟩ f (hf ⟨z, hcod⟩ hz)
    exact ⟨u, hu⟩
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    apply mem_range_stalk_of_codimOne hnorm x W hx
    intro z hz hcod
    obtain ⟨u, hu⟩ := scheme_ord_zero_exists_stalk_unit ⟨z, hcod⟩ f (hf ⟨z, hcod⟩ hz)
    exact ⟨(u⁻¹ : (X.presheaf.stalk z)ˣ), by rw [map_units_inv, hu, Units.val_inv_eq_inv_val]⟩
  obtain ⟨a, ha⟩ := hreg
  obtain ⟨b, hb⟩ := hinv
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hab : a * b = 1 := by
    apply hinj
    rw [map_mul, ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact ⟨⟨a, b, hab, by simpa only [mul_comm] using hab⟩, ha⟩

/-- Equal orders on a neighborhood give the explicit unit ratio of two rational equations. -/
theorem normal_scheme_equal_orders_unit_ratio
    [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (x : X) (W : X.Opens) (hx : x ∈ W) (f g : X.functionFieldˣ)
    (hfg : ∀ z : CodimensionOnePoint X, (z : X) ∈ W →
      X.ord (f : X.functionField) (z : X) = X.ord (g : X.functionField) (z : X)) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField u * g := by
  obtain ⟨u, hu⟩ := normal_scheme_ord_zero_exists_stalk_unit hnorm x W hx (f * g⁻¹) (by
    intro z hz
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Scheme.ord_mul (Units.ne_zero f)
      (inv_ne_zero (Units.ne_zero g)), TauCeti.AlgebraicGeometry.Scheme.ord_inv, hfg z hz,
      add_neg_cancel])
  refine ⟨u, ?_⟩
  rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, inv_mul_cancel₀ (Units.ne_zero g),
    mul_one]

end MixedFujita
