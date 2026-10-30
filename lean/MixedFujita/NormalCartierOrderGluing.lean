/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierCoefficientExt
public import MixedFujita.RegularEquationCartier
public import OAI.AlgebraicGeometry.SectionFields.NormalDivisors

/-!
On an arbitrary-dimensional normal Noetherian integral scheme, actual local
rational equations with the specified codimension-one orders glue to one
actual Cartier divisor. Hartogs supplies regular unit transition functions.
This extends the curve-only Cartier/Weil gluing dictionary to the normal
case without asserting that every Weil divisor is Cartier.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- Equal orders on a nonempty normal open give a regular unit transition over that whole open. -/
theorem normal_equal_orders_exists_regularUnit_ratio_on_open
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hord : ∀ z : CodimensionOnePoint X, (z : X) ∈ U →
      X.ord (f : X.functionField) (z : X) = X.ord (g : X.functionField) (z : X)) :
    ∃ w : Γ(X, U)ˣ, f = Units.map (X.germToFunctionField U).hom w * g := by
  obtain ⟨w, hw⟩ := OAI.RelativeDenominators.exists_section_unit_of_ord_eq_zero
    X hnorm U (f * g⁻¹) (by
      intro z hz hcod
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Scheme.ord_mul (Units.ne_zero f)
        (inv_ne_zero (Units.ne_zero g)), TauCeti.AlgebraicGeometry.Scheme.ord_inv,
        hord ⟨z, hcod⟩ hz, add_neg_cancel])
  have heq : Units.map (X.germToFunctionField U).hom w = f * g⁻¹ := by
    apply Units.ext
    exact hw
  refine ⟨w, ?_⟩
  rw [heq]
  group

/-- Actual local order equations construct one unique Cartier divisor on a normal Noetherian scheme. -/
theorem normal_existsUnique_cartier_of_local_orders
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (b : CodimensionOnePoint X → ℤ)
    (hloc : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ f : X.functionFieldˣ,
      ∀ z : CodimensionOnePoint X, (z : X) ∈ U → X.ord (f : X.functionField) (z : X) = b z) :
    ∃! D : CartierDivisor X, ∀ z : CodimensionOnePoint X, cartierCoefficient D (z : X) = b z := by
  classical
  choose U hmem f hord using hloc
  letI : ∀ x : X, Nonempty (U x) := fun x => ⟨⟨x, hmem x⟩⟩
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hmem x⟩
  obtain ⟨D, hD, _⟩ := cartierDivisor_existsUnique_of_rationalUnits X U hcover f (by
    intro i j
    letI := integral_opens_inter_nonempty X (U i) (U j)
    exact normal_equal_orders_exists_regularUnit_ratio_on_open hnorm (U i ⊓ U j) (f i) (f j)
      (fun z hz => (hord i z hz.1).trans (hord j z hz.2).symm))
  have hcoeff : ∀ z : CodimensionOnePoint X, cartierCoefficient D (z : X) = b z := by
    intro z
    rw [cartierCoefficient_eq_ord
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hD (z : X)).symm (hmem (z : X)))]
    exact hord (z : X) z (hmem (z : X))
  refine ⟨D, hcoeff, ?_⟩
  intro E hE
  exact cartierDivisor_eq_of_forall_coefficient_eq hnorm E D (fun z => (hE z).trans (hcoeff z).symm)

end MixedFujita
