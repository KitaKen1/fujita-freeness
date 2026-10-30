/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantCartierPullback
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
Normality descends through an actual dominant morphism whose maps on regular functions over
every open are bijective. First prove that all regular-function rings on nonempty opens of an
integral scheme with integrally closed stalks are integrally closed: a rational function integral
over the open's ring is integral over every stalk, and the regular germs glue. This argument
does not identify the scheme function field with the fraction field of a nonaffine open.
The descent then uses the actual open ring isomorphism and affine localization at each point.
Neither properness nor Noetherianity is needed for this normality theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped nonZeroDivisors

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Every regular-function ring of a nonempty open is integrally closed in the scheme function
field when all actual stalks are normal. -/
theorem normal_sections_isIntegrallyClosedIn_functionField
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨X.germToFunctionField_injective U, ?_⟩
  intro a ha
  apply exists_germToFunctionField_eq_of_forall_mem_range
  intro x hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  have := functionField_isScalarTower X U ⟨x, hx⟩
  have := hnorm x
  exact IsIntegrallyClosed.isIntegral_iff.mp (ha.tower_top (A := X.presheaf.stalk x))

/-- Normal stalks make the ring of regular functions on every nonempty open integrally closed,
including nonaffine opens and the whole proper scheme. -/
theorem normal_sections_isIntegrallyClosed
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosed Γ(X, U) := by
  have := normal_sections_isIntegrallyClosedIn_functionField hnorm U
  have : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (X.germToFunctionField_injective U)
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn Γ(X, U) X.functionField

variable {Y : Scheme.{u}} [IsIntegral Y] (g : X ⟶ Y) [IsDominant g]

/-- The actual open ring on the target is normal under all-open function bijections. -/
theorem normal_sections_of_all_open_app_bijective
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (happ : ∀ V : Y.Opens, Function.Bijective (g.app V).hom)
    (V : Y.Opens) [Nonempty V] : IsIntegrallyClosed Γ(Y, V) := by
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  have := normal_sections_isIntegrallyClosed hnorm (g ⁻¹ᵁ V)
  exact IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective (g.app V).hom (happ V)).symm

/-- Normality of all actual stalks descends through a dominant map with the Stein all-open
regular-function isomorphism property. -/
theorem normal_stalks_of_all_open_app_bijective
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (happ : ∀ V : Y.Opens, Function.Bijective (g.app V).hom) (y : Y) :
    IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top y)
  letI : Nonempty V := ⟨⟨y, hy⟩⟩
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : V)
  have := hV.isLocalization_stalk (⟨y, hy⟩ : V)
  have := normal_sections_of_all_open_app_bijective g hnorm happ V
  exact isIntegrallyClosed_of_isLocalization (Y.presheaf.stalk y)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl_le_nonZeroDivisors

end MixedFujita
