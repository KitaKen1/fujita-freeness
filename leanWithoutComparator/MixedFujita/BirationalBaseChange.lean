/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
Base change of a flat domain along a birational map of domains (step 12, section 6.1 of the
manuscript). Let A be a domain, A → A' a ring map into a ring whose fraction field F is also a
fraction field of A (the map is birational), and R a flat domain over A in which A is faithful.
Then A' ⊗_A R embeds in F ⊗_A R, the localization of R at the nonzero elements of A: flatness of R
preserves the injection A' → F. Hence A' ⊗_A R is a domain, R embeds in it, and every element of
it is a quotient of two elements of R: the base change is birational to R. A pair of ring maps
from A' and from R to a commutative ring agreeing on A gives a ring map from the base change.
-/

@[expose] public section

open TensorProduct
open scoped nonZeroDivisors

namespace MixedFujita

section Point

variable {A A' R κ : Type*} [CommRing A] [CommRing A'] [CommRing R] [Algebra A A'] [Algebra A R]
  [CommRing κ]

/-- Two ring maps to a commutative ring agreeing on the base give a ring map from the base
change. -/
theorem baseChange_exists_ringHom (τ : A' →+* κ) (ρ : R →+* κ)
    (h : ∀ a : A, τ (algebraMap A A' a) = ρ (algebraMap A R a)) :
    ∃ π : A' ⊗[A] R →+* κ, ∀ (a : A') (r : R), π (a ⊗ₜ r) = τ a * ρ r := by
  let _ : Algebra A κ := (τ.comp (algebraMap A A')).toAlgebra
  let f : A' →ₐ[A] κ := { τ with commutes' := fun _ => rfl }
  let g : R →ₐ[A] κ := { ρ with commutes' := fun a => (h a).symm }
  exact ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun a r =>
    Algebra.TensorProduct.productMap_apply_tmul f g a r⟩

end Point

variable {A A' R F : Type*} [CommRing A] [IsDomain A] [CommRing A'] [CommRing R] [IsDomain R]
  [Algebra A A'] [Algebra A R] [Module.Flat A R] [FaithfulSMul A R]
  [Field F] [Algebra A' F] [Algebra A F] [IsScalarTower A A' F] [IsFractionRing A F]

omit [Module.Flat A R] in
/-- The nonzero elements of the base are nonzero in a domain in which the base is faithful. -/
theorem faithfulDomain_base_denominators_nonZero : Algebra.algebraMapSubmonoid R A⁰ ≤ R⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A R)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp ha))

variable (A A' R F) in
/-- The comparison map from the base change to the base change of the fraction field. -/
noncomputable def baseChangeToFraction : A' ⊗[A] R →ₐ[A] F ⊗[A] R :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' F) (AlgHom.id A R)

omit [IsDomain A] [IsDomain R] [Module.Flat A R] [FaithfulSMul A R] [IsFractionRing A F] in
theorem baseChangeToFraction_tmul (a : A') (r : R) :
    baseChangeToFraction A A' R F (a ⊗ₜ r) = algebraMap A' F a ⊗ₜ r :=
  rfl

omit [IsDomain A] [IsDomain R] [FaithfulSMul A R] [IsFractionRing A F] in
/-- Flatness preserves the injection of the ring into its fraction field. -/
theorem baseChangeToFraction_injective (hF : Function.Injective (algebraMap A' F)) :
    Function.Injective (baseChangeToFraction A A' R F) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := R)
    (IsScalarTower.toAlgHom A A' F).toLinearMap hF
  have heq : ∀ x, baseChangeToFraction A A' R F x =
      (IsScalarTower.toAlgHom A A' F).toLinearMap.rTensor R x := by
    intro x
    induction x with
    | tmul a r => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  apply h
  rw [← heq, ← heq, hxy]

omit [Module.Flat A R] in
/-- The domain embeds in its base change along a birational map. -/
theorem birationalBaseChange_includeRight_injective (F₀ : Type*) [Field F₀] [Algebra A' F₀]
    [Algebra A F₀] [IsScalarTower A A' F₀] [IsFractionRing A F₀] :
    Function.Injective fun r : R => (1 : A') ⊗ₜ[A] r := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := A) (A := F₀) (B := R)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid R A⁰) (F₀ ⊗[A] R) :=
    IsLocalization.tensorRight F₀ A⁰
  have hinj : Function.Injective (algebraMap R (F₀ ⊗[A] R)) :=
    IsLocalization.injective (F₀ ⊗[A] R)
      (faithfulDomain_base_denominators_nonZero (A := A) (R := R))
  intro r r' hrr
  apply hinj
  have h := congrArg (baseChangeToFraction A A' R F₀) hrr
  rw [baseChangeToFraction_tmul, baseChangeToFraction_tmul, map_one] at h
  exact h

section Main

variable (hF : Function.Injective (algebraMap A' F))

include hF

/-- The base change of a flat domain along a birational map is a domain. -/
theorem birationalBaseChange_isDomain : IsDomain (A' ⊗[A] R) := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := A) (A := F) (B := R)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid R A⁰) (F ⊗[A] R) :=
    IsLocalization.tensorRight F A⁰
  have : IsDomain (F ⊗[A] R) := IsLocalization.isDomain_of_le_nonZeroDivisors (F ⊗[A] R)
    (faithfulDomain_base_denominators_nonZero (A := A) (R := R))
  exact Function.Injective.isDomain (baseChangeToFraction A A' R F)
    (baseChangeToFraction_injective (A := A) (R := R) hF)

/-- Every element of the base change along a birational map is a quotient of two elements of the
flat domain. -/
theorem birationalBaseChange_exists_fraction (b : A' ⊗[A] R) :
    ∃ r s : R, s ≠ 0 ∧ ((1 : A') ⊗ₜ[A] s) * b = (1 : A') ⊗ₜ[A] r := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := A) (A := F) (B := R)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid R A⁰) (F ⊗[A] R) :=
    IsLocalization.tensorRight F A⁰
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid R A⁰)
    (baseChangeToFraction A A' R F b)
  refine ⟨r, s, nonZeroDivisors.ne_zero
    (faithfulDomain_base_denominators_nonZero (A := A) (R := R) s.property), ?_⟩
  apply baseChangeToFraction_injective (A := A) (R := R) hF
  rw [map_mul, baseChangeToFraction_tmul, baseChangeToFraction_tmul, map_one, mul_comm]
  exact hrs

end Main

end MixedFujita
