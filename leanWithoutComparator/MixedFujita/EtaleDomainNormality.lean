/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
Normality of an étale domain over a normal domain, via its generic fiber.
The generic fiber is a domain and an étale algebra over the base fraction field,
so it is a field. Smooth base change of integral closure then gives normality.
This avoids constructing a general regular-local-ring factoriality theorem.
-/

@[expose] public section

open TensorProduct
open scoped nonZeroDivisors

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.Etale R S]

/-- Flatness sends nonzero base denominators to nonzero elements of the domain. -/
theorem etale_base_denominators_nonZero : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  have hinj : Function.Injective (algebraMap R S) :=
    FaithfulSMul.algebraMap_injective R S
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp ha))

/-- Generic localization of an étale domain remains a domain. -/
theorem etale_genericFiber_isDomain : IsDomain (S ⊗[R] FractionRing R) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (S ⊗[R] FractionRing R)
    (etale_base_denominators_nonZero (R := R) (S := S))

/-- The generic fiber is a field because an étale algebra over a field is Artinian. -/
theorem etale_genericFiber_isField : IsField (S ⊗[R] FractionRing R) := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := FractionRing R)
  have : Algebra.Etale (FractionRing R) (S ⊗[R] FractionRing R) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R (FractionRing R) S)
  have := etale_genericFiber_isDomain (R := R) (S := S)
  have := Algebra.FormallyUnramified.finite_of_free (FractionRing R)
    (S ⊗[R] FractionRing R)
  have : IsArtinianRing (S ⊗[R] FractionRing R) :=
    isArtinian_of_tower (FractionRing R) inferInstance
  exact IsArtinianRing.isField_of_isDomain _

/-- The generic fiber is the actual fraction field of the étale domain. -/
theorem etale_genericFiber_isFractionRing : IsFractionRing S (S ⊗[R] FractionRing R) := by
  let := (etale_genericFiber_isField (R := R) (S := S)).toField
  have hinj : Function.Injective (algebraMap S (S ⊗[R] FractionRing R)) := by
    exact IsLocalization.injective (S ⊗[R] FractionRing R)
      (etale_base_denominators_nonZero (R := R) (S := S))
  let : FaithfulSMul S (S ⊗[R] FractionRing R) :=
    (faithfulSMul_iff_algebraMap_injective S (S ⊗[R] FractionRing R)).mpr hinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid S R⁰) z
  have hb : algebraMap S (S ⊗[R] FractionRing R) b ≠ 0 :=
    (IsLocalization.map_units (S ⊗[R] FractionRing R) b).ne_zero
  exact ⟨a, b, (eq_div_iff_mul_eq hb).mpr hab⟩

/-- An étale integral domain over a normal domain is normal. -/
theorem etaleDomain_isIntegrallyClosed [IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  let := (etale_genericFiber_isField (R := R) (S := S)).toField
  have := etale_genericFiber_isFractionRing (R := R) (S := S)
  refine (isIntegrallyClosed_iff (S ⊗[R] FractionRing R)).mpr ?_
  intro y hy
  obtain ⟨x, hx⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := S) (B := FractionRing R)).surjective ⟨y, hy⟩
  have hmem : ∀ x : S ⊗[R] integralClosure R (FractionRing R),
      ((TensorProduct.toIntegralClosure R S (FractionRing R)) x : S ⊗[R] FractionRing R) ∈
        (algebraMap S (S ⊗[R] FractionRing R)).range := by
    intro x
    induction x with
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp only [map_add, ha, hb, Subalgebra.coe_add]⟩
    | tmul s z =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp z.property
      refine ⟨s * algebraMap R S r, ?_⟩
      simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, ← hr]
      simpa only [Algebra.smul_def, mul_one, one_mul, mul_comm] using
        (TensorProduct.smul_tmul (R := R) r s (1 : FractionRing R))
  simpa only [hx, RingHom.mem_range] using hmem x

end MixedFujita
