/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleLocalCoordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
A rational point of a local K-algebra identifies its actual residue field
with K. Compatible rational points construct the residue-field comparison
for an etale local map; the comparison is no longer a separate input.
Rational points also extend to localization at their actual kernels.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

section RationalPoint

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  (α : A →ₐ[K] K)

theorem rationalPoint_surjective : Function.Surjective α :=
  fun k => ⟨algebraMap K A k, α.commutes k⟩

theorem rationalPoint_ker_isMaximal : (RingHom.ker α.toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective α.toRingHom (rationalPoint_surjective α)

variable [IsLocalRing A]

theorem rationalLocalPoint_ker : RingHom.ker α.toRingHom = IsLocalRing.maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal α.toRingHom (rationalPoint_surjective α)

theorem rationalLocalPoint_isUnit_iff (a : A) : IsUnit a ↔ α a ≠ 0 := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← rationalLocalPoint_ker α]
  rfl

noncomputable def rationalLocalPointResidueEquiv :
    (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (rationalLocalPoint_ker α).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (rationalPoint_surjective α))

@[simp]
theorem rationalLocalPointResidueEquiv_mk (a : A) :
    rationalLocalPointResidueEquiv α (Ideal.Quotient.mk _ a) = α a := by
  simp only [rationalLocalPointResidueEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk]
  rfl

end RationalPoint

attribute [local instance] rationalPoint_ker_isMaximal

section Localization

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  (α : A →ₐ[K] K)
  (S : Type*) [CommRing S] [Algebra K S] [Algebra A S]
  [IsScalarTower K A S] [IsLocalization (RingHom.ker α.toRingHom).primeCompl S]

noncomputable def rationalPointLocalization : S →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := (RingHom.ker α.toRingHom).primeCompl)
    (f := α) (fun y => isUnit_iff_ne_zero.mpr y.property)

@[simp]
theorem rationalPointLocalization_algebraMap (a : A) :
    rationalPointLocalization α S (algebraMap A S a) = α a :=
  IsLocalization.lift_eq _ a

end Localization

section AwayPoint

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  (α : A →ₐ[K] K) (a : A) (ha : α a ≠ 0)
  (S : Type*) [CommRing S] [Algebra K S] [Algebra A S]
  [IsScalarTower K A S] [IsLocalization.Away a S]

noncomputable def rationalPointAway : S →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := Submonoid.powers a) (f := α) (fun y => by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.val a).mp y.property
    rw [← hn, map_pow]
    exact (isUnit_iff_ne_zero.mpr ha).pow n)

@[simp]
theorem rationalPointAway_algebraMap (x : A) :
    rationalPointAway α a ha S (algebraMap A S x) = α x :=
  IsLocalization.lift_eq _ x

theorem rationalPointAway_ker_comap :
    (RingHom.ker (rationalPointAway α a ha S).toRingHom).comap (algebraMap A S) =
      RingHom.ker α.toRingHom := by
  ext x
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rationalPointAway_algebraMap]

end AwayPoint

section CompatiblePoints

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S]
  (α : R →ₐ[K] K) (β : S →ₐ[K] K)
  (h : ∀ r, β (algebraMap R S r) = α r)

include h

theorem compatibleRationalPoints_isLocalHom : IsLocalHom (algebraMap R S) := by
  constructor
  intro r hr
  apply (rationalLocalPoint_isUnit_iff α r).mpr
  rw [← h r]
  exact (rationalLocalPoint_isUnit_iff β _).mp hr

noncomputable def compatibleRationalPointsResidueEquiv :
    (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] S ⧸ IsLocalRing.maximalIdeal S where
  __ := ((rationalLocalPointResidueEquiv α).trans
    (rationalLocalPointResidueEquiv β).symm).toRingEquiv
  commutes' r := by
    apply (rationalLocalPointResidueEquiv β).injective
    change rationalLocalPointResidueEquiv β
      ((rationalLocalPointResidueEquiv β).symm
        (rationalLocalPointResidueEquiv α (Ideal.Quotient.mk _ r))) =
      rationalLocalPointResidueEquiv β (Ideal.Quotient.mk _ (algebraMap R S r))
    rw [AlgEquiv.apply_symm_apply, rationalLocalPointResidueEquiv_mk,
      rationalLocalPointResidueEquiv_mk, h r]

@[simp]
theorem compatibleRationalPointsResidueEquiv_mk (r : R) :
    compatibleRationalPointsResidueEquiv α β h (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r) :=
  (compatibleRationalPointsResidueEquiv α β h).commutes r

variable [Algebra.EssFiniteType R S] [Algebra.FormallyEtale R S]

noncomputable def rationalEtaleLocalCompletionEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S := by
  let : IsLocalHom (algebraMap R S) := compatibleRationalPoints_isLocalHom α β h
  exact formallyEtaleLocalCompletionEquiv (compatibleRationalPointsResidueEquiv α β h)

theorem rationalEtaleLocalCompletionEquiv_of (r : R) :
    rationalEtaleLocalCompletionEquiv α β h
      (AdicCompletion.of (IsLocalRing.maximalIdeal R) R r) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S r) :=
  (rationalEtaleLocalCompletionEquiv α β h).commutes r

end CompatiblePoints

end MixedFujita
