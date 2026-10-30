/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DVRVanishingOrder
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! A nonzero principal prime in a Noetherian domain gives an actual DVR.
Its generator is a uniformizer, and a factor outside the prime is a unit,
so a factorization determines the intrinsic order exactly. -/

@[expose] public section
namespace MixedFujita
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

omit [IsDomain A] [IsNoetherianRing A] in
theorem principalPrime_localization_maximalIdeal (p : Ideal A) [p.IsPrime]
    (a : A) (hp : p = Ideal.span {a}) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) =
      Ideal.span {algebraMap A (Localization.AtPrime p) a} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact (congrArg (Ideal.map (algebraMap A (Localization.AtPrime p))) hp).trans
    (by rw [Ideal.map_span, Set.image_singleton])

theorem principalPrime_localization_isDiscreteValuationRing (p : Ideal A) [p.IsPrime]
    (a : A) (hp : p = Ideal.span {a}) (ha : a ≠ 0) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let L := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L p.primeCompl_le_nonZeroDivisors
  have hne : algebraMap A L a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero _).symm))
  have hm := principalPrime_localization_maximalIdeal p a hp
  have hprincipal : (IsLocalRing.maximalIdeal L).IsPrincipal := by
    rw [hm]
    infer_instance
  have : IsPrincipalIdealRing L :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain L).out 5 1).mp hprincipal
  refine { not_a_field' := ?_ }
  intro hbot
  have hmem : algebraMap A L a ∈ IsLocalRing.maximalIdeal L := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact hne hmem

theorem principalPrime_localization_order (p : Ideal A) [p.IsPrime]
    (a : A) (hp : p = Ideal.span {a}) (ha : a ≠ 0)
    (r q : A) (d : ℕ) (hr : r = a ^ d * q) (hq : q ∉ p) :
    localAdicOrder (Localization.AtPrime p)
      (algebraMap A (Localization.AtPrime p) r) = (d : ℕ∞) := by
  let L := Localization.AtPrime p
  let := principalPrime_localization_isDiscreteValuationRing p a hp ha
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L p.primeCompl_le_nonZeroDivisors
  have hne : algebraMap A L a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero _).symm))
  have hirr : Irreducible (algebraMap A L a) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne
      (principalPrime_localization_maximalIdeal p a hp)
  have hu : IsUnit (algebraMap A L q) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff L p q).mpr hq
  rw [dvr_localAdicOrder_eq_addVal, hr, map_mul, map_pow,
    IsDiscreteValuationRing.addVal_mul, hirr.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, add_zero]

theorem ringEquiv_dvr_structure {B L : Type*} [CommRing B] [CommRing L]
    [IsDomain L] [IsDiscreteValuationRing L] (e : B ≃+* L) :
    ∃ hB : IsDomain B, @IsDiscreteValuationRing B _ hB := by
  have hB : IsDomain B := e.toMulEquiv.isDomain L
  let := hB
  exact ⟨hB, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm⟩

end MixedFujita
