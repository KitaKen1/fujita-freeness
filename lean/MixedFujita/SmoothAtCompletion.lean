/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothAffineCompletion
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
A finitely presented algebra smooth at a K-rational point has completed
power-series coordinates at its actual local ring. A standard smooth
neighbourhood is obtained from Mathlib, its rational point is constructed,
and localization comparisons return the coordinates to the original ring.
The variable count is existential; comparison with the geometric dimension
and scalar-compatible transport to a general scheme stalk remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] rationalPoint_ker_isMaximal

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem smoothAtRationalPoint_exists_localCompletionCoordinates
    [Algebra.FinitePresentation K A] (α : A →ₐ[K] K)
    [Algebra.IsSmoothAt K (RingHom.ker α.toRingHom)]
    (S : Type*) [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [IsLocalization.AtPrime S (RingHom.ker α.toRingHom)] [IsLocalRing S] :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K]
      MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order =
        localAdicOrder S s := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K
    (RingHom.ker α.toRingHom)
  have hαf : α f ≠ 0 := hf
  let A' := Localization.Away f
  let α' : A' →ₐ[K] K := rationalPointAway α f hαf A'
  let S' := Localization.AtPrime (RingHom.ker α'.toRingHom)
  let : Algebra.IsStandardSmooth K A' := hstd
  let : IsScalarTower K A S' := IsScalarTower.to₁₂₄ K A A' S'
  have hq : (RingHom.ker α'.toRingHom).comap (algebraMap A A') =
      RingHom.ker α.toRingHom := rationalPointAway_ker_comap α f hαf A'
  let : IsLocalization.AtPrime S' (RingHom.ker α.toRingHom) := by
    have H := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) S' (RingHom.ker α'.toRingHom)
    simpa only [hq] using H
  obtain ⟨n, e', _⟩ := standardSmooth_exists_localCompletionCoordinates α' S'
  let c : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K]
      AdicCompletion (IsLocalRing.maximalIdeal S') S' :=
    (((localizationCompletionEquiv (RingHom.ker α.toRingHom) S).symm).trans
      (localizationCompletionEquiv (RingHom.ker α.toRingHom) S')).restrictScalars K
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (M := (RingHom.ker α.toRingHom).primeCompl) S
      inferInstance
  exact ⟨n, c.trans e', fun s =>
    completionCoordinates_order_eq_localAdicOrder (c.trans e').toRingEquiv s⟩

theorem smoothRationalPoint_exists_localCompletionCoordinates [Algebra.Smooth K A]
    (α : A →ₐ[K] K)
    (S : Type*) [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [IsLocalization.AtPrime S (RingHom.ker α.toRingHom)] [IsLocalRing S] :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K]
      MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order =
        localAdicOrder S s :=
  smoothAtRationalPoint_exists_localCompletionCoordinates α S

end MixedFujita
