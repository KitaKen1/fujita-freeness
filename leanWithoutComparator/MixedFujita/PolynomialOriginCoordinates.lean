/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalizationCompletion
public import MixedFujita.LocalAdicOrder
public import Mathlib.RingTheory.Localization.Submodule

/-!
Construct completion coordinates for the actual localization of a finite
polynomial algebra at its origin. The coefficient field structure and the
images of every polynomial are respected. This is a genuine coordinate
existence theorem for this local model, not a theorem that every smooth
local ring has such coordinates; the etale comparison remains separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

theorem polynomialVariableIdeal_eq_ker_constantCoeff {σ R : Type*} [CommRing R] :
    MvPolynomial.idealOfVars σ R = RingHom.ker
      (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) := by
  ext p
  rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff',
    RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h x hx
    have hz : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
    simpa only [hz] using h

theorem polynomialVariableIdeal_isMaximal {σ K : Type*} [Field K] :
    (MvPolynomial.idealOfVars σ K).IsMaximal := by
  rw [polynomialVariableIdeal_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun k => ⟨MvPolynomial.C k, by simp⟩)

attribute [local instance] polynomialVariableIdeal_isMaximal

variable {σ K : Type*} [Finite σ] [Field K]
  (S : Type*) [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
  [IsScalarTower K (MvPolynomial σ K) S]
  [IsLocalization.AtPrime S (MvPolynomial.idealOfVars σ K)] [IsLocalRing S]

noncomputable def polynomialOriginCompletionCoordinates :
    AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K] MvPowerSeries σ K :=
  ((localizationCompletionEquiv (MvPolynomial.idealOfVars σ K) S).symm.restrictScalars K).trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv σ K).symm.restrictScalars K)

theorem polynomialOriginCompletionCoordinates_polynomial (p : MvPolynomial σ K) :
    polynomialOriginCompletionCoordinates (σ := σ) (K := K) S
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap (MvPolynomial σ K) S p)) = (p : MvPowerSeries σ K) := by
  change (MvPowerSeries.toAdicCompletionAlgEquiv σ K).symm
    ((localizationCompletionEquiv (MvPolynomial.idealOfVars σ K) S).symm
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap (MvPolynomial σ K) S p))) = _
  rw [← localizationCompletionEquiv_of (MvPolynomial.idealOfVars σ K) S p,
    AlgEquiv.symm_apply_apply]
  apply (MvPowerSeries.toAdicCompletionAlgEquiv σ K).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (MvPowerSeries.toAdicCompletion_coe p).symm

theorem polynomialOriginCompletionCoordinates_variable (i : σ) :
    polynomialOriginCompletionCoordinates (σ := σ) (K := K) S
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))) = MvPowerSeries.X i := by
  rw [polynomialOriginCompletionCoordinates_polynomial, MvPolynomial.coe_X]

theorem polynomialOriginCompletionCoordinates_localOrder [IsNoetherianRing S] (r : S) :
    (polynomialOriginCompletionCoordinates (σ := σ) (K := K) S
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S r)).order = localAdicOrder S r :=
  completionCoordinates_order_eq_localAdicOrder
    (polynomialOriginCompletionCoordinates (σ := σ) (K := K) S).toRingEquiv r

noncomputable def polynomialOriginLocalCoordinates (σ K : Type*) [Finite σ] [Field K] :
    AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime (MvPolynomial.idealOfVars σ K)))
      (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) ≃ₐ[K] MvPowerSeries σ K :=
  polynomialOriginCompletionCoordinates (Localization.AtPrime (MvPolynomial.idealOfVars σ K))

theorem polynomialOriginLocalCoordinates_polynomial (p : MvPolynomial σ K) :
    polynomialOriginLocalCoordinates σ K
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime (MvPolynomial.idealOfVars σ K)))
        (Localization.AtPrime (MvPolynomial.idealOfVars σ K))
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) p)) =
      (p : MvPowerSeries σ K) :=
  polynomialOriginCompletionCoordinates_polynomial _ p

theorem polynomialOriginLocalCoordinates_localOrder
    (r : Localization.AtPrime (MvPolynomial.idealOfVars σ K)) :
    (polynomialOriginLocalCoordinates σ K
      (AdicCompletion.of
        (IsLocalRing.maximalIdeal (Localization.AtPrime (MvPolynomial.idealOfVars σ K)))
        (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) r)).order =
      localAdicOrder (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) r := by
  let : IsNoetherianRing (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) :=
    IsLocalization.isNoetherianRing (M := (MvPolynomial.idealOfVars σ K).primeCompl)
      (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) inferInstance
  exact polynomialOriginCompletionCoordinates_localOrder _ r

end MixedFujita
