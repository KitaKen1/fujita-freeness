/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FormallyEtaleQuotients
public import MixedFujita.PolynomialOriginCoordinates
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
An essentially finite type formally etale local algebra with the same
residue field has an isomorphic completed local ring. For an actual
polynomial-origin local source, this constructs power-series coordinates
and identifies their order with the intrinsic local adic order. An etale
local chart and its residue-field isomorphism are inputs; deriving such
a chart from an arbitrary smooth scheme point remains unfinished.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

section LocalComparison

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.EssFiniteType R S] [Algebra.FormallyEtale R S]
  (e : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] S ⧸ IsLocalRing.maximalIdeal S)

include e

noncomputable def formallyEtaleLocalCompletionEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal S) S := by
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  exact (formallyEtaleCompletionEquiv (I := IsLocalRing.maximalIdeal R) (S := S)
    (e := e.trans (Ideal.quotientEquivAlgOfEq R hm.symm))).trans
      (adicCompletionIdealEquiv (B := R) _ _ hm)

theorem formallyEtaleLocalCompletionEquiv_of (r : R) :
    formallyEtaleLocalCompletionEquiv e
      (AdicCompletion.of (IsLocalRing.maximalIdeal R) R r) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S r) :=
  (formallyEtaleLocalCompletionEquiv e).commutes r

end LocalComparison

attribute [local instance] polynomialVariableIdeal_isMaximal

section PolynomialChart

variable {σ K : Type*} [Finite σ] [Field K]
  (T : Type*) [CommRing T] [Algebra K T] [Algebra (MvPolynomial σ K) T]
  [IsScalarTower K (MvPolynomial σ K) T]
  [IsLocalization.AtPrime T (MvPolynomial.idealOfVars σ K)] [IsLocalRing T]
  (S : Type*) [CommRing S] [Algebra T S] [Algebra K S] [IsScalarTower K T S]
  [IsLocalRing S] [IsLocalHom (algebraMap T S)]
  [Algebra.EssFiniteType T S] [Algebra.FormallyEtale T S]
  (e : (T ⧸ IsLocalRing.maximalIdeal T) ≃ₐ[T] S ⧸ IsLocalRing.maximalIdeal S)

noncomputable def etalePolynomialOriginCompletionCoordinates :
    AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K] MvPowerSeries σ K :=
  ((formallyEtaleLocalCompletionEquiv e).symm.restrictScalars K).trans
    (polynomialOriginCompletionCoordinates (σ := σ) (K := K) T)

theorem etalePolynomialOriginCompletionCoordinates_base (t : T) :
    etalePolynomialOriginCompletionCoordinates (σ := σ) (K := K) T S e
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap T S t)) =
      polynomialOriginCompletionCoordinates (σ := σ) (K := K) T
        (AdicCompletion.of (IsLocalRing.maximalIdeal T) T t) := by
  change polynomialOriginCompletionCoordinates (σ := σ) (K := K) T
    ((formallyEtaleLocalCompletionEquiv e).symm
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap T S t))) = _
  rw [← formallyEtaleLocalCompletionEquiv_of e t, AlgEquiv.symm_apply_apply]

theorem etalePolynomialOriginCompletionCoordinates_polynomial (p : MvPolynomial σ K) :
    etalePolynomialOriginCompletionCoordinates (σ := σ) (K := K) T S e
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap T S (algebraMap (MvPolynomial σ K) T p))) = (p : MvPowerSeries σ K) := by
  rw [etalePolynomialOriginCompletionCoordinates_base,
    polynomialOriginCompletionCoordinates_polynomial]

theorem etalePolynomialOriginCompletionCoordinates_localOrder (s : S) :
    (etalePolynomialOriginCompletionCoordinates (σ := σ) (K := K) T S e
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order = localAdicOrder S s := by
  let : IsNoetherianRing T :=
    IsLocalization.isNoetherianRing (M := (MvPolynomial.idealOfVars σ K).primeCompl) T
      inferInstance
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing T S
  exact completionCoordinates_order_eq_localAdicOrder
    (etalePolynomialOriginCompletionCoordinates (σ := σ) (K := K) T S e).toRingEquiv s

end PolynomialChart

end MixedFujita
