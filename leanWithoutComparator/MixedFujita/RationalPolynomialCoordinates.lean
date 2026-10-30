/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalLocalPoints

/-!
The actual polynomial-origin local ring has its canonical K-rational point.
A compatible rational point on an essentially finite type formally etale
local target constructs completed power-series coordinates without a
separately supplied residue-field isomorphism or local-hom hypothesis.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] polynomialVariableIdeal_isMaximal

theorem polynomialOrigin_notMem_iff {σ K : Type*} [Field K] (p : MvPolynomial σ K) :
    p ∉ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.constantCoeff p ≠ 0 := by
  rw [polynomialVariableIdeal_eq_ker_constantCoeff, RingHom.mem_ker]

section OriginPoint

variable {σ K : Type*} [Field K]
  (T : Type*) [CommRing T] [Algebra K T] [Algebra (MvPolynomial σ K) T]
  [IsScalarTower K (MvPolynomial σ K) T]
  [IsLocalization.AtPrime T (MvPolynomial.idealOfVars σ K)]

noncomputable def polynomialOriginLocalPoint : T →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := (MvPolynomial.idealOfVars σ K).primeCompl)
    (f := MvPolynomial.aeval (fun _ => 0)) (fun y => by
      apply isUnit_iff_ne_zero.mpr
      have hy : (y : MvPolynomial σ K) ∉ MvPolynomial.idealOfVars σ K := y.property
      have hy' := (polynomialOrigin_notMem_iff (y : MvPolynomial σ K)).mp hy
      simpa using hy')

@[simp]
theorem polynomialOriginLocalPoint_polynomial (p : MvPolynomial σ K) :
    polynomialOriginLocalPoint (σ := σ) (K := K) T
      (algebraMap (MvPolynomial σ K) T p) = MvPolynomial.constantCoeff p := by
  change IsLocalization.lift _ (algebraMap (MvPolynomial σ K) T p) = _
  rw [IsLocalization.lift_eq]
  simp

end OriginPoint

section Coordinates

variable {σ K : Type*} [Finite σ] [Field K]
  (T : Type*) [CommRing T] [Algebra K T] [Algebra (MvPolynomial σ K) T]
  [IsScalarTower K (MvPolynomial σ K) T]
  [IsLocalization.AtPrime T (MvPolynomial.idealOfVars σ K)] [IsLocalRing T]
  (S : Type*) [CommRing S] [Algebra T S] [Algebra K S] [IsScalarTower K T S]
  [IsLocalRing S] [Algebra.EssFiniteType T S] [Algebra.FormallyEtale T S]
  (β : S →ₐ[K] K)
  (h : ∀ p : MvPolynomial σ K,
    β (algebraMap T S (algebraMap (MvPolynomial σ K) T p)) = MvPolynomial.constantCoeff p)

include h

omit [Finite σ] [IsLocalRing T] [IsLocalRing S] [Algebra.EssFiniteType T S]
  [Algebra.FormallyEtale T S] in
theorem rationalPolynomialPoint_compatible (t : T) :
    β (algebraMap T S t) = polynomialOriginLocalPoint (σ := σ) (K := K) T t := by
  have he : β.comp (IsScalarTower.toAlgHom K T S) =
      polynomialOriginLocalPoint (σ := σ) (K := K) T := by
    apply IsLocalization.algHom_ext (MvPolynomial.idealOfVars σ K).primeCompl
    apply AlgHom.ext
    intro p
    exact (h p).trans (polynomialOriginLocalPoint_polynomial T p).symm
  exact congrArg (fun f : T →ₐ[K] K => f t) he

noncomputable def rationalEtalePolynomialOriginCoordinates :
    AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K] MvPowerSeries σ K :=
  ((rationalEtaleLocalCompletionEquiv
    (polynomialOriginLocalPoint (σ := σ) (K := K) T) β
    (rationalPolynomialPoint_compatible T S β h)).symm.restrictScalars K).trans
      (polynomialOriginCompletionCoordinates (σ := σ) (K := K) T)

theorem rationalEtalePolynomialOriginCoordinates_polynomial (p : MvPolynomial σ K) :
    rationalEtalePolynomialOriginCoordinates (σ := σ) (K := K) T S β h
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap T S (algebraMap (MvPolynomial σ K) T p))) = (p : MvPowerSeries σ K) := by
  change polynomialOriginCompletionCoordinates (σ := σ) (K := K) T
    ((rationalEtaleLocalCompletionEquiv _ β _).symm
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap T S (algebraMap (MvPolynomial σ K) T p)))) = _
  rw [← rationalEtaleLocalCompletionEquiv_of
    (polynomialOriginLocalPoint (σ := σ) (K := K) T) β
    (rationalPolynomialPoint_compatible T S β h), AlgEquiv.symm_apply_apply,
    polynomialOriginCompletionCoordinates_polynomial]

theorem rationalEtalePolynomialOriginCoordinates_localOrder (s : S) :
    (rationalEtalePolynomialOriginCoordinates (σ := σ) (K := K) T S β h
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order = localAdicOrder S s := by
  let : IsNoetherianRing T :=
    IsLocalization.isNoetherianRing (M := (MvPolynomial.idealOfVars σ K).primeCompl) T
      inferInstance
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing T S
  exact completionCoordinates_order_eq_localAdicOrder
    (rationalEtalePolynomialOriginCoordinates (σ := σ) (K := K) T S β h).toRingEquiv s

end Coordinates

end MixedFujita
