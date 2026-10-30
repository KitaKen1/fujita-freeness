/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CenteredSmoothCharts
public import MixedFujita.RationalPolynomialCoordinates

/-!
Construct completed power-series coordinates for the actual localization
of a standard smooth K-algebra at a K-rational point. The polynomial chart,
its local extension, localness, and residue-field comparison are constructed.
No coordinate isomorphism is assumed. Transport from a general smooth
scheme point to its actual stalk is not part of this module.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] polynomialVariableIdeal_isMaximal rationalPoint_ker_isMaximal

variable {σ K A : Type*} [Finite σ] [Field K] [CommRing A] [Algebra K A]

theorem centeredEtaleChart_exists_completionCoordinates
    (g : MvPolynomial σ K →ₐ[K] A) (hg : g.Etale)
    (α : A →ₐ[K] K)
    (hc : ∀ p, α (g p) = MvPolynomial.constantCoeff p)
    (S : Type*) [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [IsLocalization.AtPrime S (RingHom.ker α.toRingHom)] [IsLocalRing S] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K] MvPowerSeries σ K,
      (∀ p, e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S
        (algebraMap A S (g p))) = (p : MvPowerSeries σ K)) ∧
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order =
        localAdicOrder S s := by
  let P := MvPolynomial σ K
  let T := Localization.AtPrime (MvPolynomial.idealOfVars σ K)
  let : Algebra P A := g.toRingHom.toAlgebra
  let : IsScalarTower K P A := IsScalarTower.of_algHom g
  let : Algebra P S := Algebra.compHom S g.toRingHom
  let : IsScalarTower P A S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K P S := IsScalarTower.to₁₂₄ K P A S
  let β := rationalPointLocalization α S
  let f : P →ₐ[K] S := (IsScalarTower.toAlgHom K A S).comp g
  have hf : ∀ y : (MvPolynomial.idealOfVars σ K).primeCompl, IsUnit (f y) := by
    intro y
    apply (rationalLocalPoint_isUnit_iff β _).mpr
    have hy : β (f y) = MvPolynomial.constantCoeff (y : P) := by
      exact (rationalPointLocalization_algebraMap α S (g y)).trans (hc y)
    rw [hy]
    exact (polynomialOrigin_notMem_iff (y : P)).mp y.property
  let φ : T →ₐ[K] S := IsLocalization.liftAlgHom hf
  have hφ (p : P) : φ (algebraMap P T p) = algebraMap A S (g p) :=
    IsLocalization.lift_eq hf p
  let : Algebra T S := φ.toRingHom.toAlgebra
  let : IsScalarTower K T S := IsScalarTower.of_algHom φ
  let : IsScalarTower P T S := IsScalarTower.of_algebraMap_eq (fun p => (hφ p).symm)
  let : Algebra.Etale P A := hg
  let : Algebra.FormallyEtale A S :=
    Algebra.FormallyEtale.of_isLocalization (RingHom.ker α.toRingHom).primeCompl
  let : Algebra.FormallyEtale P S := Algebra.FormallyEtale.comp P A S
  let : Algebra.FormallyEtale P T :=
    Algebra.FormallyEtale.of_isLocalization (MvPolynomial.idealOfVars σ K).primeCompl
  let : Algebra.FormallyEtale T S := Algebra.FormallyEtale.of_restrictScalars (R := P)
  let : Algebra.EssFiniteType A S :=
    Algebra.EssFiniteType.of_isLocalization S (RingHom.ker α.toRingHom).primeCompl
  let : Algebra.EssFiniteType P S := Algebra.EssFiniteType.comp P A S
  let : Algebra.EssFiniteType T S := Algebra.EssFiniteType.of_comp P T S
  have hβ (p : P) :
      β (algebraMap T S (algebraMap P T p)) = MvPolynomial.constantCoeff p := by
    change β (φ (algebraMap P T p)) = _
    rw [hφ, rationalPointLocalization_algebraMap, hc]
  refine ⟨rationalEtalePolynomialOriginCoordinates (σ := σ) (K := K) T S β hβ, ?_,
    rationalEtalePolynomialOriginCoordinates_localOrder T S β hβ⟩
  intro p
  rw [← hφ p]
  exact rationalEtalePolynomialOriginCoordinates_polynomial T S β hβ p

theorem standardSmooth_exists_localCompletionCoordinates
    [Algebra.IsStandardSmooth K A] (α : A →ₐ[K] K)
    (S : Type*) [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [IsLocalization.AtPrime S (RingHom.ker α.toRingHom)] [IsLocalRing S] :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K]
      MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order =
        localAdicOrder S s := by
  obtain ⟨n, g, hg, hc⟩ := standardSmooth_exists_centeredEtaleChart α
  obtain ⟨e, _, he⟩ := centeredEtaleChart_exists_completionCoordinates g hg α hc S
  exact ⟨n, e, he⟩

theorem standardSmoothRelativeDimension_exists_localCompletionCoordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (α : A →ₐ[K] K)
    (S : Type*) [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    [IsLocalization.AtPrime S (RingHom.ker α.toRingHom)] [IsLocalRing S] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal S) S s)).order =
        localAdicOrder S s := by
  obtain ⟨g, hg, hc⟩ := standardSmoothRelativeDimension_exists_centeredEtaleChart n α
  obtain ⟨e, _, he⟩ := centeredEtaleChart_exists_completionCoordinates g hg α hc S
  exact ⟨e, he⟩

end MixedFujita
