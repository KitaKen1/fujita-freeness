/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupExceptionalQuotient
public import MixedFujita.PrincipalExceptionalDVR
public import MixedFujita.TaylorLinearCombination
public import MixedFujita.ProjectiveUniversalNonzeroCharts
public import Hironaka.Scheme.BlowUp.Composite

/-! The actual exceptional prime and DVR of R[m/x_k]. Exact finite order in R
becomes exact order in this DVR. The nonvanishing of the leading form is
transported through the proved polynomial quotient isomorphism. -/

@[expose] public section
open AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R] {n : ℕ}

noncomputable def localPointBlowupExceptionalPrime
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) :
    PrimeSpectrum (affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))) :=
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ
    (localTaylorCoordinate_mem_maximalIdeal ψ T hX hord) k
  ⟨Ideal.span {τ (MvPolynomial.X k)},
    localPointBlowup_exceptionalIdeal_isPrime ψ T hX hord hmax k⟩

omit [IsLocalRing R] in
theorem localPointBlowup_parameter_ne_zero
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i) (k : Fin n) :
    ψ (MvPolynomial.X k) ≠ 0 := by
  intro he
  have h := hX k
  rw [he, map_zero] at h
  exact nonZeroDivisors.ne_zero (MvPowerSeries.X_mem_nonZeroDivisors (R := K) (i := k)) h.symm

theorem localPointBlowup_isDomain [IsDomain R]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i) (k : Fin n) :
    IsDomain (affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))) := by
  have : IsDomain (Localization.Away (ψ (MvPolynomial.X k))) :=
    IsLocalization.Away.isDomain _ (localPointBlowup_parameter_ne_zero ψ T hX k)
  infer_instance

theorem localPointBlowup_exceptional_isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) :
    letI := localPointBlowup_isDomain ψ T hX k
    IsDiscreteValuationRing (Localization.AtPrime
      (localPointBlowupExceptionalPrime ψ T hX hord hmax k).asIdeal) := by
  let A := affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))
  have : IsDomain A := localPointBlowup_isDomain ψ T hX k
  have : IsNoetherianRing A := isNoetherianRing_affineBlowUpAlgebra _ _
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  exact principalPrime_localization_isDiscreteValuationRing
    (localPointBlowupExceptionalPrime ψ T hX hord hmax k).asIdeal (τ (MvPolynomial.X k)) rfl
    (nonZeroDivisors.ne_zero (localPointBlowupPolynomialMap_exceptional_nonZeroDivisor _ ψ hψ k))

theorem localPointBlowup_exact_exceptional_order [IsDomain R] [IsNoetherianRing R]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) (r : R) (d : ℕ) (hr : localAdicOrder R r = (d : ℕ∞)) :
    let p := localPointBlowupExceptionalPrime ψ T hX hord hmax k
    localAdicOrder (Localization.AtPrime p.asIdeal)
      (algebraMap _ (Localization.AtPrime p.asIdeal)
        (algebraMap R (affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))) r)) =
      (d : ℕ∞) := by
  dsimp only
  let A := affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))
  have : IsDomain A := localPointBlowup_isDomain ψ T hX k
  have : IsNoetherianRing A := isNoetherianRing_affineBlowUpAlgebra _ _
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  let p := localPointBlowupExceptionalPrime ψ T hX hord hmax k
  have hTr : (T r).order = (d : ℕ∞) := (hord r).trans hr
  obtain ⟨q, ⟨he, hres⟩, _⟩ :=
    localPointBlowup_germ_exceptional_restriction ψ T hX hord k r d hTr.ge
  have hlead : homogeneousTaylorForm d (T r) ≠ 0 :=
    (homogeneousTaylorForm_nonzero_iff_order d (T r) hTr.ge).mpr hTr
  have hpoly : projectiveDehomogenize K k (homogeneousTaylorForm d (T r)) ≠ 0 :=
    fun h => hlead ((projectiveDehomogenize_eq_zero_iff k d _
      (homogeneousTaylorForm_isHomogeneous d (T r))).mp h)
  have hq : q ∉ p.asIdeal := by
    intro hmem
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    change Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q = 0 at hzero
    rw [hres] at hzero
    exact hpoly ((localPointBlowupExceptionalQuotientEquiv ψ T hX hord hmax k).injective
      (hzero.trans (map_zero _).symm))
  exact principalPrime_localization_order p.asIdeal (τ (MvPolynomial.X k)) rfl
    (nonZeroDivisors.ne_zero (localPointBlowupPolynomialMap_exceptional_nonZeroDivisor _ ψ hψ k))
    (algebraMap R A r) q d he hq

end MixedFujita
