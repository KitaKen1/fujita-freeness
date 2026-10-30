/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupFormalChart
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! The exceptional quotient of the actual local blow-up chart is the
polynomial ring in the remaining coordinates. Surjectivity uses actual
fractions and the leading-jet formula. Injectivity uses the constructed
formal chart map, followed by setting the exceptional coordinate to zero. -/

@[expose] public section
open AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R A : Type*} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
  [CommRing A] {n : ℕ}

theorem pointBlowupExceptionalEvaluation_injective_of_formalChart
    (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n)
    (ν : A →+* MvPowerSeries (Fin n) K)
    (hν : ∀ g, ν (τ g) = (g : MvPowerSeries (Fin n) K)) :
    Function.Injective (pointBlowupExceptionalEvaluation τ k) := by
  let ρ := (pointBlowupExceptionalRestriction (K := K) k).toRingHom.comp ν
  have hzero : ρ (τ (MvPolynomial.X k)) = 0 := by
    change pointBlowupExceptionalRestriction k (ν (τ (MvPolynomial.X k))) = 0
    rw [hν, MvPolynomial.coe_X]
    apply MvPowerSeries.killCompl_X_eq_zero
    rintro ⟨i, hi⟩
    exact i.property hi
  have hker : Ideal.span {τ (MvPolynomial.X k)} ≤ RingHom.ker ρ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hzero
  let δ := Ideal.Quotient.lift _ ρ (fun a ha => hker ha)
  have he (g : MvPolynomial {i : Fin n // i ≠ k} K) :
      δ (pointBlowupExceptionalEvaluation τ k g) = (g : MvPowerSeries _ K) := by
    have hXi (i : {i : Fin n // i ≠ k}) :
        δ (pointBlowupExceptionalEvaluation τ k (MvPolynomial.X i)) = MvPowerSeries.X i := by
      rw [pointBlowupExceptionalEvaluation_X, Ideal.Quotient.lift_mk]
      change pointBlowupExceptionalRestriction k (ν (τ (MvPolynomial.X i.1))) = _
      rw [hν, MvPolynomial.coe_X]
      exact MvPowerSeries.killCompl_X i
    induction g using MvPolynomial.induction_on with
    | C c =>
      rw [pointBlowupExceptionalEvaluation_C, Ideal.Quotient.lift_mk]
      change pointBlowupExceptionalRestriction k (ν (τ (MvPolynomial.C c))) = _
      simp only [hν, MvPolynomial.coe_C]
      exact MvPowerSeries.killCompl_C c
    | add g h hg hh => simp only [map_add, MvPolynomial.coe_add, hg, hh]
    | mul_X g i hg => simp only [map_mul, MvPolynomial.coe_mul, MvPolynomial.coe_X, hg, hXi]
  intro g h hgh
  apply MvPolynomial.coe_injective _ K
  exact (he g).symm.trans ((congrArg δ hgh).trans (he h))

theorem localPointBlowup_exceptionalEvaluation_surjective
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r) (k : Fin n) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    Function.Surjective (pointBlowupExceptionalEvaluation
      (localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k) k) := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  intro z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨m, r, hr, he⟩ := (affineBlowUpAlgebra.mem_iff (hψ k) q).mp q.2
  have hordr : (m : ℕ∞) ≤ (T r).order := by
    rw [hord, localAdicOrder_nat_le_iff]
    exact hr
  obtain ⟨q', ⟨hq', hres⟩, _⟩ :=
    localPointBlowup_germ_exceptional_restriction ψ T hX hord k r m hordr
  have hq : algebraMap R _ r = τ (MvPolynomial.X k) ^ m * q := by
    rw [localPointBlowupPolynomialMap_X_self]
    exact (mul_comm _ _).trans (Subtype.ext he) |>.symm
  have heq : q' = q := localPointBlowupStrictTransform_unique _ ψ hψ k m r q' q hq' hq
  exact ⟨projectiveDehomogenize K k (homogeneousTaylorForm m (T r)),
    hres.symm.trans (congrArg (Ideal.Quotient.mk _) heq)⟩

noncomputable def localPointBlowupExceptionalQuotientEquiv
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
    MvPolynomial {i : Fin n // i ≠ k} K ≃+*
      affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)) ⧸
        Ideal.span {τ (MvPolynomial.X k)} := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  have hinj : Function.Injective (pointBlowupExceptionalEvaluation
      (localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k) k) := by
    obtain ⟨ν, _, hν⟩ := localPointBlowup_exists_formalChart ψ T hX hmax hψ k
    exact pointBlowupExceptionalEvaluation_injective_of_formalChart _ k ν hν
  exact RingEquiv.ofBijective _
    ⟨hinj,
      localPointBlowup_exceptionalEvaluation_surjective ψ T hX hord k⟩

theorem localPointBlowupExceptionalQuotientEquiv_apply
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) (g : MvPolynomial {i : Fin n // i ≠ k} K) :
    localPointBlowupExceptionalQuotientEquiv ψ T hX hord hmax k g =
      pointBlowupExceptionalEvaluation (localPointBlowupPolynomialMap _ ψ
        (localTaylorCoordinate_mem_maximalIdeal ψ T hX hord) k) k g := rfl

theorem localPointBlowup_exceptionalIdeal_isPrime
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
    (Ideal.span {τ (MvPolynomial.X k)}).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact (localPointBlowupExceptionalQuotientEquiv ψ T hX hord hmax k).symm.toMulEquiv.isDomain _

end MixedFujita
