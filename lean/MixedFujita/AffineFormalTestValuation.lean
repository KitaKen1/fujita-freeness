/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FormalTestFieldDerivation
public import MixedFujita.AffineEtaleChartModel
public import MixedFujita.GeometricJacobianBound

/-!
Formal tests at points of affine space as valuations of its function field. A K-algebra map ψ of
power series rings with nonzero Jacobian determinant is injective in characteristic zero: by the
adjugate identity ψ(G) = 0 forces ψ(∂_i G) = 0, and some iterated derivative of a nonzero G is a
unit. So the shifted test P ↦ ψ(P(p + X)) is injective on polynomials and extends to the function
field of affine space; its constant term is P(p), so polynomials not vanishing at p have
valuation one. The identity étale chart of affine space has the polynomial variables as
coordinates in the function field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPowerSeries

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Injective

variable {σ K : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

/-- If ψ kills G then ψ kills every partial derivative of G. -/
theorem powerSeriesAlgHom_pderiv_eq_zero_of_eq_zero
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (hJ : (powerSeriesJacobian ψ).det ≠ 0)
    {G : MvPowerSeries σ K} (hG : ψ G = 0) (i : σ) : ψ (pderiv i G) = 0 := by
  have h := jacobian_adjugate_identity ψ (powerSeries_chainRule ψ (constantCoeff_algHom_X ψ) G) i
  rw [hG] at h
  simp only [map_zero, zero_mul, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hJ

theorem powerSeriesAlgHom_iteratedPDeriv_eq_zero
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (hJ : (powerSeriesJacobian ψ).det ≠ 0)
    {G : MvPowerSeries σ K} (hG : ψ G = 0) : ∀ L : List σ, ψ (iteratedPDeriv L G) = 0
  | [] => hG
  | i :: L => powerSeriesAlgHom_pderiv_eq_zero_of_eq_zero ψ hJ
      (powerSeriesAlgHom_iteratedPDeriv_eq_zero ψ hJ hG L) i

/-- A formal test with nonzero Jacobian determinant is injective. -/
theorem powerSeriesAlgHom_injective_of_jacobian
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (hJ : (powerSeriesJacobian ψ).det ≠ 0) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro G hG
  by_contra hne
  obtain ⟨L, -, hu⟩ := exists_iteratedPDeriv_isUnit hne
  exact (hu.map ψ).ne_zero (powerSeriesAlgHom_iteratedPDeriv_eq_zero ψ hJ hG L)

end Injective

section Shift

variable {K : Type*} [Field K] {m : ℕ}

/-- The shift P ↦ P(p + X) of polynomials into power series. -/
noncomputable def shiftPowerSeriesMap (p : Fin m → K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K :=
  MvPolynomial.aeval fun j => algebraMap K (MvPowerSeries (Fin m) K) (p j) + MvPowerSeries.X j

/-- The shifted test factors through the shift. -/
theorem shiftedFormalTestMap_eq_comp
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (p : Fin m → K) :
    shiftedFormalTestMap ψ p = ψ.comp (shiftPowerSeriesMap p) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [shiftedFormalTestMap_X, AlgHom.comp_apply, shiftPowerSeriesMap, MvPolynomial.aeval_X,
    map_add, AlgHom.commutes]

/-- The polynomial shift P ↦ P(X + p). -/
noncomputable def shiftPolynomialMap (p : Fin m → K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval fun j => (MvPolynomial.X j + MvPolynomial.C (p j) : MvPolynomial (Fin m) K)

theorem shiftPolynomial_injective (p : Fin m → K) :
    Function.Injective (shiftPolynomialMap (K := K) p) := by
  have h : (MvPolynomial.aeval (R := K)
      fun j : Fin m => (MvPolynomial.X j - MvPolynomial.C (p j) : MvPolynomial (Fin m) K)).comp
      (shiftPolynomialMap p) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [shiftPolynomialMap, AlgHom.comp_apply, MvPolynomial.aeval_X, map_add,
      MvPolynomial.algHom_C, AlgHom.id_apply, MvPolynomial.algebraMap_eq, sub_add_cancel]
  intro P Q hPQ
  have := congrArg (MvPolynomial.aeval (R := K)
    fun j : Fin m => (MvPolynomial.X j - MvPolynomial.C (p j) : MvPolynomial (Fin m) K)) hPQ
  simpa only [← AlgHom.comp_apply, h, AlgHom.id_apply] using this

/-- The shift is the inclusion of the shifted polynomial. -/
theorem shiftPowerSeriesMap_eq_coe (p : Fin m → K) (P : MvPolynomial (Fin m) K) :
    shiftPowerSeriesMap p P = ((shiftPolynomialMap p P : MvPolynomial (Fin m) K) :
      MvPowerSeries (Fin m) K) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, MvPolynomial.coe_add]
  | mul_X P j hP =>
    rw [map_mul, map_mul, hP, MvPolynomial.coe_mul, shiftPowerSeriesMap, MvPolynomial.aeval_X,
      shiftPolynomialMap, MvPolynomial.aeval_X, MvPolynomial.coe_add, MvPolynomial.coe_X, MvPolynomial.coe_C,
      MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, add_comm]

theorem shiftPowerSeriesMap_injective (p : Fin m → K) :
    Function.Injective (shiftPowerSeriesMap (K := K) p) := by
  intro P Q hPQ
  rw [shiftPowerSeriesMap_eq_coe, shiftPowerSeriesMap_eq_coe] at hPQ
  exact shiftPolynomial_injective p (MvPolynomial.coe_inj.mp hPQ)

/-- The shifted test of a formal test with nonzero Jacobian determinant is injective. -/
theorem shiftedFormalTestMap_injective [CharZero K]
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (p : Fin m → K) :
    Function.Injective (shiftedFormalTestMap ψ p) := by
  rw [shiftedFormalTestMap_eq_comp]
  exact (powerSeriesAlgHom_injective_of_jacobian ψ hJ).comp (shiftPowerSeriesMap_injective p)

/-- The constant coefficient of the shifted test of P is P(p). -/
theorem constantCoeff_shiftedFormalTestMap
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (p : Fin m → K)
    (P : MvPolynomial (Fin m) K) :
    constantCoeff (shiftedFormalTestMap ψ p P) = MvPolynomial.eval p P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.algHom_C, MvPolynomial.eval_C, MvPowerSeries.algebraMap_apply,
      constantCoeff_C, Algebra.algebraMap_self, RingHom.id_apply]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add]
  | mul_X P j hP =>
    rw [map_mul, map_mul, hP, shiftedFormalTestMap_X, map_add, constantCoeff_algHom_X, add_zero,
      MvPowerSeries.algebraMap_apply, constantCoeff_C, Algebra.algebraMap_self, RingHom.id_apply,
      map_mul (MvPolynomial.eval p), MvPolynomial.eval_X]

/-- A polynomial not vanishing at p has shifted test of weighted valuation one. -/
theorem weightedValuation_shiftedFormalTestMap_eq_one
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K) (p : Fin m → K)
    (w : Fin m → ℕ) {Q : MvPolynomial (Fin m) K} (hQ : MvPolynomial.eval p Q ≠ 0) :
    weightedValuation w (shiftedFormalTestMap ψ p Q) = 1 := by
  have hu : IsUnit (shiftedFormalTestMap ψ p Q) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_shiftedFormalTestMap]
    exact hQ.isUnit
  have hne : shiftedFormalTestMap ψ p Q ≠ 0 := hu.ne_zero
  rw [weightedValuation_of_ne_zero w hne, weightedOrder_eq_zero_of_isUnit w hu]
  rfl

/-- Every power series has weighted valuation at most one. -/
theorem weightedValuation_le_one {σ : Type*} (w : σ → ℕ) (F : MvPowerSeries σ K) :
    weightedValuation w F ≤ 1 := by
  rw [← map_one (weightedValuation (K := K) w), weightedValuation_le_iff, weightedOrder_one]
  exact zero_le

end Shift

section AffineSpace

variable (K : Type u) [Field K] (m : ℕ)

attribute [local instance] specAlgebraOver

theorem mvPolynomial_id_formallyEtale :
    (AlgHom.id K (MvPolynomial (Fin m) K)).toRingHom.FormallyEtale :=
  RingHom.formallyEtale_algebraMap.mpr inferInstance

/-- The identity étale chart of affine space: the polynomial variables on the whole spectrum. -/
noncomputable def affineSpaceEtaleChart :
    EtaleChart K (Spec (CommRingCat.of (MvPolynomial (Fin m) K))) m where
  U := ⊤
  isAffine := isAffineOpen_top _
  nonempty := ⟨⟨genericPoint _, trivial⟩⟩
  coords := specAlgebraCoords (AlgHom.id K (MvPolynomial (Fin m) K))
  formallyEtale := specAlgebraCoords_formallyEtale _ (mvPolynomial_id_formallyEtale K m)

/-- A global function of the spectrum of a domain has the canonical image in the function field. -/
theorem spec_germToFunctionField_ΓSpecIso_inv (A : CommRingCat.{u}) [IsDomain A] (P : A) :
    ((Spec A).germToFunctionField ⊤).hom ((Scheme.ΓSpecIso A).inv.hom P) =
      algebraMap A (Spec A).functionField P := by
  rw [Scheme.ΓSpecIso_inv]
  change ((Spec A).presheaf.germ ⊤ (genericPoint _) _).hom (algebraMap A _ P) =
    (StructureSheaf.toStalk A (genericPoint (Spec A))).hom P
  rw [← StructureSheaf.algebraMap_germ_apply ⊤ (genericPoint (Spec A)) trivial P]
  rfl

/-- The chart coordinates of a polynomial are its image in the function field. -/
theorem affineSpaceEtaleChart_functionFieldCoords (P : MvPolynomial (Fin m) K) :
    etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P =
      @algebraMap (CommRingCat.of (MvPolynomial (Fin m) K))
        (Spec (CommRingCat.of (MvPolynomial (Fin m) K))).functionField _ _
        (instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (MvPolynomial (Fin m) K))) P :=
  spec_germToFunctionField_ΓSpecIso_inv (CommRingCat.of (MvPolynomial (Fin m) K)) P

theorem affineSpaceEtaleChart_functionFieldCoords_injective :
    Function.Injective (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m)) := by
  let := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (MvPolynomial (Fin m) K))
  have := functionField_isFractionRing_of_affine (CommRingCat.of (MvPolynomial (Fin m) K))
  intro P Q h
  rw [affineSpaceEtaleChart_functionFieldCoords, affineSpaceEtaleChart_functionFieldCoords] at h
  exact IsFractionRing.injective (CommRingCat.of (MvPolynomial (Fin m) K)) _ h

/-- Every rational function on affine space is a quotient of polynomials in the coordinates. -/
theorem affineSpaceEtaleChart_exists_fraction
    (f : (Spec (CommRingCat.of (MvPolynomial (Fin m) K))).functionField) :
    ∃ P Q : MvPolynomial (Fin m) K,
      etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) Q ≠ 0 ∧
        f * etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) Q =
          etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P := by
  let := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (MvPolynomial (Fin m) K))
  have := functionField_isFractionRing_of_affine (CommRingCat.of (MvPolynomial (Fin m) K))
  obtain ⟨⟨P, Q⟩, h⟩ := IsLocalization.surj
    (nonZeroDivisors (CommRingCat.of (MvPolynomial (Fin m) K))) f
  refine ⟨P, Q, ?_, ?_⟩
  · rw [affineSpaceEtaleChart_functionFieldCoords]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Q.2
  · rw [affineSpaceEtaleChart_functionFieldCoords, affineSpaceEtaleChart_functionFieldCoords]
    exact h

/-- The closed point of affine space at p. -/
noncomputable def affineSpacePoint (p : Fin m → K) : Spec (CommRingCat.of (MvPolynomial (Fin m) K)) :=
  ⟨RingHom.ker (MvPolynomial.eval p), RingHom.ker_isPrime _⟩

theorem affineSpacePoint_mem_iff (p : Fin m → K) (P : MvPolynomial (Fin m) K) :
    P ∈ (affineSpacePoint K m p).asIdeal ↔ MvPolynomial.eval p P = 0 :=
  RingHom.mem_ker

end AffineSpace

end MixedFujita
