/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatCokernelCriterion
public import MixedFujita.PolynomialUniversalRegularity
public import MixedFujita.RegularPrincipalIdeal
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.Equalizer

/-!
A finite-variable polynomial with a unit coefficient cuts out a hypersurface
flat over its coefficient ring. Tensor multiplication is transported through
the actual polynomial base-change equivalence. McCoy supplies injectivity
over each quotient R/I; the flat-cokernel criterion closes the proof.
-/

@[expose] public section

namespace MixedFujita

open scoped TensorProduct

variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem polynomial_multiplication_tensor_baseChange (f : MvPolynomial σ R)
    (x : A ⊗[R] MvPolynomial σ R) :
    MvPolynomial.algebraTensorAlgEquiv R A
      (((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R).lTensor A x) =
        MvPolynomial.map (algebraMap R A) f * MvPolynomial.algebraTensorAlgEquiv R A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, LinearMap.mul_apply',
      MvPolynomial.algebraTensorAlgEquiv_tmul, map_mul, mul_smul_comm]
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem polynomial_tensor_multiplication_injective_of_regular_map
    (f : MvPolynomial σ R)
    (hf : MvPolynomial.map (algebraMap R A) f ∈ nonZeroDivisors (MvPolynomial σ A)) :
    Function.Injective
      (((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R).lTensor A) := by
  intro x y hxy
  apply (MvPolynomial.algebraTensorAlgEquiv R A).injective
  apply regular_multiplication_injective _ hf
  change MvPolynomial.map (algebraMap R A) f * _ = MvPolynomial.map (algebraMap R A) f * _
  rw [← polynomial_multiplication_tensor_baseChange f x,
    ← polynomial_multiplication_tensor_baseChange f y, hxy]

theorem polynomial_unit_coefficient_tensor_multiplication_injective [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    Function.Injective
      (((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R).lTensor A) :=
  polynomial_tensor_multiplication_injective_of_regular_map f
    (finitePolynomial_unit_coefficient_baseChange (algebraMap R A) f q hq)

theorem polynomial_principal_quotient_exact_over_coefficients (f : MvPolynomial σ R) :
    Function.Exact
      ((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R)
      (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set (MvPolynomial σ R)))).toLinearMap := by
  intro p
  change Ideal.Quotient.mk _ p = 0 ↔ ∃ g, f * g = p
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

theorem polynomial_unit_coefficient_quotient_flat [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    Module.Flat R (MvPolynomial σ R ⧸ Ideal.span ({f} : Set (MvPolynomial σ R))) := by
  exact flat_cokernel_of_quotient_tensor_injective
    ((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R)
    (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set (MvPolynomial σ R)))).toLinearMap
    (polynomial_principal_quotient_exact_over_coefficients f)
    (Ideal.Quotient.mkₐ_surjective R _)
    (fun I => polynomial_unit_coefficient_tensor_multiplication_injective (A := R ⧸ I) f q hq)

theorem polynomial_localized_coefficient_quotient_flat [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) :
    Module.Flat (Localization.Away (f.coeff q))
      (MvPolynomial σ (Localization.Away (f.coeff q)) ⧸
        Ideal.span ({MvPolynomial.map (algebraMap R (Localization.Away (f.coeff q))) f} :
          Set (MvPolynomial σ (Localization.Away (f.coeff q))))) := by
  apply polynomial_unit_coefficient_quotient_flat _ q
  rw [MvPolynomial.coeff_map]
  exact IsLocalization.Away.algebraMap_isUnit (f.coeff q)

omit [Algebra R A] in
theorem polynomial_unit_coefficient_quotient_baseChange_flat [Finite σ]
    (c : R →+* A) (f : MvPolynomial σ R) (q : σ →₀ ℕ)
    (hq : IsUnit (f.coeff q)) :
    Module.Flat A (MvPolynomial σ A ⧸
      Ideal.span ({MvPolynomial.map c f} : Set (MvPolynomial σ A))) := by
  apply polynomial_unit_coefficient_quotient_flat _ q
  rw [MvPolynomial.coeff_map]
  exact hq.map c

theorem polynomial_unit_coefficient_all_module_tensor_injective [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q))
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective
      (((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R).lTensor M) := by
  let _ := polynomial_unit_coefficient_quotient_flat f q hq
  exact LinearMap.lTensor_injective_of_exact_of_flat
    (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set (MvPolynomial σ R)))).toLinearMap
    (Ideal.Quotient.mkₐ_surjective R _)
    ((LinearMap.mul (MvPolynomial σ R) (MvPolynomial σ R) f).restrictScalars R)
    (regular_multiplication_injective f (finitePolynomial_regular_of_unit_coefficient f q hq))
    (polynomial_principal_quotient_exact_over_coefficients f) M

end MixedFujita
