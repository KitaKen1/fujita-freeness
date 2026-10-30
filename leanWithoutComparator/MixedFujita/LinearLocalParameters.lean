/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FirstOrderLeadingForms
public import MixedFujita.LocalLeadingJet

/-! Invertible linear changes of actual local parameters preserve the ideal
they generate. Polynomial linear substitutions agree with the corresponding
formal substitutions; only finite linear combinations in the local ring are
needed to align its parameters with supplied completion coordinates. -/

@[expose] public section
namespace MixedFujita
open MvPowerSeries IsLocalRing
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

noncomputable def linearCoordinateFamily {V : Type*} [AddCommGroup V] [Module K V]
    (A : Matrix (Fin n) (Fin n) K) (v : Fin n → V) : Fin n → V :=
  fun i => ∑ j, A i j • v j

theorem linearCoordinateFamily_comp {V : Type*} [AddCommGroup V] [Module K V]
    (A B : Matrix (Fin n) (Fin n) K) (v : Fin n → V) :
    linearCoordinateFamily A (linearCoordinateFamily B v) = linearCoordinateFamily (A * B) v := by
  funext i
  simp only [linearCoordinateFamily, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem linearCoordinateFamily_one {V : Type*} [AddCommGroup V] [Module K V] (v : Fin n → V) :
    linearCoordinateFamily (1 : Matrix (Fin n) (Fin n) K) v = v := by
  funext i
  simp [linearCoordinateFamily, Matrix.one_apply, ite_smul]

theorem linearCoordinateFamily_span_le {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin n) (Fin n) K) (v : Fin n → R) :
    Ideal.span (Set.range (linearCoordinateFamily A v)) ≤ Ideal.span (Set.range v) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem linearCoordinateFamily_inv_span {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) (v : Fin n → R) :
    Ideal.span (Set.range (linearCoordinateFamily A⁻¹ v)) = Ideal.span (Set.range v) := by
  apply le_antisymm (linearCoordinateFamily_span_le A⁻¹ v)
  have h := linearCoordinateFamily_span_le A (linearCoordinateFamily A⁻¹ v)
  rwa [linearCoordinateFamily_comp,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), linearCoordinateFamily_one] at h

noncomputable def polynomialLinearSubstitution (A : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (linearCoordinateFamily A MvPolynomial.X)

theorem polynomialLinearSubstitution_X (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    polynomialLinearSubstitution A (MvPolynomial.X i) = ∑ j, A i j • MvPolynomial.X j :=
  MvPolynomial.aeval_X _ i

theorem polynomialLinearSubstitution_coe (A : Matrix (Fin n) (Fin n) K)
    (g : MvPolynomial (Fin n) K) :
    (polynomialLinearSubstitution A g : MvPowerSeries (Fin n) K) =
      substAlgHom (R := K) (hasSubst_linearSubst A) (g : MvPowerSeries (Fin n) K) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have hc : polynomialLinearSubstitution A (MvPolynomial.C c) = MvPolynomial.C c :=
      (polynomialLinearSubstitution A).commutes c
    rw [hc, MvPolynomial.coe_C]
    exact (substAlgHom (R := K) (hasSubst_linearSubst A)).commutes c |>.symm
  | add g h hg hh => simp only [map_add, MvPolynomial.coe_add, hg, hh]
  | mul_X g i hg =>
    rw [map_mul, MvPolynomial.coe_mul, MvPolynomial.coe_mul, hg, MvPolynomial.coe_X, map_mul,
      substAlgHom_X, polynomialLinearSubstitution_X]
    congr 1
    change MvPolynomial.coeToMvPowerSeries.ringHom (∑ j, A i j • MvPolynomial.X j) = _
    rw [map_sum]
    simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_smul,
      MvPolynomial.coe_X, linearSubst]

theorem polynomialLinearSubstitution_parameters_span {R : Type*} [CommRing R] [Algebra K R]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    Ideal.span (Set.range fun i => (ψ.comp (polynomialLinearSubstitution A⁻¹)) (MvPolynomial.X i)) =
      Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)) := by
  have h (i : Fin n) : (ψ.comp (polynomialLinearSubstitution A⁻¹)) (MvPolynomial.X i) =
      linearCoordinateFamily A⁻¹ (fun j => ψ (MvPolynomial.X j)) i := by
    simp only [AlgHom.comp_apply, polynomialLinearSubstitution_X, map_sum, map_smul,
      linearCoordinateFamily]
  simp only [h]
  exact linearCoordinateFamily_inv_span A hA _

set_option maxHeartbeats 600000 in
theorem linear_aligned_local_parameters {R : Type*} [CommRing R] [Algebra K R] [IsLocalRing R]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = X i)
    (hmax : maximalIdeal R = Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)))
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    ∃ ψ' : MvPolynomial (Fin n) K →ₐ[K] R,
      maximalIdeal R = Ideal.span (Set.range fun i => ψ' (MvPolynomial.X i)) ∧
      ∀ i, powerSeriesLinearEquiv A hA (T (ψ' (MvPolynomial.X i))) = X i := by
  refine ⟨ψ.comp (polynomialLinearSubstitution A⁻¹), ?_, ?_⟩
  · rw [polynomialLinearSubstitution_parameters_span ψ A hA]
    exact hmax
  · intro i
    change powerSeriesLinearEquiv A hA (T (ψ (polynomialLinearSubstitution A⁻¹ (MvPolynomial.X i)))) = _
    rw [powerSeriesLinearEquiv_apply, taylorCoordinates_polynomial ψ T hX,
      polynomialLinearSubstitution_coe, substAlgHom_linearSubst_apply_inv A hA, MvPolynomial.coe_X]

end MixedFujita
