/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricJacobianBound
public import MixedFujita.TaylorLinearCombination
public import Hironaka.Algebra.Local.PowerSeriesEndomorphism
public import Hironaka.Algebra.Local.FormalAut
public import Hironaka.Algebra.Local.PowerSeries

/-! Leading forms are unchanged by coordinate automorphisms tangent to the
identity. The higher-order defect is controlled by the existing formal
substitution theorem, with no continuity or characteristic-zero premise. -/

@[expose] public section
namespace MixedFujita
open MvPowerSeries IsLocalRing
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

theorem powerSeriesAlgHom_mem_maximalIdeal_pow
    (σ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    {m : ℕ} {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ m) :
    σ f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ m :=
  mem_maximalIdeal_pow_map_of_forall_X_mem σ
    (fun i => mem_maximalIdeal_mvPowerSeries_iff.mpr (constantCoeff_algHom_X σ i)) hf

theorem homogeneousTaylorForm_eq_of_sub_mem_pow_succ (m : ℕ)
    (f g : MvPowerSeries (Fin n) K)
    (h : f - g ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (m + 1)) :
    homogeneousTaylorForm m f = homogeneousTaylorForm m g := by
  rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order] at h
  ext p
  simp only [homogeneousTaylorForm_coeff]
  split_ifs with hp
  · have hp' : (p.degree : ℕ∞) < (m + 1 : ℕ) := by rw [hp]; exact_mod_cast Nat.lt_succ_self m
    have hc : coeff p (f - g) = 0 := coeff_of_lt_order (lt_of_lt_of_le hp' h)
    rw [map_sub] at hc
    exact sub_eq_zero.mp hc
  · rfl

theorem powerSeriesAlgHom_unipotent_defect
    (σ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hσ : ∀ i, σ (X i) - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2)
    (m : ℕ) {f : MvPowerSeries (Fin n) K}
    (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ m) :
    σ f - f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ (m + 1) := by
  have hX i := mem_maximalIdeal_mvPowerSeries_iff.mpr (constantCoeff_algHom_X σ i)
  rw [eq_substAlgHom_of_forall_X_mem σ hX]
  exact substAlgHom_sub_mem_pow_succ (hasSubst_of_forall_X_mem σ hX) hσ m hf

theorem homogeneousTaylorForm_unipotent_algHom
    (σ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hσ : ∀ i, σ (X i) - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2)
    (m : ℕ) (f : MvPowerSeries (Fin n) K) (hf : (m : ℕ∞) ≤ f.order) :
    homogeneousTaylorForm m (σ f) = homogeneousTaylorForm m f := by
  apply homogeneousTaylorForm_eq_of_sub_mem_pow_succ
  apply powerSeriesAlgHom_unipotent_defect σ hσ m
  rwa [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order]

noncomputable def powerSeriesLinearEquiv (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) :
    MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K :=
  AlgEquiv.ofBijective (substAlgHom (R := K) (hasSubst_linearSubst A))
    (bijective_substAlgHom_linearSubst A hA)

theorem powerSeriesLinearEquiv_apply (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A)
    (f : MvPowerSeries (Fin n) K) :
    powerSeriesLinearEquiv A hA f = substAlgHom (R := K) (hasSubst_linearSubst A) f := rfl

theorem powerSeriesLinearEquiv_X (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A) (i : Fin n) :
    powerSeriesLinearEquiv A hA (X i) = linearSubst A i :=
  substAlgHom_X (hasSubst_linearSubst A) i

theorem homogeneousTaylorForm_algEquiv_linearization
    (θ : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K)
    (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A)
    (hθ : ∀ i, θ (X i) - linearSubst A i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2)
    (m : ℕ) (f : MvPowerSeries (Fin n) K) (hf : (m : ℕ∞) ≤ f.order) :
    homogeneousTaylorForm m (θ f) = homogeneousTaylorForm m (powerSeriesLinearEquiv A hA f) := by
  let L := powerSeriesLinearEquiv A hA
  let σ := L.symm.toAlgHom.comp θ.toAlgHom
  have hσ : ∀ i, σ (X i) - X i ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ 2 := by
    intro i
    have h := powerSeriesAlgHom_mem_maximalIdeal_pow L.symm.toAlgHom (hθ i)
    rw [map_sub, ← powerSeriesLinearEquiv_X A hA i] at h
    simpa only [σ, L, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h
  apply homogeneousTaylorForm_eq_of_sub_mem_pow_succ
  have h := powerSeriesAlgHom_mem_maximalIdeal_pow L.toAlgHom
    (powerSeriesAlgHom_unipotent_defect σ hσ m (by
      rwa [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order]))
  simpa only [σ, map_sub, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h

noncomputable def powerSeriesTangentMatrix
    (θ : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  linearPart (fun i => θ (X i))

theorem powerSeriesTangentMatrix_isUnit
    (θ : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K) :
    IsUnit (powerSeriesTangentMatrix θ) := by
  have hX i := mem_maximalIdeal_mvPowerSeries_iff.mpr (constantCoeff_algHom_X θ.toAlgHom i)
  apply isUnit_linearPart_of_bijective (hasSubst_of_forall_X_mem θ.toAlgHom hX)
  have he : substAlgHom (R := K) (hasSubst_of_forall_X_mem θ.toAlgHom hX) = θ.toAlgHom := by
    apply AlgHom.ext
    intro f
    exact (eq_substAlgHom_of_forall_X_mem θ.toAlgHom hX f).symm
  rw [he]
  exact θ.bijective

theorem homogeneousTaylorForm_algEquiv_tangent
    (θ : MvPowerSeries (Fin n) K ≃ₐ[K] MvPowerSeries (Fin n) K)
    (m : ℕ) (f : MvPowerSeries (Fin n) K) (hf : (m : ℕ∞) ≤ f.order) :
    homogeneousTaylorForm m (θ f) = homogeneousTaylorForm m
      (powerSeriesLinearEquiv (powerSeriesTangentMatrix θ) (powerSeriesTangentMatrix_isUnit θ) f) := by
  apply homogeneousTaylorForm_algEquiv_linearization θ _ _ _ m f hf
  intro i
  exact sub_linearSubst_linearPart_mem_sq
    (hasSubst_of_constantCoeff_zero (constantCoeff_algHom_X θ.toAlgHom)) i

end MixedFujita

