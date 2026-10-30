/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
The de Rham complex in coordinates, and Cartan's homotopy formula (step 10, the algebraic core of
the Deligne–Illusie route to Kodaira vanishing).

Let `A` be a commutative `K`-algebra with `n` pairwise commuting `K`-derivations `∂_1, …, ∂_n`.
On `Ω = A ⊗_K ⋀(Kⁿ)` put `d = Σ_j ∂_j ⊗ (e_j ∧ -)`. Then `d ∘ d = 0`
(`koszulDeRhamDiff_comp_self`): the terms `∂_i ∂_j ⊗ e_i ∧ e_j` cancel in pairs, because the
derivations commute and `e_i ∧ e_j = - e_j ∧ e_i`. For an algebra étale over a polynomial ring with
the extended partial derivatives, this is the de Rham complex in the étale coordinates.

If moreover `x_1, …, x_n ∈ A` satisfy `∂_i x_j = δ_{ij}` (étale coordinates), the operators
`h_j = x_j ⊗ ι_j`, with `ι_j` the contraction with the `j`-th dual basis vector, satisfy Cartan's
formula `d h_j + h_j d = θ_j` with `θ_j = x_j ∂_j ⊗ 1 + 1 ⊗ (e_j ∧ ι_j -)`
(`koszulDeRham_cartan`). On the polynomial ring `θ_j` multiplies `x^β e_I` by its `j`-th weight
`β_j + [j ∈ I]`; hence a cocycle on which some `θ_j` acts by a unit is a coboundary
(`mem_range_koszulDeRhamDiff_of_cartan_unit`). In characteristic `p` this is the exactness of the
weights not divisible by `p`, the heart of the Cartier isomorphism.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Complex

variable (K : Type u) [CommRing K] (A : Type v) [CommRing A] [Algebra K A] (n : ℕ)

/-- The exterior algebra on the coordinate vectors `e_1, …, e_n`. -/
abbrev CoordExterior := ExteriorAlgebra K (Fin n → K)

variable {n}

/-- The `j`-th coordinate vector in the exterior algebra. -/
noncomputable abbrev coordVector (j : Fin n) : CoordExterior K n :=
  ExteriorAlgebra.ι K (Pi.single j (1 : K))

/-- Left multiplication by the `j`-th coordinate vector. -/
noncomputable def coordWedge (j : Fin n) : CoordExterior K n →ₗ[K] CoordExterior K n :=
  LinearMap.mulLeft K (coordVector K j)

theorem coordWedge_apply (j : Fin n) (e : CoordExterior K n) :
    coordWedge K j e = coordVector K j * e := rfl

theorem coordWedge_comp_self (j : Fin n) : coordWedge K j ∘ₗ coordWedge K j = 0 := by
  ext e
  simp only [LinearMap.comp_apply, coordWedge_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
    zero_mul, LinearMap.zero_apply]

theorem coordWedge_comp_add_swap (i j : Fin n) :
    coordWedge K i ∘ₗ coordWedge K j + coordWedge K j ∘ₗ coordWedge K i = 0 := by
  ext e
  simp only [LinearMap.add_apply, LinearMap.comp_apply, coordWedge_apply, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul, LinearMap.zero_apply]

variable {K A}

/-- The de Rham differential of commuting derivations: `d = Σ_j ∂_j ⊗ (e_j ∧ -)`. -/
noncomputable def koszulDeRhamDiff (D : Fin n → A →ₗ[K] A) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  ∑ j, TensorProduct.map (D j) (coordWedge K j)

theorem koszulDeRhamDiff_tmul (D : Fin n → A →ₗ[K] A) (a : A) (e : CoordExterior K n) :
    koszulDeRhamDiff D (a ⊗ₜ e) = ∑ j, D j a ⊗ₜ (coordVector K j * e) := by
  simp [koszulDeRhamDiff, coordWedge_apply]

/-- **`d ∘ d = 0`** for pairwise commuting derivations. -/
theorem koszulDeRhamDiff_comp_self (D : Fin n → A →ₗ[K] A)
    (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i) :
    koszulDeRhamDiff D ∘ₗ koszulDeRhamDiff D = 0 := by
  apply TensorProduct.ext'
  intro a e
  rw [LinearMap.comp_apply, koszulDeRhamDiff_tmul, map_sum, LinearMap.zero_apply]
  simp_rw [koszulDeRhamDiff_tmul]
  rw [← Finset.sum_product']
  refine Finset.sum_ninvolution (fun p => (p.2, p.1)) ?_ ?_ (fun _ => Finset.mem_univ _)
    (fun _ => rfl)
  · rintro ⟨i, j⟩
    have h1 : D i (D j a) = D j (D i a) := LinearMap.congr_fun (hD i j) a
    have h2 : coordVector K j * (coordVector K i * e) + coordVector K i * (coordVector K j * e) = 0 := by
      rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
    simp only
    rw [h1, ← TensorProduct.tmul_add, h2, TensorProduct.tmul_zero]
  · rintro ⟨i, j⟩ hne heq
    apply hne
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp only
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.tmul_zero]

theorem koszulDeRhamDiff_apply_apply (D : Fin n → A →ₗ[K] A)
    (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i) (z : A ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff D (koszulDeRhamDiff D z) = 0 :=
  LinearMap.congr_fun (koszulDeRhamDiff_comp_self D hD) z

end Complex

section Cartan

variable {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] {n : ℕ}

/-- The contraction with the `j`-th dual basis vector. -/
noncomputable def coordContract (j : Fin n) : CoordExterior K n →ₗ[K] CoordExterior K n :=
  CliffordAlgebra.contractLeft (LinearMap.proj j)

theorem coordContract_coordVector_mul (i j : Fin n) (e : CoordExterior K n) :
    coordContract j (coordVector K i * e) =
      (Pi.single i (1 : K) : Fin n → K) j • e - coordVector K i * coordContract j e :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/-- The homotopy `h_j = x_j ⊗ ι_j`. -/
noncomputable def koszulDeRhamHomotopy (x : Fin n → A) (j : Fin n) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  TensorProduct.map (LinearMap.mulLeft K (x j)) (coordContract j)

/-- The weight operator `θ_j = x_j ∂_j ⊗ 1 + 1 ⊗ (e_j ∧ ι_j -)`. -/
noncomputable def koszulDeRhamWeight (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  TensorProduct.map (LinearMap.mulLeft K (x j) ∘ₗ D j) LinearMap.id +
    TensorProduct.map LinearMap.id (coordWedge K j ∘ₗ coordContract j)

/-- **Cartan's homotopy formula** `d h_j + h_j d = θ_j`, for `K`-linear maps `∂_i` satisfying the
Leibniz rule against `x_j` with `∂_i x_j = δ_{ij}`. -/
theorem koszulDeRham_cartan (D : Fin n → A →ₗ[K] A) (x : Fin n → A)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (j : Fin n) :
    koszulDeRhamDiff D ∘ₗ koszulDeRhamHomotopy x j + koszulDeRhamHomotopy x j ∘ₗ koszulDeRhamDiff D =
      koszulDeRhamWeight D x j := by
  classical
  apply TensorProduct.ext'
  intro a e
  simp only [LinearMap.add_apply, LinearMap.comp_apply, koszulDeRhamHomotopy, koszulDeRhamWeight,
    TensorProduct.map_tmul, LinearMap.mulLeft_apply, koszulDeRhamDiff_tmul, map_sum,
    LinearMap.id_apply, coordWedge_apply]
  simp_rw [hleib, coordContract_coordVector_mul]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin n,
      (x j * D i a + (if i = j then a else 0)) ⊗ₜ[K] (coordVector K i * coordContract j e) +
        (x j * D i a) ⊗ₜ[K] ((Pi.single i (1 : K) : Fin n → K) j • e -
          coordVector K i * coordContract j e) =
      if i = j then a ⊗ₜ[K] (coordVector K j * coordContract j e) + (x j * D j a) ⊗ₜ[K] e
      else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, Pi.single_eq_same, one_smul, TensorProduct.add_tmul,
        TensorProduct.tmul_sub]
      abel
    · have hji : (Pi.single i (1 : K) : Fin n → K) j = 0 := Pi.single_eq_of_ne' hij 1
      simp only [hij, ite_false, add_zero, hji, zero_smul, zero_sub, TensorProduct.tmul_neg,
        add_neg_cancel]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, ite_true]
  abel

/-- The weight operators commute with the differential. -/
theorem koszulDeRhamDiff_comp_weight (D : Fin n → A →ₗ[K] A) (x : Fin n → A)
    (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (j : Fin n) :
    koszulDeRhamDiff D ∘ₗ koszulDeRhamWeight D x j = koszulDeRhamWeight D x j ∘ₗ koszulDeRhamDiff D := by
  have hdd := koszulDeRhamDiff_comp_self D hD
  have hdd' : ∀ f : A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n,
      koszulDeRhamDiff D ∘ₗ (koszulDeRhamDiff D ∘ₗ f) = 0 := fun f => by
    rw [← LinearMap.comp_assoc, hdd, LinearMap.zero_comp]
  rw [← koszulDeRham_cartan D x hleib j, LinearMap.comp_add, LinearMap.add_comp]
  simp only [LinearMap.comp_assoc, hdd, hdd', LinearMap.comp_zero, zero_add, add_zero]

/-- The weight operators send cocycles to coboundaries. -/
theorem koszulDeRhamWeight_mem_range (D : Fin n → A →ₗ[K] A) (x : Fin n → A)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (j : Fin n)
    (z : A ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff D z = 0) :
    koszulDeRhamWeight D x j z ∈ LinearMap.range (koszulDeRhamDiff D) := by
  refine ⟨koszulDeRhamHomotopy x j z, ?_⟩
  have h := LinearMap.congr_fun (koszulDeRham_cartan D x hleib j) z
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero] using h

/-- A cocycle on which a weight operator acts through a unit is a coboundary. -/
theorem mem_range_koszulDeRhamDiff_of_cartan_unit (D : Fin n → A →ₗ[K] A) (x : Fin n → A)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (j : Fin n)
    (z : A ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff D z = 0) (c : Kˣ)
    (hθ : koszulDeRhamWeight D x j z = (c : K) • z) :
    z ∈ LinearMap.range (koszulDeRhamDiff D) := by
  refine ⟨((c⁻¹ : Kˣ) : K) • koszulDeRhamHomotopy x j z, ?_⟩
  have h := LinearMap.congr_fun (koszulDeRham_cartan D x hleib j) z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero] at h
  rw [map_smul, h, hθ, smul_smul, Units.inv_mul, one_smul]

end Cartan

end MixedFujita
