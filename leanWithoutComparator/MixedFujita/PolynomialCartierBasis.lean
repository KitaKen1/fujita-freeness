/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialCartierDecomposition
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
The Cartier subspace of a polynomial ring in a basis (step 10, the explicit Cartier isomorphism).

The monomials `x^β` and the exterior basis vectors `e_s = e_{s_1} ∧ … ∧ e_{s_k}` (`s` a finite set
of coordinates in increasing order) form a basis `b_{β,s} = x^β ⊗ e_s` of `K[x_1, …, x_n] ⊗ ⋀(Kⁿ)`.
The weight operators of check-396 are diagonal in this basis: `θ_j b_{β,s} = (β_j + [j ∈ s]) b_{β,s}`
(`polynomialDeRhamWeight_basis`; on the exterior side `e_j ∧ ι_j -` multiplies a product of
coordinate vectors by `[j ∈ s]`, `coordWedgeContract_listProd`). Hence, over a ring of prime
characteristic `p`, a form lies in the Cartier subspace (all weights vanish) exactly when its
coordinates vanish outside the basis vectors whose weights `β_j + [j ∈ s]` are all divisible by `p`
(`mem_polynomialCartierSubspace_iff`), i.e. outside the vectors
`x^{p γ + (p - 1) 1_s} ⊗ e_s`. With the Cartier decomposition this is the explicit form of the
Cartier isomorphism: the de Rham cohomology of the polynomial ring has the basis of the classes of
`x^{p γ} x_s^{p - 1} e_s`, the images of the basis `x^γ e_s` of the Frobenius twist under the
inverse Cartier operator.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section ExteriorWeight

variable {K : Type u} [CommRing K] {n : ℕ}

theorem coordVector_mul_comm_neg (i j : Fin n) (y : CoordExterior K n) :
    coordVector K j * (coordVector K i * y) = -(coordVector K i * (coordVector K j * y)) := by
  rw [← mul_assoc, ← mul_assoc, ← neg_mul, eq_neg_iff_add_eq_zero.mpr
    (ExteriorAlgebra.ι_add_mul_swap _ _)]

/-- A product of coordinate vectors containing `e_j` is killed by `e_j ∧ -`. -/
theorem coordVector_mul_listProd_of_mem (j : Fin n) (l : List (Fin n)) (h : j ∈ l) :
    coordVector K j * (l.map (coordVector K)).prod = 0 := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp h with hji | hjl
    · subst hji
      rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    · rw [coordVector_mul_comm_neg, ih hjl, mul_zero, neg_zero]

/-- The exterior weight `e_j ∧ ι_j -` multiplies a product of coordinate vectors by `[j ∈ l]`. -/
theorem coordWedgeContract_listProd (j : Fin n) (l : List (Fin n)) :
    (coordWedge K j ∘ₗ coordContract (K := K) j) (l.map (coordVector K)).prod =
      (if j ∈ l then (1 : K) else 0) • (l.map (coordVector K)).prod := by
  classical
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, LinearMap.comp_apply, List.not_mem_nil, ite_false,
      zero_smul]
    rw [show coordContract (K := K) j 1 = 0 from CliffordAlgebra.contractLeft_one _ _, map_zero]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, LinearMap.comp_apply, coordWedge_apply,
      coordContract_coordVector_mul, mul_sub, mul_smul_comm] at ih ⊢
    rw [coordVector_mul_comm_neg, ih, mul_smul_comm, sub_neg_eq_add]
    by_cases hij : i = j
    · subst hij
      by_cases hl : i ∈ l
      · rw [coordVector_mul_listProd_of_mem i l hl]
        simp [hl]
      · simp [hl]
    · have hji : (Pi.single i (1 : K) : Fin n → K) j = 0 := Pi.single_eq_of_ne' hij 1
      have hmem : (j ∈ i :: l) ↔ j ∈ l := by
        simp only [List.mem_cons]
        exact ⟨fun h => h.resolve_left (fun e => hij e.symm), Or.inr⟩
      simp only [hji, zero_smul, zero_add, hmem]

/-- The exterior basis of `⋀(Kⁿ)` indexed by finite sets of coordinates. -/
noncomputable abbrev coordExteriorBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis (Finset (Fin n)) K (CoordExterior K n) :=
  (Pi.basisFun K (Fin n)).ExteriorAlgebra

theorem coordExteriorBasis_eq_listProd (s : Finset (Fin n)) :
    coordExteriorBasis K n s =
      ((List.ofFn (s.orderEmbOfFin rfl)).map (coordVector K)).prod := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti K s.card ((Pi.basisFun K (Fin n)) ∘ (s.orderEmbOfFin rfl)) = _
  rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, Pi.basisFun_apply, coordVector]

theorem coordWedgeContract_basis (j : Fin n) (s : Finset (Fin n)) :
    (coordWedge K j ∘ₗ coordContract (K := K) j) (coordExteriorBasis K n s) =
      (if j ∈ s then (1 : K) else 0) • coordExteriorBasis K n s := by
  have hmem : j ∈ List.ofFn (s.orderEmbOfFin rfl) ↔ j ∈ s := by
    rw [List.mem_ofFn', Finset.range_orderEmbOfFin]
    rfl
  rw [coordExteriorBasis_eq_listProd, coordWedgeContract_listProd]
  simp only [hmem]

end ExteriorWeight

section Basis

variable {K : Type u} [CommRing K] {n : ℕ}

/-- The basis `x^β ⊗ e_s` of the coordinate de Rham complex of the polynomial ring. -/
noncomputable abbrev polynomialDeRhamBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Finset (Fin n)) K (MvPolynomial (Fin n) K ⊗[K] CoordExterior K n) :=
  (MvPolynomial.basisMonomials (Fin n) K).tensorProduct (coordExteriorBasis K n)

/-- The `j`-th weight of a basis vector: `β_j + [j ∈ s]`. -/
def polynomialDeRhamWeightOf (i : (Fin n →₀ ℕ) × Finset (Fin n)) (j : Fin n) : ℕ :=
  i.1 j + if j ∈ i.2 then 1 else 0

/-- **The weight operators are diagonal in the basis `x^β ⊗ e_s`.** -/
theorem polynomialDeRhamWeight_basis (j : Fin n) (i : (Fin n →₀ ℕ) × Finset (Fin n)) :
    polynomialDeRhamWeight (K := K) n j (polynomialDeRhamBasis K n i) =
      ((polynomialDeRhamWeightOf i j : ℕ) : K) • polynomialDeRhamBasis K n i := by
  classical
  obtain ⟨β, s⟩ := i
  rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials]
  simp only [polynomialDeRhamWeight, koszulDeRhamWeight_eq_add, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, mvEuler_monomial, coordWedgeContract_basis,
    polynomialDeRhamWeightOf]
  simp only [← TensorProduct.smul_tmul', Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [TensorProduct.tmul_smul, add_smul]

/-- The coordinates of the image under a weight operator are the coordinates times the weights. -/
theorem polynomialDeRhamBasis_repr_weight (j : Fin n) (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (i : (Fin n →₀ ℕ) × Finset (Fin n)) :
    (polynomialDeRhamBasis K n).repr (polynomialDeRhamWeight n j z) i =
      ((polynomialDeRhamWeightOf i j : ℕ) : K) * (polynomialDeRhamBasis K n).repr z i := by
  classical
  have h : (polynomialDeRhamBasis K n).coord i ∘ₗ polynomialDeRhamWeight n j =
      ((polynomialDeRhamWeightOf i j : ℕ) : K) • (polynomialDeRhamBasis K n).coord i := by
    apply (polynomialDeRhamBasis K n).ext
    intro k
    simp only [LinearMap.comp_apply, polynomialDeRhamWeight_basis, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
    by_cases hik : k = i
    · subst hik; rfl
    · rw [Finsupp.single_eq_of_ne' hik, mul_zero, mul_zero]
  have h2 := LinearMap.congr_fun h z
  simpa only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply, smul_eq_mul]
    using h2

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

include hp in
theorem natCast_isUnit_of_not_dvd (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : K) := by
  have hz : (m : ZMod p) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  have hu : IsUnit (m : ZMod p) := hz.isUnit
  simpa only [map_natCast] using hu.map (ZMod.castHom (dvd_refl p) K)

include hp in
/-- **The Cartier subspace in the monomial basis.** Over a ring of prime characteristic `p`, all
weight operators vanish on a form exactly when its coordinates vanish outside the basis vectors
`x^β ⊗ e_s` with all weights `β_j + [j ∈ s]` divisible by `p`. -/
theorem mem_polynomialCartierSubspace_iff (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n) :
    (∀ j, polynomialDeRhamWeight n j z = 0) ↔
      ∀ i, (polynomialDeRhamBasis K n).repr z i ≠ 0 → ∀ j, p ∣ polynomialDeRhamWeightOf i j := by
  constructor
  · intro hz i hi j
    by_contra hdvd
    apply hi
    have h := polynomialDeRhamBasis_repr_weight j z i
    rw [hz j, map_zero, Finsupp.zero_apply] at h
    exact ((natCast_isUnit_of_not_dvd p _ hdvd).mul_right_eq_zero).mp h.symm
  · intro h j
    apply (polynomialDeRhamBasis K n).repr.injective
    ext i
    rw [polynomialDeRhamBasis_repr_weight, map_zero, Finsupp.zero_apply]
    by_cases hi : (polynomialDeRhamBasis K n).repr z i = 0
    · rw [hi, mul_zero]
    · rw [(CharP.cast_eq_zero_iff K p _).mpr (h i hi j), zero_mul]

/-- The weights of a basis vector are all divisible by `p` exactly when it is
`x^{p γ + (p - 1) 1_s} ⊗ e_s`. -/
theorem polynomialDeRhamWeightOf_dvd_iff (i : (Fin n →₀ ℕ) × Finset (Fin n)) :
    (∀ j, p ∣ polynomialDeRhamWeightOf i j) ↔
      ∃ γ : Fin n →₀ ℕ, ∀ j, i.1 j = p * γ j + if j ∈ i.2 then p - 1 else 0 := by
  classical
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  constructor
  · intro h
    refine ⟨Finsupp.onFinset Finset.univ (fun j => (i.1 j + if j ∈ i.2 then 1 else 0) / p - if j ∈ i.2 then 1 else 0)
      (fun _ _ => Finset.mem_univ _), fun j => ?_⟩
    obtain ⟨c, hc⟩ := h j
    simp only [polynomialDeRhamWeightOf] at hc
    rw [Finsupp.onFinset_apply, hc, Nat.mul_div_cancel_left _ hp.out.pos]
    split_ifs with hj
    · simp only [hj, ite_true] at hc
      have hc1 : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, mul_zero] at hc; omega
        · exact h0
      have hpc : p ≤ p * c := Nat.le_mul_of_pos_right p hc1
      have : p * (c - 1) + (p - 1) = p * c - 1 := by
        rw [Nat.mul_sub, mul_one]; omega
      omega
    · simp only [hj, ite_false, add_zero] at hc
      rw [Nat.sub_zero, add_zero]
      exact hc
  · rintro ⟨γ, hγ⟩ j
    simp only [polynomialDeRhamWeightOf, hγ j]
    split_ifs
    · exact ⟨γ j + 1, by rw [mul_add, mul_one]; omega⟩
    · exact ⟨γ j, by rw [add_zero, add_zero]⟩

end Basis

end MixedFujita
