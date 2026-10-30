/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CommutingDerivationDeRham
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

/-!
The Cartier decomposition of the de Rham complex of a polynomial ring in characteristic `p`
(step 10, the algebraic core of the Deligne–Illusie route).

On `Ω = K[x_1, …, x_n] ⊗ ⋀(Kⁿ)` with `d = Σ ∂_j ⊗ (e_j ∧ -)` the weight operators
`θ_j = x_j ∂_j ⊗ 1 + 1 ⊗ (e_j ∧ ι_j -)` of check-395 commute with each other and with `d`. If `K`
has characteristic `p`, then `θ_j^p = θ_j` (`koszulDeRhamWeight_pow_char`): the exterior part is
an idempotent, and the Euler operator `x_j ∂_j` multiplies a monomial by its exponent, which is
fixed by the Frobenius of the prime field. Let `C` be the subspace on which every `θ_j` vanishes
(all weights divisible by `p`). Then:
* `d` vanishes on `C` (`polynomialDeRhamDiff_eq_zero_of_weights`): `∂_i (1 - (x_i ∂_i)^{p-1}) = 0`
  because `β^p = β`;
* the composite `P` of the idempotents `1 - θ_j^{p-1}` commutes with `d`, maps onto `C`, is the
  identity on `C`, and `z - P z` is a coboundary for every cocycle `z`, since `θ_j^{p-1} z =
  θ_j (θ_j^{p-2} z)` and `θ_j` sends cocycles to coboundaries by Cartan's formula.
Hence every cocycle is uniquely the sum of an element of `C` and a coboundary
(`polynomialDeRham_cartier_decomposition`): the cohomology of the de Rham complex is `C`, spanned
by the forms `x^β e_I` with `β + 1_I ≡ 0 (mod p)`. This is the Cartier isomorphism for the
polynomial ring; the inverse Cartier operator `x^γ e_I ↦ x^{pγ + (p-1) 1_I} e_I` is its explicit
form.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Exterior

variable {K : Type u} [CommRing K] {n : ℕ}

theorem coordContract_coordContract (j : Fin n) (e : CoordExterior K n) :
    coordContract (K := K) j (coordContract j e) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem coordContract_comp_self (j : Fin n) :
    coordContract (K := K) j ∘ₗ coordContract j = 0 :=
  LinearMap.ext fun e => coordContract_coordContract j e

theorem linearMap_id_pow {M : Type v} [AddCommGroup M] [Module K M] (k : ℕ) :
    (LinearMap.id : M →ₗ[K] M) ^ k = LinearMap.id := by
  rw [← Module.End.one_eq_id, one_pow]

theorem coordContract_comp_coordWedge (i j : Fin n) :
    coordContract (K := K) j ∘ₗ coordWedge K i =
      ((Pi.single i (1 : K) : Fin n → K) j) • LinearMap.id - coordWedge K i ∘ₗ coordContract j :=
  LinearMap.ext fun e => by
    simp only [LinearMap.comp_apply, coordWedge_apply, coordContract_coordVector_mul,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

/-- The exterior weight `e_j ∧ ι_j -` is idempotent. -/
theorem coordWedgeContract_idem (j : Fin n) :
    (coordWedge K j ∘ₗ coordContract j) ∘ₗ (coordWedge K j ∘ₗ coordContract (K := K) j) =
      coordWedge K j ∘ₗ coordContract j := by
  refine LinearMap.ext fun e => ?_
  simp only [LinearMap.comp_apply, coordWedge_apply, coordContract_coordVector_mul,
    Pi.single_eq_same, one_smul, coordContract_coordContract, mul_zero, sub_zero]

theorem coordWedgeContract_pow_succ (j : Fin n) (k : ℕ) :
    (coordWedge K j ∘ₗ coordContract (K := K) j) ^ (k + 1) = coordWedge K j ∘ₗ coordContract j := by
  induction k with
  | zero => rw [zero_add, pow_one]
  | succ k ih => rw [pow_succ, ih, Module.End.mul_eq_comp, coordWedgeContract_idem]

theorem coordWedge_comp_wedgeContract (j : Fin n) :
    coordWedge K j ∘ₗ (coordWedge K j ∘ₗ coordContract (K := K) j) = 0 := by
  rw [← LinearMap.comp_assoc, coordWedge_comp_self, LinearMap.zero_comp]

/-- The exterior weights for distinct coordinates commute. -/
theorem coordWedgeContract_comm (i j : Fin n) :
    (coordWedge K i ∘ₗ coordContract (K := K) i) ∘ₗ (coordWedge K j ∘ₗ coordContract j) =
      (coordWedge K j ∘ₗ coordContract j) ∘ₗ (coordWedge K i ∘ₗ coordContract (K := K) i) := by
  by_cases hij : i = j
  · subst hij; rfl
  refine LinearMap.ext fun e => ?_
  have hji : (Pi.single j (1 : K) : Fin n → K) i = 0 := Pi.single_eq_of_ne' (Ne.symm hij) 1
  have hij' : (Pi.single i (1 : K) : Fin n → K) j = 0 := Pi.single_eq_of_ne' hij 1
  simp only [LinearMap.comp_apply, coordWedge_apply, coordContract_coordVector_mul, hji, hij',
    zero_smul, zero_sub, mul_neg]
  have hcomm : coordContract (K := K) i (coordContract j e) = -coordContract j (coordContract i e) :=
    CliffordAlgebra.contractLeft_comm _ _ _
  have hswap : coordVector K i * coordVector K j = -(coordVector K j * coordVector K i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap _ _
  rw [hcomm]
  simp only [mul_neg, neg_neg, ← mul_assoc, hswap, neg_mul]

end Exterior

section General

variable {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] {n : ℕ}

/-- The Euler part `x_j ∂_j` of a weight operator. -/
noncomputable def eulerOperator (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n) : A →ₗ[K] A :=
  LinearMap.mulLeft K (x j) ∘ₗ D j

theorem eulerOperator_apply (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n) (a : A) :
    eulerOperator D x j a = x j * D j a := rfl

theorem koszulDeRhamWeight_eq_add (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n) :
    koszulDeRhamWeight D x j =
      TensorProduct.map (eulerOperator D x j) LinearMap.id +
        TensorProduct.map LinearMap.id (coordWedge K j ∘ₗ coordContract j) := rfl

theorem commute_eulerPart_wedgePart (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n) :
    Commute (TensorProduct.map (eulerOperator D x j) LinearMap.id)
      (TensorProduct.map (LinearMap.id : A →ₗ[K] A) (coordWedge K j ∘ₗ coordContract j)) := by
  change TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
  rfl

/-- In characteristic `p`, a weight operator whose Euler part satisfies `(x_j ∂_j)^p = x_j ∂_j`
satisfies `θ_j^p = θ_j`. -/
theorem koszulDeRhamWeight_pow_of_euler (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) = 0)
    (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (j : Fin n)
    (hE : eulerOperator D x j ^ p = eulerOperator D x j) :
    koszulDeRhamWeight D x j ^ p = koszulDeRhamWeight D x j := by
  rw [koszulDeRhamWeight_eq_add, (commute_eulerPart_wedgePart D x j).add_pow_prime_eq hp.out,
    TensorProduct.map_pow, TensorProduct.map_pow, hE, linearMap_id_pow, linearMap_id_pow]
  have hY : (coordWedge K j ∘ₗ coordContract (K := K) j) ^ p = coordWedge K j ∘ₗ coordContract j := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    rw [hq, coordWedgeContract_pow_succ]
  have hpE : ((p : ℕ) : Module.End K (A ⊗[K] CoordExterior K n)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (A ⊗[K] CoordExterior K n))), hpK, map_zero]
  rw [hY, hpE, zero_mul, zero_mul, zero_mul, add_zero]

/-- The term `∂_i ⊗ (e_i ∧ -)` of the differential absorbs powers of the `i`-th weight into its
Euler part. -/
theorem partialWedge_comp_weight_pow (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (i : Fin n) (k : ℕ) :
    TensorProduct.map (D i) (coordWedge K i) ∘ₗ koszulDeRhamWeight D x i ^ k =
      TensorProduct.map (D i ∘ₗ eulerOperator D x i ^ k) (coordWedge K i) := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, koszulDeRhamWeight_eq_add,
      LinearMap.comp_add, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
      coordWedge_comp_wedgeContract, TensorProduct.map_zero_right, add_zero, LinearMap.comp_id,
      pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]

end General

section Polynomial

variable {K : Type u} [CommRing K] {n : ℕ}

/-- The partial derivatives of the polynomial ring as linear maps. -/
noncomputable abbrev mvPartial (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K :=
  (MvPolynomial.pderiv j : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))

theorem mvPartial_comm (i j : Fin n) :
    mvPartial (K := K) n i ∘ₗ mvPartial n j = mvPartial n j ∘ₗ mvPartial n i := by
  classical
  have h : ⁅(MvPolynomial.pderiv i : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)),
      (MvPolynomial.pderiv j : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  refine LinearMap.ext fun a => ?_
  have h2 := congrArg
    (fun D : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K) => D a) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  simpa [sub_eq_zero] using h2

theorem mvPartial_X_mul (i j : Fin n) (a : MvPolynomial (Fin n) K) :
    mvPartial n i (MvPolynomial.X j * a) =
      MvPolynomial.X j * mvPartial n i a + (if i = j then a else 0) := by
  classical
  change MvPolynomial.pderiv i (MvPolynomial.X j * a) =
    MvPolynomial.X j * MvPolynomial.pderiv i a + (if i = j then a else 0)
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem mvEuler_monomial (j : Fin n) (s : Fin n →₀ ℕ) (c : K) :
    eulerOperator (fun i => mvPartial n i) (fun i => MvPolynomial.X i) j (MvPolynomial.monomial s c) =
      ((s j : ℕ) : K) • MvPolynomial.monomial s c := by
  rw [eulerOperator_apply]
  change MvPolynomial.X j * MvPolynomial.pderiv j (MvPolynomial.monomial s c) = _
  rw [MvPolynomial.X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

include hp in
theorem natCast_pow_char (m : ℕ) : ((m : K)) ^ p = (m : K) := by
  have h := ZMod.pow_card (p := p) (m : ZMod p)
  have h2 := congrArg (ZMod.castHom (dvd_refl p) K) h
  simpa only [map_pow, map_natCast] using h2

theorem mvEuler_pow_monomial (j : Fin n) (k : ℕ) (s : Fin n →₀ ℕ) (c : K) :
    (eulerOperator (fun i => mvPartial n i) (fun i => MvPolynomial.X i) j ^ k)
        (MvPolynomial.monomial s c) = ((s j : ℕ) : K) ^ k • MvPolynomial.monomial s c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, mvEuler_monomial, map_smul, ih, smul_smul, pow_succ,
      mul_comm]

include hp in
theorem mvEuler_pow_char (j : Fin n) :
    eulerOperator (fun i => mvPartial (K := K) n i) (fun i => MvPolynomial.X i) j ^ p =
      eulerOperator (fun i => mvPartial n i) (fun i => MvPolynomial.X i) j := by
  apply LinearMap.ext
  intro a
  induction a using MvPolynomial.induction_on' with
  | monomial s c => rw [mvEuler_pow_monomial, natCast_pow_char p, mvEuler_monomial]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

include hp in
theorem mvPartial_comp_euler_pow_pred (j : Fin n) :
    mvPartial (K := K) n j ∘ₗ
        eulerOperator (fun i => mvPartial n i) (fun i => MvPolynomial.X i) j ^ (p - 1) =
      mvPartial n j := by
  apply LinearMap.ext
  intro a
  induction a using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [LinearMap.comp_apply, mvEuler_pow_monomial, map_smul]
    simp only [mvPartial, Derivation.coeFn_coe, MvPolynomial.pderiv_monomial, MvPolynomial.smul_monomial,
      smul_eq_mul]
    congr 1
    rw [← mul_assoc, mul_comm _ c, mul_assoc, ← pow_succ,
      Nat.sub_add_cancel hp.out.one_lt.le, natCast_pow_char p]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The Euler operators of the polynomial ring commute. -/
theorem mvEuler_comm (i j : Fin n) :
    eulerOperator (fun k => mvPartial (K := K) n k) (fun k => MvPolynomial.X k) i ∘ₗ
        eulerOperator (fun k => mvPartial n k) (fun k => MvPolynomial.X k) j =
      eulerOperator (fun k => mvPartial n k) (fun k => MvPolynomial.X k) j ∘ₗ
        eulerOperator (fun k => mvPartial n k) (fun k => MvPolynomial.X k) i := by
  apply LinearMap.ext
  intro a
  induction a using MvPolynomial.induction_on' with
  | monomial s c =>
    simp only [LinearMap.comp_apply, mvEuler_monomial, map_smul, smul_smul]
    rw [mul_comm]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end Polynomial

section Cartier

variable {K : Type u} [CommRing K] {n : ℕ}

/-- The de Rham differential of the polynomial ring. -/
noncomputable abbrev polynomialDeRhamDiff (n : ℕ) :
    MvPolynomial (Fin n) K ⊗[K] CoordExterior K n →ₗ[K] MvPolynomial (Fin n) K ⊗[K] CoordExterior K n :=
  koszulDeRhamDiff (fun j => mvPartial n j)

/-- The weight operators of the polynomial ring. -/
noncomputable abbrev polynomialDeRhamWeight (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K ⊗[K] CoordExterior K n →ₗ[K] MvPolynomial (Fin n) K ⊗[K] CoordExterior K n :=
  koszulDeRhamWeight (fun i => mvPartial n i) (fun i => MvPolynomial.X i) j

theorem polynomialDeRhamDiff_comp_self :
    polynomialDeRhamDiff (K := K) n ∘ₗ polynomialDeRhamDiff n = 0 :=
  koszulDeRhamDiff_comp_self _ (fun i j => mvPartial_comm i j)

theorem polynomialDeRham_cartan (j : Fin n) :
    polynomialDeRhamDiff (K := K) n ∘ₗ koszulDeRhamHomotopy (fun i => MvPolynomial.X i) j +
        koszulDeRhamHomotopy (fun i => MvPolynomial.X i) j ∘ₗ polynomialDeRhamDiff n =
      polynomialDeRhamWeight n j :=
  koszulDeRham_cartan _ _ (fun i j a => mvPartial_X_mul i j a) j

theorem polynomialDeRhamDiff_comp_weight (j : Fin n) :
    polynomialDeRhamDiff (K := K) n ∘ₗ polynomialDeRhamWeight n j =
      polynomialDeRhamWeight n j ∘ₗ polynomialDeRhamDiff n :=
  koszulDeRhamDiff_comp_weight _ _ (fun i j => mvPartial_comm i j) (fun i j a => mvPartial_X_mul i j a) j

/-- The weight operators of the polynomial ring commute. -/
theorem polynomialDeRhamWeight_comm (i j : Fin n) :
    polynomialDeRhamWeight (K := K) n i ∘ₗ polynomialDeRhamWeight n j =
      polynomialDeRhamWeight n j ∘ₗ polynomialDeRhamWeight n i := by
  simp only [polynomialDeRhamWeight, koszulDeRhamWeight_eq_add, LinearMap.comp_add,
    LinearMap.add_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
    mvEuler_comm i j, coordWedgeContract_comm i j]
  abel

variable (p : ℕ)

/-- The composite of the idempotents `1 - θ_j^{p-1}` over the first `k` coordinates. -/
noncomputable def cartierProjection (k : ℕ) :
    MvPolynomial (Fin n) K ⊗[K] CoordExterior K n →ₗ[K] MvPolynomial (Fin n) K ⊗[K] CoordExterior K n :=
  match k with
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < n then
      (LinearMap.id - polynomialDeRhamWeight n ⟨k, h⟩ ^ (p - 1)) ∘ₗ cartierProjection k
    else cartierProjection k

theorem cartierProjection_zero : cartierProjection (K := K) (n := n) p 0 = LinearMap.id := rfl

theorem cartierProjection_succ_of_lt {k : ℕ} (h : k < n) :
    cartierProjection (K := K) (n := n) p (k + 1) =
      (LinearMap.id - polynomialDeRhamWeight n ⟨k, h⟩ ^ (p - 1)) ∘ₗ cartierProjection p k := by
  simp only [cartierProjection, h, dite_true]

theorem cartierProjection_succ_of_not_lt {k : ℕ} (h : ¬k < n) :
    cartierProjection (K := K) (n := n) p (k + 1) = cartierProjection p k := by
  simp only [cartierProjection, h, dite_false]

theorem polynomialDeRhamDiff_comp_weight_pow (j : Fin n) (m : ℕ) :
    polynomialDeRhamDiff (K := K) n ∘ₗ (polynomialDeRhamWeight n j ^ m) =
      (polynomialDeRhamWeight n j ^ m) ∘ₗ polynomialDeRhamDiff n := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      polynomialDeRhamDiff_comp_weight, ← LinearMap.comp_assoc]

theorem polynomialDeRhamWeight_comp_weight_pow (i j : Fin n) (m : ℕ) :
    polynomialDeRhamWeight (K := K) n i ∘ₗ (polynomialDeRhamWeight n j ^ m) =
      (polynomialDeRhamWeight n j ^ m) ∘ₗ polynomialDeRhamWeight n i := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      polynomialDeRhamWeight_comm, ← LinearMap.comp_assoc]

/-- The projection commutes with the differential. -/
theorem polynomialDeRhamDiff_comp_cartierProjection (k : ℕ) :
    polynomialDeRhamDiff (K := K) n ∘ₗ cartierProjection p k =
      cartierProjection p k ∘ₗ polynomialDeRhamDiff n := by
  induction k with
  | zero => rw [cartierProjection_zero, LinearMap.comp_id, LinearMap.id_comp]
  | succ k ih =>
    by_cases h : k < n
    · refine LinearMap.ext fun z => ?_
      have h1 := LinearMap.congr_fun ih z
      have h2 := LinearMap.congr_fun (polynomialDeRhamDiff_comp_weight_pow ⟨k, h⟩ (p - 1))
        (cartierProjection p k z)
      simp only [LinearMap.comp_apply] at h1 h2
      simp only [LinearMap.comp_apply, cartierProjection_succ_of_lt p h, LinearMap.sub_apply,
        LinearMap.id_apply, map_sub, h2, h1]
    · rw [cartierProjection_succ_of_not_lt p h, ih]

/-- The projection commutes with the weight operators. -/
theorem polynomialDeRhamWeight_comp_cartierProjection (i : Fin n) (k : ℕ) :
    polynomialDeRhamWeight (K := K) n i ∘ₗ cartierProjection p k =
      cartierProjection p k ∘ₗ polynomialDeRhamWeight n i := by
  induction k with
  | zero => rw [cartierProjection_zero, LinearMap.comp_id, LinearMap.id_comp]
  | succ k ih =>
    by_cases h : k < n
    · refine LinearMap.ext fun z => ?_
      have h1 := LinearMap.congr_fun ih z
      have h2 := LinearMap.congr_fun (polynomialDeRhamWeight_comp_weight_pow i ⟨k, h⟩ (p - 1))
        (cartierProjection p k z)
      simp only [LinearMap.comp_apply] at h1 h2
      simp only [LinearMap.comp_apply, cartierProjection_succ_of_lt p h, LinearMap.sub_apply,
        LinearMap.id_apply, map_sub, h2, h1]
    · rw [cartierProjection_succ_of_not_lt p h, ih]

variable [hp : Fact p.Prime] [CharP K p]


include hp in
theorem polynomialDeRhamWeight_pow_char (j : Fin n) :
    polynomialDeRhamWeight (K := K) n j ^ p = polynomialDeRhamWeight n j :=
  koszulDeRhamWeight_pow_of_euler p (CharP.cast_eq_zero K p) _ _ j (mvEuler_pow_char p j)

include hp in
/-- `d` vanishes where all weights vanish. -/
theorem polynomialDeRhamDiff_eq_zero_of_weights (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hz : ∀ j, polynomialDeRhamWeight n j z = 0) : polynomialDeRhamDiff n z = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [polynomialDeRhamDiff, koszulDeRhamDiff, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hpow : (polynomialDeRhamWeight (K := K) n i ^ (p - 1)) z = 0 := by
    obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by omega⟩
    rw [hq, pow_succ, Module.End.mul_apply, hz i, map_zero]
  have h := LinearMap.congr_fun (partialWedge_comp_weight_pow (fun i => mvPartial n i)
    (fun i => MvPolynomial.X i) i (p - 1)) z
  rw [LinearMap.comp_apply, hpow, map_zero, mvPartial_comp_euler_pow_pred p i] at h
  exact h.symm

omit [CharP K p] in
theorem polynomialDeRhamWeight_pow_pred_eq_zero (j : Fin n)
    (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n) (hz : polynomialDeRhamWeight n j z = 0) :
    (polynomialDeRhamWeight n j ^ (p - 1)) z = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by omega⟩
  rw [hq, pow_succ, Module.End.mul_apply, hz, map_zero]

omit [CharP K p] in
include hp in
/-- The projection is the identity where all weights vanish. -/
theorem cartierProjection_apply_of_weights (k : ℕ) (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hz : ∀ j, polynomialDeRhamWeight n j z = 0) : cartierProjection p k z = z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · rw [cartierProjection_succ_of_lt p h, LinearMap.comp_apply, ih, LinearMap.sub_apply,
        LinearMap.id_apply, polynomialDeRhamWeight_pow_pred_eq_zero p _ z (hz _), sub_zero]
    · rw [cartierProjection_succ_of_not_lt p h, ih]

include hp in
/-- The projection kills the weights of the first `k` coordinates. -/
theorem polynomialDeRhamWeight_cartierProjection (k : ℕ) (y : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (j : Fin n) (hj : (j : ℕ) < k) : polynomialDeRhamWeight n j (cartierProjection p k y) = 0 := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases h : k < n
    · rw [cartierProjection_succ_of_lt p h, LinearMap.comp_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · have hc := LinearMap.congr_fun (polynomialDeRhamWeight_comp_weight_pow j ⟨k, h⟩ (p - 1))
          (cartierProjection p k y)
        simp only [LinearMap.comp_apply] at hc
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hc, ih hjk, map_zero, sub_zero]
      · have hjk' : j = ⟨k, h⟩ := Fin.ext hjk
        subst hjk'
        have hw : polynomialDeRhamWeight n ⟨k, h⟩ ((polynomialDeRhamWeight n ⟨k, h⟩ ^ (p - 1))
            (cartierProjection p k y)) = polynomialDeRhamWeight n ⟨k, h⟩ (cartierProjection p k y) := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le,
            polynomialDeRhamWeight_pow_char p]
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hw, sub_self]
    · rw [cartierProjection_succ_of_not_lt p h]
      exact ih (by omega)

/-- A weight operator sends cocycles to coboundaries (Cartan's formula). -/
theorem polynomialDeRhamWeight_mem_range (j : Fin n) (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hz : polynomialDeRhamDiff n z = 0) :
    polynomialDeRhamWeight n j z ∈ LinearMap.range (polynomialDeRhamDiff (K := K) n) :=
  koszulDeRhamWeight_mem_range _ _ (fun i j a => mvPartial_X_mul i j a) j z hz

omit [CharP K p] in
include hp in
/-- Every cocycle differs from its projection by a coboundary. -/
theorem sub_cartierProjection_mem_range (k : ℕ) (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hz : polynomialDeRhamDiff n z = 0) :
    z - cartierProjection p k z ∈ LinearMap.range (polynomialDeRhamDiff (K := K) n) := by
  induction k with
  | zero => rw [cartierProjection_zero, LinearMap.id_apply, sub_self]; exact Submodule.zero_mem _
  | succ k ih =>
    by_cases h : k < n
    · have hw : polynomialDeRhamDiff n (cartierProjection p k z) = 0 := by
        have hc := LinearMap.congr_fun (polynomialDeRhamDiff_comp_cartierProjection p k) z
        simp only [LinearMap.comp_apply] at hc
        rw [hc, hz, map_zero]
      have hθ : (polynomialDeRhamWeight n ⟨k, h⟩ ^ (p - 1)) (cartierProjection p k z) ∈
          LinearMap.range (polynomialDeRhamDiff (K := K) n) := by
        obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by have := hp.out.two_le; omega⟩
        rw [hq, pow_succ', Module.End.mul_apply]
        apply polynomialDeRhamWeight_mem_range
        have hc := LinearMap.congr_fun (polynomialDeRhamDiff_comp_weight_pow ⟨k, h⟩ q)
          (cartierProjection p k z)
        simp only [LinearMap.comp_apply] at hc
        rw [hc, hw, map_zero]
      have heq : z - cartierProjection p (k + 1) z = (z - cartierProjection p k z) +
          (polynomialDeRhamWeight n ⟨k, h⟩ ^ (p - 1)) (cartierProjection p k z) := by
        rw [cartierProjection_succ_of_lt p h, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.id_apply]
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hθ
    · rw [cartierProjection_succ_of_not_lt p h]; exact ih

include hp in
/-- An element on which all weights vanish and which is a coboundary is zero. -/
theorem polynomialDeRham_weights_eq_zero_of_mem_range (c : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hc : ∀ j, polynomialDeRhamWeight n j c = 0)
    (hcd : c ∈ LinearMap.range (polynomialDeRhamDiff (K := K) n)) : c = 0 := by
  obtain ⟨y, rfl⟩ := hcd
  rw [← cartierProjection_apply_of_weights p n _ hc]
  have hc' := LinearMap.congr_fun (polynomialDeRhamDiff_comp_cartierProjection p n) y
  simp only [LinearMap.comp_apply] at hc'
  rw [← hc']
  exact polynomialDeRhamDiff_eq_zero_of_weights p _
    (fun j => polynomialDeRhamWeight_cartierProjection p n y j j.2)

include hp in
/-- **The Cartier decomposition of the de Rham complex of a polynomial ring in characteristic
`p`.** Every cocycle is the sum of a coboundary and a unique element on which all weight operators
vanish; `d` vanishes on such elements. Hence the cohomology is the subspace where all weights are
divisible by `p`. -/
theorem polynomialDeRham_cartier_decomposition (z : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n)
    (hz : polynomialDeRhamDiff n z = 0) :
    ∃! c : MvPolynomial (Fin n) K ⊗[K] CoordExterior K n,
      (∀ j, polynomialDeRhamWeight n j c = 0) ∧
        z - c ∈ LinearMap.range (polynomialDeRhamDiff (K := K) n) := by
  refine ⟨cartierProjection p n z, ⟨fun j => polynomialDeRhamWeight_cartierProjection p n z j j.2,
    sub_cartierProjection_mem_range p n z hz⟩, ?_⟩
  rintro c ⟨hc, hzc⟩
  have hdiff : c - cartierProjection p n z ∈ LinearMap.range (polynomialDeRhamDiff (K := K) n) := by
    have h := Submodule.sub_mem _ (sub_cartierProjection_mem_range p n z hz) hzc
    rwa [sub_sub_sub_cancel_left] at h
  have hw : ∀ j, polynomialDeRhamWeight n j (c - cartierProjection p n z) = 0 := fun j => by
    rw [map_sub, hc j, polynomialDeRhamWeight_cartierProjection p n z j j.2, sub_zero]
  exact sub_eq_zero.mp (polynomialDeRham_weights_eq_zero_of_mem_range p _ hw hdiff)

end Cartier

end MixedFujita
