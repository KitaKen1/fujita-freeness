/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
The Jacobian criterion in the converse direction, and two genericity tools (step 8). Let P be a
formally smooth K-algebra and g a non-zero-divisor of P with P/(g) formally smooth. Then the
conormal map (g)/(g²) → P/(g) ⊗ Ω_P has a P-linear retraction, so the class of g is a P-multiple
of the image of dg. If dg = Σ c_j w_j with all c_j in a prime m containing g, the class of g is
a multiple a·[g] with a in m; then (1 - a) g lies in (g²), so 1 - a lies in (g) ⊆ m, which is
absurd. Hence some coefficient c_j of dg lies outside every such m: for étale coordinates, some
partial derivative ∂g/∂y_j does not vanish at the points of {g = 0}. In a Noetherian ring an
element outside the finitely many associated primes is a non-zero-divisor, and a nonzero linear
map on K^ι is nonzero at every point outside the zeros of some nonzero linear polynomial.
-/

@[expose] public section

namespace MixedFujita

open KaehlerDifferential TensorProduct

section Jacobian

variable {K P : Type*} [Field K] [CommRing P] [Algebra K P] [Algebra.FormallySmooth K P]

/-- The converse Jacobian criterion: if P/(g) is formally smooth with g a non-zero-divisor of a
formally smooth P, then in any expression dg = Σ c_j w_j some coefficient c_j lies outside a
given prime containing g. -/
theorem exists_coeff_notMem_of_formallySmooth_quotient (g : P)
    (hg : ∀ x : P, x * g = 0 → x = 0)
    (hA : Algebra.FormallySmooth K (P ⧸ Ideal.span {g})) (m : Ideal P) [m.IsPrime]
    (hgm : g ∈ m) {ι : Type*} [Fintype ι] (c : ι → P) (w : ι → Ω[P⁄K])
    (hD : D K P g = ∑ j, c j • w j) : ∃ j, c j ∉ m := by
  classical
  have hsurj : Function.Surjective (algebraMap P (P ⧸ Ideal.span {g})) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hsurj).mp hA
  have hI : RingHom.ker (algebraMap P (P ⧸ Ideal.span {g})) = Ideal.span {g} := Ideal.mk_ker
  have hgI : g ∈ RingHom.ker (algebraMap P (P ⧸ Ideal.span {g})) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self g
  -- the class of g in I/I² and its multiples
  have hgen : ∀ y : (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).Cotangent, ∃ b : P,
      y = b • (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).toCotangent ⟨g, hgI⟩ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
    have hx' : x ∈ Ideal.span {g} := by rwa [hI] at hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    refine ⟨b, ?_⟩
    rw [← map_smul]
    rfl
  by_contra hall
  push Not at hall
  -- the class of g is Σ c_j • l (1 ⊗ w_j)
  have h1 := LinearMap.congr_fun hl
    ((RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).toCotangent ⟨g, hgI⟩)
  rw [LinearMap.comp_apply, kerCotangentToTensor_toCotangent, LinearMap.id_apply] at h1
  change l (1 ⊗ₜ D K P g) = _ at h1
  rw [hD, tmul_sum, map_sum] at h1
  choose b hb using fun j => hgen (l (1 ⊗ₜ w j))
  have hza : (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).toCotangent ⟨g, hgI⟩ =
      (∑ j, c j * b j) • (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).toCotangent
        ⟨g, hgI⟩ := by
    conv_lhs => rw [← h1]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tmul_smul, map_smul, hb j, smul_smul]
  have ham : ∑ j, c j * b j ∈ m := Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hall j)
  -- (1 - a) g ∈ I², so (1 - a) g = e g²
  have h0 : (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))).toCotangent
      ((1 - ∑ j, c j * b j) • ⟨g, hgI⟩) = 0 := by
    rw [map_smul, sub_smul, one_smul, ← hza, sub_self]
  have h2 : (1 - ∑ j, c j * b j) * g ∈ (RingHom.ker (algebraMap P (P ⧸ Ideal.span {g}))) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp h0
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨e, he⟩ := h2
  have hkill : ((1 - ∑ j, c j * b j) - e * g) * g = 0 := by
    linear_combination -he
  have h1a : (1 - ∑ j, c j * b j) - e * g = 0 := hg _ hkill
  have hone : (1 : P) ∈ m := by
    have : (1 : P) = (∑ j, c j * b j) + e * g := by linear_combination h1a
    rw [this]
    exact m.add_mem ham (m.mul_mem_left e hgm)
  exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one m).mpr hone)

end Jacobian

section Generic

/-- In a Noetherian ring an element outside every associated prime is a non-zero-divisor. -/
theorem mul_eq_zero_of_notMem_associatedPrimes {R : Type*} [CommRing R] [IsNoetherianRing R]
    {x : R} (hx : ∀ p ∈ associatedPrimes R R, x ∉ p) (y : R) (hy : y * x = 0) : y = 0 := by
  by_contra hy0
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨y, hy0, by rw [smul_eq_mul, mul_comm, hy]⟩
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hmem
  exact hx p hp hxp

/-- A nonzero linear map on K^ι is nonzero outside the zeros of a nonzero linear polynomial. -/
theorem exists_mvPolynomial_ne_zero_of_linearMap_ne_zero {K : Type*} [Field K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module K M]
    (φ : (ι → K) →ₗ[K] M) (hφ : φ ≠ 0) :
    ∃ ℓ : MvPolynomial ι K, ℓ ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t ℓ ≠ 0 → φ t ≠ 0 := by
  have hlt : LinearMap.ker φ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hφ (LinearMap.ker_eq_top.mp h)
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set ℓ : MvPolynomial ι K := ∑ i, MvPolynomial.C (f fun j => if i = j then 1 else 0) *
    MvPolynomial.X i with hℓ
  have heval : ∀ t : ι → K, MvPolynomial.aeval t ℓ = f t := by
    intro t
    rw [hℓ, LinearMap.pi_apply_eq_sum_univ f t, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, smul_eq_mul, mul_comm]
    rfl
  refine ⟨ℓ, fun h0 => hf (LinearMap.ext fun t => ?_), fun t ht hφt => ht ?_⟩
  · rw [← heval t, h0, map_zero, LinearMap.zero_apply]
  · rw [heval t]
    exact hle (LinearMap.mem_ker.mpr hφt)

end Generic

end MixedFujita
