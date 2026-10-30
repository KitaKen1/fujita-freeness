/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCartierWeights

/-!
The inverse Cartier operator and the Cartier isomorphism on étale charts (step 10).

Let `K` be a field of characteristic `p` and `S` a `K`-algebra of finite type with formally étale
coordinates `y`. Write forms of the coordinate de Rham complex as `ω = Σ_s ω_s ⊗ e_s`. The inverse
Cartier operator is
`C⁻¹ ω = Σ_s ω_s^p · y_s^{p-1} ⊗ e_s`, `y_s^{p-1} = Π_{j ∈ s} y_j^{p-1}`
(`etaleInverseCartier`). It is additive and Frobenius-semilinear (`C⁻¹(a ω) = a^p C⁻¹ ω`), and its
values are killed by all weight operators (check-400), hence are cocycles.

If `K` is perfect, `K·S^p` consists of `p`-th powers (`exists_pow_eq_of_mem_frobeniusSubalgebra`),
so by check-400 every form killed by the weight operators is a value of `C⁻¹`. If moreover `S` is a
domain and the coordinates are nonzero, `C⁻¹` is injective. With the Cartier decomposition of
check-397 this gives **the Cartier isomorphism on an étale chart**: every cocycle `z` is
`C⁻¹ ω + d η` for a unique `ω` (`etale_cartier_isomorphism`). In other words, `ω ↦ [C⁻¹ ω]` is a
bijection from the forms of `S` (on which `S` acts through Frobenius) onto the de Rham cohomology
of `S`, preserving the exterior degree.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section CharP

/-- In a commutative ring in which the prime `p` vanishes, `(u + v)^p = u^p + v^p`. -/
theorem add_pow_prime_of_natCast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (hpA : (p : A) = 0) (u v : A) : (u + v) ^ p = u ^ p + v ^ p := by
  rw [add_pow_prime_eq hp u v, hpA, zero_mul, zero_mul, zero_mul, add_zero]

end CharP

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}

theorem natCast_char_eq_zero_of_algebra (p : ℕ) [CharP K p] : (p : S) = 0 := by
  rw [← map_natCast (algebraMap K S), CharP.cast_eq_zero, map_zero]

/-- Over a perfect field, the subalgebra `K·S^p` consists of `p`-th powers. -/
theorem exists_pow_eq_of_mem_frobeniusSubalgebra (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    [PerfectRing K p] {c : S} (hc : c ∈ frobeniusSubalgebra K S p) : ∃ a : S, a ^ p = c := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩
  | algebraMap r =>
    obtain ⟨t, ht⟩ := surjective_frobenius K p r
    refine ⟨algebraMap K S t, ?_⟩
    rw [← map_pow, ← ht, frobenius_def]
  | add x z _ _ hx hz =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, add_pow_prime_of_natCast_eq_zero hp.out hpS a b⟩
  | mul x z _ _ hx hz =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a * b, mul_pow a b p⟩

section Coefficients

/-- The coefficient of `1 ⊗ e_s` in a form. -/
noncomputable abbrev coordExteriorCoeff (ω : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) : S :=
  (Algebra.TensorProduct.basis S (coordExteriorBasis K n)).repr ω s

theorem coordExteriorCoeff_sum_tmul (a : Finset (Fin n) → S) (s : Finset (Fin n)) :
    coordExteriorCoeff (∑ t, a t ⊗ₜ[K] coordExteriorBasis K n t) s = a s := by
  have h : (∑ t, a t ⊗ₜ[K] coordExteriorBasis K n t) =
      ∑ t, a t • (Algebra.TensorProduct.basis S (coordExteriorBasis K n)) t := by
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [coordExteriorCoeff, h, Module.Basis.repr_sum_self]

theorem coordExteriorCoeff_add (ω η : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) :
    coordExteriorCoeff (ω + η) s = coordExteriorCoeff ω s + coordExteriorCoeff η s := by
  rw [coordExteriorCoeff, map_add, Finsupp.add_apply]

theorem coordExteriorCoeff_sub (ω η : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) :
    coordExteriorCoeff (ω - η) s = coordExteriorCoeff ω s - coordExteriorCoeff η s := by
  rw [coordExteriorCoeff, map_sub, Finsupp.sub_apply]

theorem coordExteriorCoeff_smul (a : S) (ω : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) :
    coordExteriorCoeff (a • ω) s = a * coordExteriorCoeff ω s := by
  rw [coordExteriorCoeff, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem eq_zero_of_coordExteriorCoeff (ω : S ⊗[K] CoordExterior K n)
    (h : ∀ s, coordExteriorCoeff ω s = 0) : ω = 0 := by
  rw [eq_sum_tmul_coordExteriorBasis ω]
  exact Finset.sum_eq_zero fun s _ => by rw [show (Algebra.TensorProduct.basis S
    (coordExteriorBasis K n)).repr ω s = 0 from h s, TensorProduct.zero_tmul]

end Coefficients

section Etale

variable (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- **The inverse Cartier operator on an étale chart**: `Σ_s ω_s e_s ↦ Σ_s ω_s^p y_s^{p-1} e_s`. -/
noncomputable def etaleInverseCartier (p : ℕ) (ω : S ⊗[K] CoordExterior K n) :
    S ⊗[K] CoordExterior K n :=
  ∑ s, (coordExteriorCoeff ω s ^ p * y (MvPolynomial.monomial (cartierExponent p s) 1)) ⊗ₜ[K]
    coordExteriorBasis K n s

theorem etaleInverseCartier_add (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (ω η : S ⊗[K] CoordExterior K n) :
    etaleInverseCartier y p (ω + η) = etaleInverseCartier y p ω + etaleInverseCartier y p η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [etaleInverseCartier, coordExteriorCoeff_add, add_pow_prime_of_natCast_eq_zero hp.out hpS,
    add_mul, TensorProduct.add_tmul, Finset.sum_add_distrib]

theorem etaleInverseCartier_sub (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (ω η : S ⊗[K] CoordExterior K n) :
    etaleInverseCartier y p (ω - η) = etaleInverseCartier y p ω - etaleInverseCartier y p η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [etaleInverseCartier, coordExteriorCoeff_sub, sub_pow_prime_of_natCast_eq_zero hp.out hpS,
    sub_mul, TensorProduct.sub_tmul, Finset.sum_sub_distrib]

/-- The inverse Cartier operator is Frobenius-semilinear. -/
theorem etaleInverseCartier_smul (p : ℕ) (a : S) (ω : S ⊗[K] CoordExterior K n) :
    etaleInverseCartier y p (a • ω) = a ^ p • etaleInverseCartier y p ω := by
  simp only [etaleInverseCartier, coordExteriorCoeff_smul, mul_pow, Finset.smul_sum,
    TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]

theorem coordExteriorCoeff_etaleInverseCartier (p : ℕ) (ω : S ⊗[K] CoordExterior K n)
    (s : Finset (Fin n)) :
    coordExteriorCoeff (etaleInverseCartier y p ω) s =
      coordExteriorCoeff ω s ^ p * y (MvPolynomial.monomial (cartierExponent p s) 1) :=
  coordExteriorCoeff_sum_tmul _ s

/-- The values of the inverse Cartier operator are killed by all weight operators. -/
theorem etaleInverseCartier_weights (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra.FiniteType K S]
    (ω : S ⊗[K] CoordExterior K n) (j : Fin n) :
    koszulDeRhamWeight (etaleCoordPartial y hy) (etaleCoordFun y) j (etaleInverseCartier y p ω) = 0 :=
  (etaleCartierSubspace_iff y hy p _).mpr ⟨fun s => coordExteriorCoeff ω s ^ p,
    fun _ => pow_mem_frobeniusSubalgebra p _, rfl⟩ j

/-- The values of the inverse Cartier operator are cocycles. -/
theorem etaleInverseCartier_cocycle (p : ℕ) [hp : Fact p.Prime] [CharP K p] [Algebra.FiniteType K S]
    [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (ω : S ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff (etaleCoordPartial y hy) (etaleInverseCartier y p ω) = 0 :=
  koszulDeRhamDiff_eq_zero_of_weights (etaleCoordPartial y hy) (etaleCoordFun y) p
    (etalePartial_comp_euler_pow_pred y hy p hy0) _ (etaleInverseCartier_weights y hy p ω)

/-- The monomials `y_s^{p-1}` are nonzero on a domain with nonzero coordinates. -/
theorem cartierMonomial_ne_zero (p : ℕ) [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (s : Finset (Fin n)) : y (MvPolynomial.monomial (cartierExponent p s) 1) ≠ 0 := by
  rw [coordinate_monomial_eq_prod, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)

/-- On a domain with nonzero coordinates the inverse Cartier operator is injective. -/
theorem etaleInverseCartier_injective (p : ℕ) [hp : Fact p.Prime] [CharP K p] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) :
    Function.Injective (etaleInverseCartier y p : S ⊗[K] CoordExterior K n → _) := by
  intro ω η h
  rw [← sub_eq_zero]
  apply eq_zero_of_coordExteriorCoeff
  intro s
  have h1 : etaleInverseCartier y p (ω - η) = 0 := by
    rw [etaleInverseCartier_sub y p, h, sub_self]
  have h2 := coordExteriorCoeff_etaleInverseCartier y p (ω - η) s
  rw [h1, coordExteriorCoeff, map_zero, Finsupp.zero_apply] at h2
  exact pow_eq_zero_iff hp.out.ne_zero |>.mp
    ((mul_eq_zero.mp h2.symm).resolve_right (cartierMonomial_ne_zero y p hy0 s))

/-- Over a perfect field every form killed by the weight operators is a value of the inverse
Cartier operator. -/
theorem exists_etaleInverseCartier_eq (p : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]
    [Algebra.FiniteType K S] (c : S ⊗[K] CoordExterior K n)
    (hc : ∀ j, koszulDeRhamWeight (etaleCoordPartial y hy) (etaleCoordFun y) j c = 0) :
    ∃ ω, etaleInverseCartier y p ω = c := by
  obtain ⟨a, ha, rfl⟩ := (etaleCartierSubspace_iff y hy p c).mp hc
  choose b hb using fun s => exists_pow_eq_of_mem_frobeniusSubalgebra p (ha s)
  refine ⟨∑ s, b s ⊗ₜ[K] coordExteriorBasis K n s, ?_⟩
  rw [etaleInverseCartier]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coordExteriorCoeff_sum_tmul, hb s]

/-- **The Cartier isomorphism on an étale chart.** Over a perfect field of characteristic `p`, for a
domain of finite type with nonzero formally étale coordinates, every cocycle of the coordinate de
Rham complex is `C⁻¹ ω` plus a coboundary for a unique form `ω`. -/
theorem etale_cartier_isomorphism (p : ℕ) [hp : Fact p.Prime] [CharP K p] [PerfectRing K p]
    [Algebra.FiniteType K S] [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : S ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff (etaleCoordPartial y hy) z = 0) :
    ∃! ω : S ⊗[K] CoordExterior K n,
      z - etaleInverseCartier y p ω ∈ LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) := by
  obtain ⟨c, ⟨hcw, hcr⟩, huniq⟩ := etale_cartier_decomposition y hy p hy0 z hz
  obtain ⟨ω₀, hω₀⟩ := exists_etaleInverseCartier_eq y hy p c hcw
  refine ⟨ω₀, ?_, fun ω hω => ?_⟩
  · show z - etaleInverseCartier y p ω₀ ∈ _
    rw [hω₀]
    exact hcr
  have h := huniq (etaleInverseCartier y p ω) ⟨etaleInverseCartier_weights y hy p ω, hω⟩
  exact etaleInverseCartier_injective y p hy0 (h.trans hω₀.symm)

end Etale

end MixedFujita
