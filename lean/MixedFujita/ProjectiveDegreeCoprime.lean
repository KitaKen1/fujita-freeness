/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierBigDefinition

/-!
The degree of an embedding by a multiple of a divisor (step 4). Let J and J' be Cartier divisors
on an integral scheme over a field with k' J linearly equivalent to k J'. Then
h^0(q k' J) = h^0(q k J') for every q, so if h^0(D J)/D^d tends to ρ and h^0(D J')/D^d tends to
ρ', then ρ k'^d = ρ' k^d. For the hyperplane classes of two actual closed immersions of an
integral scheme of dimension d ≥ 1 the limits are r/d! and r'/d! with the degrees r, r' ≥ 1, so
r k'^d = r' k^d, and if k and k' are coprime then k^d divides r; in particular r ≥ k^d. For an
ample L with k L and k' L very ample this is the integrality of L^d: the degree of the embedding
by k L is k^d L^d. No Snapper polynomial, Serre vanishing or intersection theory is used; the
two-sided Hilbert asymptotics of both embeddings are the input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- If k' J ∼ k J' then q k' J and q k J' have the same number of sections. -/
theorem finrank_nsmul_of_nsmul_eq_add_principal {J J' : CartierDivisor Y} {k k' : ℕ}
    (f : Y.functionFieldˣ) (hrel : k' • J = k • J' + principalCartierDivisor Y f) (q : ℕ) :
    Module.finrank K Γ(((q * k') • J).sheaf, ⊤) = Module.finrank K Γ(((q * k) • J').sheaf, ⊤) := by
  have hdiv : (q * k') • J = (q * k) • J' + principalCartierDivisor Y (f ^ q) := by
    rw [mul_nsmul', hrel, nsmul_add, principalCartierDivisor_power, mul_nsmul']
  rw [hdiv, finrank_add_principal]

/-- The leading term along the multiples of c. -/
theorem tendsto_finrank_mul_div_pow {J : CartierDivisor Y} {d c : ℕ} (hc : 1 ≤ c) {ρ : ℝ}
    (hlim : Tendsto (fun D : ℕ => (Module.finrank K Γ((D • J).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
      atTop (nhds ρ)) :
    Tendsto (fun q : ℕ => (Module.finrank K Γ(((q * c) • J).sheaf, ⊤) : ℝ) / (q : ℝ) ^ d)
      atTop (nhds (ρ * (c : ℝ) ^ d)) := by
  have hmul : Tendsto (fun q : ℕ => q * c) atTop atTop :=
    tendsto_atTop_mono (fun q => Nat.le_mul_of_pos_right q hc) tendsto_id
  have h := (hlim.comp hmul).mul_const ((c : ℝ) ^ d)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hq0 : (q : ℝ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (by omega))
  have hc0 : (c : ℝ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (by omega))
  simp only [Function.comp_apply]
  rw [Nat.cast_mul, mul_pow, div_mul_eq_mul_div, mul_div_mul_right _ _ hc0]

/-- If k' J ∼ k J', the leading Hilbert terms satisfy ρ k'^d = ρ' k^d. -/
theorem hilbert_leading_mul_pow_eq {J J' : CartierDivisor Y} {d k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (f : Y.functionFieldˣ)
    (hrel : k' • J = k • J' + principalCartierDivisor Y f) {ρ ρ' : ℝ}
    (hlim : Tendsto (fun D : ℕ => (Module.finrank K Γ((D • J).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
      atTop (nhds ρ))
    (hlim' : Tendsto (fun D : ℕ => (Module.finrank K Γ((D • J').sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
      atTop (nhds ρ')) :
    ρ * (k' : ℝ) ^ d = ρ' * (k : ℝ) ^ d := by
  have h1 := tendsto_finrank_mul_div_pow (K := K) hk' hlim
  have h2 := tendsto_finrank_mul_div_pow (K := K) hk hlim'
  have h3 : (fun q : ℕ => (Module.finrank K Γ(((q * k') • J).sheaf, ⊤) : ℝ) / (q : ℝ) ^ d) =
      fun q : ℕ => (Module.finrank K Γ(((q * k) • J').sheaf, ⊤) : ℝ) / (q : ℝ) ^ d := by
    funext q
    rw [finrank_nsmul_of_nsmul_eq_add_principal (K := K) f hrel q]
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- Coprime multiples: from r k'^d = r' k^d, k^d divides r. -/
theorem pow_dvd_of_coprime_of_mul_pow_eq {r r' k k' d : ℕ} (hcop : Nat.Coprime k k')
    (h : r * k' ^ d = r' * k ^ d) : k ^ d ∣ r :=
  (Nat.Coprime.pow d d hcop).dvd_of_dvd_mul_right ⟨r', by rw [h, mul_comm]⟩

variable [Infinite K] {n n' : ℕ}
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
  (e' : Y ⟶ polynomialProjectiveScheme n' K) [IsClosedImmersion e']
  (g' : MvPolynomial (Fin n') K) (hg' : g'.IsHomogeneous 1)
  (hggen' : g' ∉ (e' (genericPoint Y)).asHomogeneousIdeal)

/-- Two actual closed immersions of an integral scheme of dimension d ≥ 1 whose hyperplane classes
J, J' satisfy k' J ∼ k J' with k, k' coprime: the degree r of the first, the leading Hilbert
coefficient of J, is divisible by k^d, so r ≥ k^d. -/
theorem projectiveHyperplane_degree_pow_dvd_of_coprime
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (he' : e' ≫ polynomialProjectiveToBase n' K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (hcop : Nat.Coprime k k') (f : Y.functionFieldˣ)
    (hrel : k' • projectiveHyperplaneCartier e g hg hggen =
      k • projectiveHyperplaneCartier e' g' hg' hggen' + principalCartierDivisor Y f) :
    ∃ r : ℕ, 1 ≤ r ∧ k ^ d ∣ r ∧ k ^ d ≤ r ∧
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
        atTop (nhds ((r : ℝ) / d.factorial)) := by
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hn hd
  obtain ⟨r', -, -, hlim'⟩ :=
    projectiveHyperplane_hilbert_leading_integral e' g' hg' hggen' he' hn hd
  have h := hilbert_leading_mul_pow_eq (K := K) hk hk' f hrel hlim hlim'
  have hfact : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hreal : (r : ℝ) * (k' : ℝ) ^ d = (r' : ℝ) * (k : ℝ) ^ d := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at h
    exact (div_left_inj' hfact).mp h
  have hnat : r * k' ^ d = r' * k ^ d := by exact_mod_cast hreal
  have hdvd := pow_dvd_of_coprime_of_mul_pow_eq hcop hnat
  exact ⟨r, hr, hdvd, Nat.le_of_dvd (by omega) hdvd, hlim⟩

end MixedFujita
