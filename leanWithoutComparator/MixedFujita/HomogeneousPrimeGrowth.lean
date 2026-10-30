/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemRelationBound

/-!
Growth of Hilbert functions along chains of homogeneous primes. For homogeneous ideals I ≤ J
the degree-D image of K[X]/J is a quotient of that of K[X]/I. If P ⊊ Q with P prime, a form
f ∈ Q \ P of degree e ≥ 1 gives h_Q(D + e) + h_P(D) ≤ h_P(D + e): multiplication by f is
injective modulo P and lands in the kernel of K[X]/P → K[X]/Q. Iterating, a lower bound
c D^i for h_Q gives a lower bound c' D^(i+1) for h_P. Along a chain of length d this produces
the growth D^d of the Hilbert function, which replaces the jets at a smooth point.
-/

@[expose] public section

open MvPolynomial Finset

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ]

theorem linearSystemFormImage_finrank_antitone {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J)
    (D : ℕ) : Module.finrank K (linearSystemFormImage (P := J) D) ≤
      Module.finrank K (linearSystemFormImage (P := I) D) := by
  have hcomp : (Ideal.Quotient.factorₐ K h).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ K I).toLinearMap =
      (Ideal.Quotient.mkₐ K J).toLinearMap := LinearMap.ext fun _ => rfl
  have heq : linearSystemFormImage (P := J) D =
      (linearSystemFormImage (P := I) D).map (Ideal.Quotient.factorₐ K h).toLinearMap := by
    unfold linearSystemFormImage
    rw [← Submodule.map_comp, hcomp]
  rw [heq]
  exact Submodule.finrank_map_le _ _

/-- One step up a chain of homogeneous primes. -/
theorem linearSystemFormImage_finrank_step {P Q : Ideal (MvPolynomial σ K)} [P.IsPrime]
    (hPQ : P ≤ Q) {f : MvPolynomial σ K} {e : ℕ} (hf : f.IsHomogeneous e) (hfQ : f ∈ Q)
    (hfP : f ∉ P) (D : ℕ) :
    Module.finrank K (linearSystemFormImage (P := Q) (D + e)) +
        Module.finrank K (linearSystemFormImage (P := P) D) ≤
      Module.finrank K (linearSystemFormImage (P := P) (D + e)) := by
  have hcomp : (Ideal.Quotient.factorₐ K hPQ).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ K P).toLinearMap =
      (Ideal.Quotient.mkₐ K Q).toLinearMap := LinearMap.ext fun _ => rfl
  set FP := linearSystemFormImage (P := P) (D + e) with hFP
  let φ : ↥FP →ₗ[K] MvPolynomial σ K ⧸ Q :=
    (Ideal.Quotient.factorₐ K hPQ).toLinearMap ∘ₗ FP.subtype
  have hrange : LinearMap.range φ = linearSystemFormImage (P := Q) (D + e) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, hFP]
    unfold linearSystemFormImage
    rw [← Submodule.map_comp, hcomp]
  have hne : Ideal.Quotient.mk P f ≠ 0 := fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let μ := LinearMap.mulLeft K (Ideal.Quotient.mk P f)
  have hμ : Function.Injective μ := mul_right_injective₀ hne
  let M := (linearSystemFormImage (P := P) D).map μ
  have hMF : M ≤ FP := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨f * g, ?_, ?_⟩
    · have h := hf.mul ((mem_homogeneousSubmodule _ _).mp hg)
      rw [Nat.add_comm e D] at h
      exact (mem_homogeneousSubmodule _ _).mpr h
    · change Ideal.Quotient.mk P (f * g) = Ideal.Quotient.mk P f * Ideal.Quotient.mk P g
      exact map_mul _ _ _
  have hMker : M.comap FP.subtype ≤ LinearMap.ker φ := by
    intro z hz
    obtain ⟨w, _, hzw⟩ := hz
    have hzw' : (z : MvPolynomial σ K ⧸ P) = Ideal.Quotient.mk P f * w := hzw.symm
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.factor hPQ (z : MvPolynomial σ K ⧸ P) = 0
    rw [hzw']
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, zero_mul]
  have hMrank : Module.finrank K (M.comap FP.subtype) =
      Module.finrank K (linearSystemFormImage (P := P) D) := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hMF)]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective μ hμ _)).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hker := Submodule.finrank_mono hMker
  rw [hrange] at hrn
  omega

omit [Fintype σ] in
/-- A strict inclusion of homogeneous ideals is witnessed by a form of positive degree. -/
theorem exists_homogeneous_mem_not_mem {P Q : Ideal (MvPolynomial σ K)}
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (hlt : P < Q) (hQtop : Q ≠ ⊤) :
    ∃ e, 1 ≤ e ∧ ∃ f : MvPolynomial σ K, f.IsHomogeneous e ∧ f ∈ Q ∧ f ∉ P := by
  classical
  obtain ⟨g, hgQ, hgP⟩ := IsConcreteLE.exists_of_lt hlt
  have hcomp : ∀ i, homogeneousComponent i g ∈ Q := by
    intro i
    have h := hQ i hgQ
    rwa [show (DirectSum.decompose (homogeneousSubmodule σ K) g i : MvPolynomial σ K) =
      homogeneousComponent i g from decomposition.decompose'_apply g i] at h
  have hex : ∃ i, homogeneousComponent i g ∉ P := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hgP
    rw [← sum_homogeneousComponent g]
    exact P.sum_mem fun i _ => h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_, homogeneousComponent i g, homogeneousComponent_isHomogeneous i g, hcomp i, hi⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exfalso
    apply hQtop
    have h0 := hcomp 0
    rw [homogeneousComponent_zero] at h0 hi
    have hc : g.coeff 0 ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hi
      exact hi P.zero_mem
    exact Ideal.eq_top_of_isUnit_mem _ h0 ((IsUnit.mk0 _ hc).map C)
  · exact hpos

/-- Iterating the step along the arithmetic progression N, N - e, N - 2e, .... -/
theorem sum_le_of_step {hP hQ : ℕ → ℕ} {e : ℕ} (hrec : ∀ D, hQ (D + e) + hP D ≤ hP (D + e)) :
    ∀ k N, k * e ≤ N → ∑ j ∈ range k, hQ (N - j * e) ≤ hP N := by
  intro k
  induction k with
  | zero => intro N _; simp
  | succ k ih =>
    intro N hN
    rw [Finset.sum_range_succ']
    have hNe : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (Nat.succ_pos k)) hN
    have hIH := ih (N - e) (by rw [Nat.succ_mul] at hN; omega)
    have hshift : ∑ j ∈ range k, hQ (N - (j + 1) * e) = ∑ j ∈ range k, hQ (N - e - j * e) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [Nat.succ_mul, Nat.sub_sub, Nat.add_comm (j * e) e]
    have hstep := hrec (N - e)
    rw [Nat.sub_add_cancel hNe] at hstep
    rw [hshift]
    simp only [zero_mul, Nat.sub_zero]
    omega

/-- A lower bound c D^i propagates one degree up the chain. -/
theorem growth_step {hP hQ : ℕ → ℕ} {e i : ℕ} (he : 1 ≤ e)
    (hrec : ∀ D, hQ (D + e) + hP D ≤ hP (D + e))
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → c * (D : ℝ) ^ i ≤ hQ D) :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → c * (D : ℝ) ^ (i + 1) ≤ hP D := by
  obtain ⟨c, hc, D₀, hD₀⟩ := hlow
  refine ⟨c / (4 * e * 2 ^ i), by positivity, 2 * D₀ + 4 * e, fun N hN => ?_⟩
  set k := N / (2 * e) with hk
  have he' : 0 < 2 * e := by omega
  have hkN : k * e ≤ N := by
    have := Nat.div_mul_le_self N (2 * e)
    rw [← hk] at this
    nlinarith
  have hlt := Nat.lt_div_mul_add (a := N) he'
  rw [← hk] at hlt
  -- each term is at least c (N/2)^i
  have hterm : ∀ j ∈ range k, c * ((N : ℝ) / 2) ^ i ≤ (hQ (N - j * e) : ℝ) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hje : j * e ≤ k * e := Nat.mul_le_mul_right e hjk.le
    have h2 : 2 * (k * e) ≤ N := by
      have := Nat.div_mul_le_self N (2 * e)
      rw [← hk] at this
      nlinarith
    have hbig : D₀ ≤ N - j * e := by omega
    have hreal : (N : ℝ) / 2 ≤ ((N - j * e : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 * (k * e) : ℝ) ≤ N := by exact_mod_cast h2
      have : (j * e : ℝ) ≤ k * e := by exact_mod_cast hje
      push_cast
      linarith
    calc c * ((N : ℝ) / 2) ^ i ≤ c * ((N - j * e : ℕ) : ℝ) ^ i :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hreal i) hc.le
      _ ≤ _ := hD₀ _ hbig
  have hsum := sum_le_of_step hrec k N hkN
  have hsumR : (k : ℝ) * (c * ((N : ℝ) / 2) ^ i) ≤ (hP N : ℝ) := by
    have h1 : ∑ j ∈ range k, c * ((N : ℝ) / 2) ^ i ≤ ∑ j ∈ range k, (hQ (N - j * e) : ℝ) :=
      Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have h2 : (∑ j ∈ range k, (hQ (N - j * e) : ℝ)) ≤ hP N := by exact_mod_cast hsum
    linarith
  -- k ≥ N / (4e)
  have hkreal : (N : ℝ) / (4 * e) ≤ k := by
    have h1 : (N : ℝ) < k * (2 * e) + 2 * e := by exact_mod_cast hlt
    have h2 : (4 * e : ℝ) ≤ N := by exact_mod_cast (by omega : 4 * e ≤ N)
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc c / (4 * e * 2 ^ i) * (N : ℝ) ^ (i + 1)
      = ((N : ℝ) / (4 * e)) * (c * ((N : ℝ) / 2) ^ i) := by
        have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
        rw [div_pow, pow_succ]
        field_simp
    _ ≤ (k : ℝ) * (c * ((N : ℝ) / 2) ^ i) :=
        mul_le_mul_of_nonneg_right hkreal (by positivity)
    _ ≤ _ := hsumR

end MixedFujita
