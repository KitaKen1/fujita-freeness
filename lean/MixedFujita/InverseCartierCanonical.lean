/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KaehlerDeRhamFunctoriality
public import Mathlib.Tactic.Module
public import Mathlib.Data.Nat.Choose.Dvd

/-!
The inverse Cartier operator is canonical in degree one (step 10).

On an étale chart `S` of finite type over a field of characteristic `p`, the inverse Cartier
operator `C⁻¹` of check-401 is defined with the coordinates `y`. We show that for every function `f`
`C⁻¹(df) - f^{p-1} df` is exact (`etaleInverseCartier_diff_sub_mem_range`). The right side does
not mention the coordinates, so the Cartier isomorphism in degree one is canonical
(`kaehlerInverseCartier_D_sub_mem_range`, `kaehlerInverseCartier_D_coordinate_independent`).

The proof expands `f` in the coordinates with coefficients in `K·S^p` (check-399) and inducts on
the expansion, with `Δ(f) = C⁻¹(df) - f^{p-1} df`:
* `Δ(c) = 0` for `c ∈ K·S^p`, since `dc = 0`;
* `Δ(f y_j) = f^p Δ(y_j) + y_j^p Δ(f)` and `Δ(y_j) = 0`, since `C⁻¹(d y_j) = y_j^{p-1} d y_j`,
  and exact forms are stable under multiplication by `p`-th powers;
* `Δ(f + g) = Δ(f) + Δ(g) - d P(f, g)` with `P(f, g) = Σ_{0<i<p} (C(p, i)/p) f^i g^{p-i}`, by the
  identity `dP = ((f+g)^{p-1} - f^{p-1}) df + ((f+g)^{p-1} - g^{p-1}) dg`, valid for every
  derivation (`derivation_frobeniusDefect`; it is `d` of `((f+g)^p - f^p - g^p)/p` computed with
  `C(p, k+1)/p · (k+1) = C(p-1, k)` and `C(p, k+1)/p · (p-1-k) = C(p-1, k+1)`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Binomial

/-- The integer polynomial `((f + g)^{q+1} - f^{q+1} - g^{q+1}) / (q+1)` for `q + 1` prime. -/
def frobeniusDefect {A : Type*} [CommRing A] (q : ℕ) (f g : A) : A :=
  ∑ k ∈ Finset.range q, (((q + 1).choose (k + 1) / (q + 1) : ℕ) : A) * (f ^ (k + 1) * g ^ (q - k))

theorem choose_div_mul_succ {q k : ℕ} (hp : (q + 1).Prime) (hk : k < q) :
    (q + 1).choose (k + 1) / (q + 1) * (k + 1) = q.choose k := by
  obtain ⟨c, hc⟩ := hp.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
  have h := Nat.add_one_mul_choose_eq q k
  rw [hc, mul_assoc] at h
  rw [hc, Nat.mul_div_cancel_left _ (Nat.succ_pos q)]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) h).symm

theorem choose_div_mul_sub {q k : ℕ} (hp : (q + 1).Prime) (hk : k < q) :
    (q + 1).choose (k + 1) / (q + 1) * (q - k) = q.choose (k + 1) := by
  obtain ⟨c, hc⟩ := hp.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
  have h := Nat.choose_mul_succ_eq q (k + 1)
  rw [hc, show q + 1 - (k + 1) = q - k by omega, mul_assoc, mul_comm] at h
  rw [hc, Nat.mul_div_cancel_left _ (Nat.succ_pos q)]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) h).symm

/-- **The Frobenius defect identity.** For every derivation `D` and `q + 1 = p` prime,
`D P(f, g) = ((f+g)^{p-1} - f^{p-1}) Df + ((f+g)^{p-1} - g^{p-1}) Dg`. -/
theorem derivation_frobeniusDefect {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] (D : Derivation R A M)
    {q : ℕ} (hp : (q + 1).Prime) (f g : A) :
    D (frobeniusDefect q f g) = ((f + g) ^ q - f ^ q) • D f + ((f + g) ^ q - g ^ q) • D g := by
  set c : ℕ → A := fun k => (((q + 1).choose (k + 1) / (q + 1) : ℕ) : A) with hcdef
  have hc1 : ∀ k ∈ Finset.range q, c k * ((k + 1 : ℕ) : A) = (q.choose k : A) := by
    intro k hk
    rw [hcdef, ← Nat.cast_mul, choose_div_mul_succ hp (Finset.mem_range.mp hk)]
  have hc2 : ∀ k ∈ Finset.range q, c k * ((q - k : ℕ) : A) = (q.choose (k + 1) : A) := by
    intro k hk
    rw [hcdef, ← Nat.cast_mul, choose_div_mul_sub hp (Finset.mem_range.mp hk)]
  have hs1 : ∑ k ∈ Finset.range q, f ^ k * g ^ (q - k) * (q.choose k : A) = (f + g) ^ q - f ^ q := by
    rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
      Nat.cast_one, mul_one, add_sub_cancel_right]
  have hs2 : ∑ k ∈ Finset.range q, f ^ (k + 1) * g ^ (q - (k + 1)) * (q.choose (k + 1) : A) =
      (f + g) ^ q - g ^ q := by
    rw [add_pow, Finset.sum_range_succ', pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, add_sub_cancel_right]
  have hterm : ∀ k ∈ Finset.range q, D (c k * (f ^ (k + 1) * g ^ (q - k))) =
      (f ^ k * g ^ (q - k) * (q.choose k : A)) • D f +
        (f ^ (k + 1) * g ^ (q - (k + 1)) * (q.choose (k + 1) : A)) • D g := by
    intro k hk
    rw [← hc1 k hk, ← hc2 k hk, Derivation.leibniz, hcdef, D.map_natCast, smul_zero, add_zero,
      Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, Nat.add_sub_cancel,
      Nat.sub_sub, ← Nat.cast_smul_eq_nsmul A, ← Nat.cast_smul_eq_nsmul A]
    module
  rw [frobeniusDefect, map_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.sum_smul, hs1, hs2]

end Binomial

section Model

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

theorem mul_tmul_one_eq_smul (x : S ⊗[K] CoordExterior K n) (b : S) : x * (b ⊗ₜ 1) = b • x := by
  induction x using TensorProduct.inductionOn with
  | tmul a e =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul,
      mul_comm]
  | add x z hx hz => rw [add_mul, hx, hz, smul_add]

/-- The differential of functions `f ↦ df` of the coordinate model, as a derivation. -/
noncomputable def etaleFunctionDiff : Derivation K S (S ⊗[K] CoordExterior K n) :=
  Derivation.mk' (koszulDeRhamDiff (etaleCoordPartial y hy) ∘ₗ
      (TensorProduct.mk K S (CoordExterior K n)).flip 1) fun a b => by
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    have h := koszulDeRhamDiff_smul (etaleCoordPartial y hy) (etaleCoordPartial_leibniz y hy) a
      (b ⊗ₜ 1)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_tmul_one_eq_smul] at h
    rw [h, add_comm]

theorem etaleFunctionDiff_apply (f : S) :
    etaleFunctionDiff y hy f = koszulDeRhamDiff (etaleCoordPartial y hy) (f ⊗ₜ 1) := rfl

theorem etaleFunctionDiff_eq_zero_of_mem (p : ℕ) [CharP K p] {c : S}
    (hc : c ∈ frobeniusSubalgebra K S p) : etaleFunctionDiff y hy c = 0 := by
  rw [etaleFunctionDiff_apply, koszulDeRhamDiff_tmul]
  exact Finset.sum_eq_zero fun j _ => by
    rw [etaleCoordPartial_eq_zero_of_mem y hy p j hc, TensorProduct.zero_tmul]

/-- Exact forms are stable under multiplication by `p`-th powers. -/
theorem pow_smul_mem_range (p : ℕ) [CharP K p] (a : S) {η : S ⊗[K] CoordExterior K n}
    (hη : η ∈ LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy))) :
    a ^ p • η ∈ LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) := by
  obtain ⟨ξ, rfl⟩ := hη
  refine ⟨a ^ p • ξ, ?_⟩
  rw [koszulDeRhamDiff_smul _ (etaleCoordPartial_leibniz y hy), ← etaleFunctionDiff_apply,
    etaleFunctionDiff_eq_zero_of_mem y hy p (pow_mem_frobeniusSubalgebra p a), zero_mul, zero_add]

theorem etaleFunctionDiff_coordinate (i : Fin n) :
    etaleFunctionDiff y hy (etaleCoordFun y i) = (1 : S) ⊗ₜ coordVector K i := by
  classical
  rw [etaleFunctionDiff_apply, koszulDeRhamDiff_tmul, Finset.sum_eq_single i]
  · rw [mul_one]
    congr 1
    change etaleCoordinateDerivation y hy i (y (MvPolynomial.X i)) = 1
    rw [etaleCoordinateDerivation_coordinate, ite_eq_left rfl]
  · intro j _ hji
    change etaleCoordinateDerivation y hy j (y (MvPolynomial.X i)) ⊗ₜ _ = 0
    rw [etaleCoordinateDerivation_coordinate, ite_eq_right (fun h => hji h.symm),
      TensorProduct.zero_tmul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coordExteriorBasis_singleton (i : Fin n) :
    coordExteriorBasis K n {i} = coordVector K i := by
  rw [coordExteriorBasis_eq_listProd]
  simp [List.ofFn_succ]
  congr 1
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)

theorem cartierExponent_singleton (p : ℕ) (i : Fin n) :
    cartierExponent p {i} = Finsupp.single i (p - 1) := by
  ext j
  rw [cartierExponent_apply, Finsupp.single_apply]
  by_cases h : j = i
  · rw [ite_eq_left (Finset.mem_singleton.mpr h), ite_eq_left h.symm]
  · rw [ite_eq_right (fun hm => h (Finset.mem_singleton.mp hm)), ite_eq_right (fun e => h e.symm)]

theorem etaleInverseCartier_coordVector (p : ℕ) [hp : Fact p.Prime] (i : Fin n) :
    etaleInverseCartier y p ((1 : S) ⊗ₜ coordVector K i) =
      etaleCoordFun y i ^ (p - 1) • ((1 : S) ⊗ₜ coordVector K i) := by
  classical
  have hsum : (1 : S) ⊗ₜ[K] coordVector K i =
      ∑ s, (if s = {i} then (1 : S) else 0) ⊗ₜ[K] coordExteriorBasis K n s := by
    rw [Finset.sum_eq_single {i}]
    · rw [ite_eq_left rfl, coordExteriorBasis_singleton]
    · intro s _ hs
      rw [ite_eq_right hs, TensorProduct.zero_tmul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [etaleInverseCartier]
  conv_lhs => enter [2, s]; rw [hsum, coordExteriorCoeff_sum_tmul]
  rw [Finset.sum_eq_single {i}]
  · rw [ite_eq_left rfl, one_pow, one_mul, cartierExponent_singleton, coordExteriorBasis_singleton,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← MvPolynomial.X_pow_eq_monomial, map_pow]
  · intro s _ hs
    rw [ite_eq_right hs, zero_pow hp.out.ne_zero, zero_mul, TensorProduct.zero_tmul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem etaleInverseCartier_zero (p : ℕ) [Fact p.Prime] [CharP K p] :
    etaleInverseCartier y p (0 : S ⊗[K] CoordExterior K n) = 0 := by
  have h := etaleInverseCartier_sub y p (0 : S ⊗[K] CoordExterior K n) 0
  rwa [sub_self, sub_self] at h

/-- **The inverse Cartier operator is canonical in degree one**: `C⁻¹(df) - f^{p-1} df` is exact. -/
theorem etaleInverseCartier_diff_sub_mem_range (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    [Algebra.FiniteType K S] (f : S) :
    etaleInverseCartier y p (etaleFunctionDiff y hy f) - f ^ (p - 1) • etaleFunctionDiff y hy f ∈
      LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) := by
  obtain ⟨q, hq⟩ := exists_aeval_frobeniusSubalgebra_eq p y hy f
  have hq' : MvPolynomial.aeval (etaleCoordFun y) q = f := hq
  rw [← hq']
  clear hq hq'
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
  simp only [Nat.add_sub_cancel]
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C]
    have hc : etaleFunctionDiff y hy (algebraMap (frobeniusSubalgebra K S (r + 1)) S c) = 0 :=
      etaleFunctionDiff_eq_zero_of_mem y hy (r + 1) c.2
    rw [hc, etaleInverseCartier_zero, smul_zero, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    set A := MvPolynomial.aeval (etaleCoordFun y) a
    set B := MvPolynomial.aeval (etaleCoordFun y) b
    have hP := derivation_frobeniusDefect (etaleFunctionDiff y hy) hp.out A B
    have heq : etaleInverseCartier y (r + 1) (etaleFunctionDiff y hy (A + B)) -
        (A + B) ^ r • etaleFunctionDiff y hy (A + B) =
        (etaleInverseCartier y (r + 1) (etaleFunctionDiff y hy A) - A ^ r • etaleFunctionDiff y hy A) +
          (etaleInverseCartier y (r + 1) (etaleFunctionDiff y hy B) - B ^ r • etaleFunctionDiff y hy B) -
            etaleFunctionDiff y hy (frobeniusDefect r A B) := by
      rw [hP, map_add, etaleInverseCartier_add]
      module
    rw [map_add, heq]
    refine Submodule.sub_mem _ (Submodule.add_mem _ ha hb) ⟨frobeniusDefect r A B ⊗ₜ 1, rfl⟩
  | mul_X a i ha =>
    set A := MvPolynomial.aeval (etaleCoordFun y) a
    have hY := etaleFunctionDiff_coordinate y hy i
    have hΨY := etaleInverseCartier_coordVector y (r + 1) i
    rw [Nat.add_sub_cancel] at hΨY
    have heq : etaleInverseCartier y (r + 1) (etaleFunctionDiff y hy (A * etaleCoordFun y i)) -
        (A * etaleCoordFun y i) ^ r • etaleFunctionDiff y hy (A * etaleCoordFun y i) =
        etaleCoordFun y i ^ (r + 1) •
          (etaleInverseCartier y (r + 1) (etaleFunctionDiff y hy A) - A ^ r • etaleFunctionDiff y hy A) := by
      rw [Derivation.leibniz, etaleInverseCartier_add, etaleInverseCartier_smul,
        etaleInverseCartier_smul, hY, hΨY]
      module
    rw [map_mul, MvPolynomial.aeval_X, heq]
    exact pow_smul_mem_range y hy (r + 1) _ ha

end Model

section Intrinsic

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- On `⋀_S Ω[S⁄K]`: `C⁻¹(df) - f^{p-1} df` is exact. -/
theorem kaehlerInverseCartier_D_sub_mem_range (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra.FiniteType K S] (f : S) :
    kaehlerInverseCartier y hy p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S f)) -
        f ^ (p - 1) • ExteriorAlgebra.ι S (KaehlerDifferential.D K S f) ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) := by
  set Φ := coordModelKaehlerEquiv y hy
  have hι : ExteriorAlgebra.ι S (KaehlerDifferential.D K S f) = Φ (etaleFunctionDiff y hy f) :=
    (coordModelToKaehler_diff_tmul_one y hy f).symm
  obtain ⟨ξ, hξ⟩ := etaleInverseCartier_diff_sub_mem_range y hy p f
  refine ⟨Φ ξ, ?_⟩
  rw [kaehlerDeRhamDiff_apply, AlgEquiv.symm_apply_apply, hξ, map_sub, map_smul, hι,
    kaehlerInverseCartier, AlgEquiv.symm_apply_apply]

/-- **Coordinate independence of the inverse Cartier operator in degree one**: for two systems of
étale coordinates, `C⁻¹_y(df)` and `C⁻¹_z(df)` differ by an exact form. -/
theorem kaehlerInverseCartier_D_coordinate_independent {m : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra.FiniteType K S] (z : MvPolynomial (Fin m) K →ₐ[K] S) (hz : z.toRingHom.FormallyEtale)
    (f : S) :
    kaehlerInverseCartier y hy p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S f)) -
        kaehlerInverseCartier z hz p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S f)) ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) := by
  have h1 := kaehlerInverseCartier_D_sub_mem_range y hy p f
  have h2 := kaehlerInverseCartier_D_sub_mem_range z hz p f
  rw [kaehlerDeRhamDiff_eq z hz y hy] at h2
  have h := Submodule.sub_mem _ h1 h2
  rwa [sub_sub_sub_cancel_right] at h

end Intrinsic

end MixedFujita
