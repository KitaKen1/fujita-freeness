/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftOneForms

/-!
The Deligne–Illusie map of a Frobenius lift on an étale chart, in all degrees (step 10).

Let `S` be an étale chart of finite type over a field `K` of characteristic `p`, with a lift
`π : L → S` modulo `p²` and a Frobenius lift `F` as in check-407, such that the elements of `K`
have Frobenius-fixed lifts. The degree-one map `φ(a) = a^{p-1} da + dδ(ã)` vanishes on `K·S^p`
(`frobeniusLiftOneForm_eq_zero_of_mem`) and satisfies the chain rule
`φ(a) = Σ_j (∂_j a)^p φ(y_j)` (`frobeniusLiftOneFormAux_D`), so it extends to a Frobenius-semilinear
map of `1`-forms and then, through the Frobenius-twisted exterior algebra of check-405, to a ring
homomorphism `Φ_F` of `⋀_S Ω[S⁄K]` with `Φ_F(da) = φ(a)` (`frobeniusLiftExteriorHom`).

Its values are closed (`frobeniusLiftExterior_closed`). A general comparison principle
(`cartier_comparison`: two unital, additive, multiplicative, Frobenius-semilinear maps, one with
closed values and the other with closed `1`-form values on exact `1`-forms, agreeing up to exact forms
on exact `1`-forms, agree up to exact forms everywhere) shows `Φ_F ≡ C⁻¹` modulo exact forms. Hence,
over a perfect field and for a domain with nonzero coordinates, **every cocycle is `Φ_F(ω)` plus a
coboundary for a unique `ω`** (`frobeniusLift_cartier_isomorphism`): the Deligne–Illusie map of a
Frobenius lift is a quasi-isomorphism `(⋀_S Ω, 0) → (⋀_S Ω, d)` on each étale chart.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Comparison

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- **Comparison principle.** Two unital, additive, multiplicative, Frobenius-semilinear maps of
`⋀_S Ω[S⁄K]` agree up to exact forms if the first has closed values, the second sends exact
`1`-forms to closed `1`-forms, and they agree up to exact forms on exact `1`-forms. -/
theorem cartier_comparison (p : ℕ) [CharP K p]
    (Ψ₁ Ψ₂ : ExteriorAlgebra S Ω[S⁄K] → ExteriorAlgebra S Ω[S⁄K])
    (h1 : Ψ₁ 1 = 1) (h1' : Ψ₂ 1 = 1)
    (hadd : ∀ x x', Ψ₁ (x + x') = Ψ₁ x + Ψ₁ x') (hadd' : ∀ x x', Ψ₂ (x + x') = Ψ₂ x + Ψ₂ x')
    (hsmul : ∀ (c : S) x, Ψ₁ (c • x) = c ^ p • Ψ₁ x) (hsmul' : ∀ (c : S) x, Ψ₂ (c • x) = c ^ p • Ψ₂ x)
    (hmul : ∀ x x', Ψ₁ (x * x') = Ψ₁ x * Ψ₁ x') (hmul' : ∀ x x', Ψ₂ (x * x') = Ψ₂ x * Ψ₂ x')
    (hclosed : ∀ x, kaehlerDeRhamDiff y hy (Ψ₁ x) = 0)
    (hone : ∀ g : S, ∃ v : Ω[S⁄K], Ψ₂ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) =
      ExteriorAlgebra.ι S v ∧ kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S v) = 0)
    (hdeg1 : ∀ g : S, Ψ₁ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) -
      Ψ₂ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) ∈ LinearMap.range (kaehlerDeRhamDiff y hy))
    (x : ExteriorAlgebra S Ω[S⁄K]) : Ψ₁ x - Ψ₂ x ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
  have h0 : ∀ Ψ : ExteriorAlgebra S Ω[S⁄K] → ExteriorAlgebra S Ω[S⁄K],
      (∀ x x', Ψ (x + x') = Ψ x + Ψ x') → Ψ 0 = 0 := fun Ψ h => by
    have := h 0 0
    rwa [add_zero, left_eq_add] at this
  induction x using kaehlerExterior_mul_induction with
  | h1 => rw [h1, h1', sub_self]; exact Submodule.zero_mem _
  | hsmul f ω h => rw [hsmul, hsmul', ← smul_sub]; exact kaehler_pow_smul_mem_range y hy p f h
  | hD g ω h =>
    rw [hmul, hmul']
    obtain ⟨ξ, hξ⟩ := hdeg1 g
    obtain ⟨β, hβ⟩ := h
    obtain ⟨v, hv, hvc⟩ := hone g
    have heq : Ψ₁ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) * Ψ₁ ω -
        Ψ₂ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) * Ψ₂ ω =
        kaehlerDeRhamDiff y hy ξ * Ψ₁ ω + ExteriorAlgebra.ι S v * kaehlerDeRhamDiff y hy β := by
      rw [hξ, hβ, ← hv]
      noncomm_ring
    rw [heq]
    refine Submodule.add_mem _ ⟨ξ * Ψ₁ ω, kaehlerDeRhamDiff_mul_of_closed y hy _ _ (hclosed ω)⟩ ?_
    have h2 := kaehlerDeRhamDiff_one_form_mul y hy v β
    rw [hvc, zero_mul, add_eq_zero_iff_eq_neg] at h2
    rw [h2, ← map_neg]
    exact ⟨_, rfl⟩
  | hadd ω ω' h h' =>
    rw [hadd, hadd', add_sub_add_comm]
    exact Submodule.add_mem _ h h'
  | h0 => rw [h0 Ψ₁ hadd, h0 Ψ₂ hadd', sub_self]; exact Submodule.zero_mem _

end Comparison

section Extension

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p)

include hann hp2 in
theorem frobeniusLiftOneForm_pow_succ (a : S) (m : ℕ) :
    frobeniusLiftOneForm K π hπ p F hF hker (a ^ (m + 1)) =
      ((m + 1 : ℕ) : S) • (a ^ p) ^ m • frobeniusLiftOneForm K π hπ p F hF hker a := by
  induction m with
  | zero => rw [zero_add, pow_one, pow_zero, one_smul, Nat.cast_one, one_smul]
  | succ m ih =>
    rw [pow_succ, frobeniusLiftOneForm_mul π hπ p F hF hker hann hp2, ih]
    have h1 : (a ^ (m + 1)) ^ p = (a ^ p) ^ (m + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h1]
    push_cast
    module

include hann hp2 hK in
/-- `φ` vanishes on `K·S^p`. -/
theorem frobeniusLiftOneForm_eq_zero_of_mem {c : S} (hc : c ∈ frobeniusSubalgebra K S p) :
    frobeniusLiftOneForm K π hπ p F hF hker c = 0 := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    have h := frobeniusLiftOneForm_pow_succ (K := K) π hπ p F hF hker hann hp2 a q
    rw [← hq, hpS, zero_smul] at h
    exact h
  | algebraMap c => exact frobeniusLiftOneForm_algebraMap π hπ p F hF hker hann hp2 hK c
  | add x z _ _ hx hz => rw [frobeniusLiftOneForm_add π hπ p F hF hker hann hp2, hx, hz, add_zero]
  | mul x z _ _ hx hz =>
    rw [frobeniusLiftOneForm_mul π hπ p F hF hker hann hp2, hx, hz, smul_zero, smul_zero, add_zero]

/-- `φ` on `1`-forms through the étale basis: `Σ_j ω_j dy_j ↦ Σ_j ω_j^p φ(y_j)`. -/
noncomputable def frobeniusLiftOneFormAux (ω : Ω[S⁄K]) : Ω[S⁄K] :=
  ∑ j, (etaleCoordinateBasis y hy).repr ω j ^ p • frobeniusLiftOneForm K π hπ p F hF hker (etaleCoordFun y j)

theorem frobeniusLiftOneFormAux_add (ω η : Ω[S⁄K]) :
    frobeniusLiftOneFormAux y hy π hπ p F hF hker (ω + η) =
      frobeniusLiftOneFormAux y hy π hπ p F hF hker ω + frobeniusLiftOneFormAux y hy π hπ p F hF hker η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [frobeniusLiftOneFormAux, map_add, Finsupp.add_apply,
    add_pow_prime_of_natCast_eq_zero hp.out hpS, add_smul, Finset.sum_add_distrib]

omit hp [CharP K p] in
theorem frobeniusLiftOneFormAux_smul (c : S) (ω : Ω[S⁄K]) :
    frobeniusLiftOneFormAux y hy π hπ p F hF hker (c • ω) =
      c ^ p • frobeniusLiftOneFormAux y hy π hπ p F hF hker ω := by
  simp only [frobeniusLiftOneFormAux, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_pow,
    Finset.smul_sum, smul_smul]

omit [CharP K p] in
theorem frobeniusLiftOneFormAux_coordinate (i : Fin n) :
    frobeniusLiftOneFormAux y hy π hπ p F hF hker (KaehlerDifferential.D K S (etaleCoordFun y i)) =
      frobeniusLiftOneForm K π hπ p F hF hker (etaleCoordFun y i) := by
  classical
  have hb : KaehlerDifferential.D K S (etaleCoordFun y i) = etaleCoordinateBasis y hy i :=
    (etaleCoordinateBasis_apply y hy i).symm
  rw [frobeniusLiftOneFormAux, hb, Finset.sum_eq_single i]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_pow, one_smul]
  · intro j _ hji
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne' hji.symm,
      zero_pow (Fact.out : p.Prime).ne_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

include hann hp2 hK in
/-- **Chain rule** `φ(a) = Σ_j (∂_j a)^p φ(y_j)`. -/
theorem frobeniusLiftOneFormAux_D [Algebra.FiniteType K S] (a : S) :
    frobeniusLiftOneFormAux y hy π hπ p F hF hker (KaehlerDifferential.D K S a) =
      frobeniusLiftOneForm K π hπ p F hF hker a := by
  obtain ⟨q, hq⟩ := exists_aeval_frobeniusSubalgebra_eq p y hy a
  have hq' : MvPolynomial.aeval (etaleCoordFun y) q = a := hq
  rw [← hq']
  clear hq hq'
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C]
    have hD : KaehlerDifferential.D K S (algebraMap (frobeniusSubalgebra K S p) S c) = 0 :=
      derivation_eq_zero_of_mem_frobeniusSubalgebra p (KaehlerDifferential.D K S) c.2
    have hφ : frobeniusLiftOneForm K π hπ p F hF hker (algebraMap (frobeniusSubalgebra K S p) S c) = 0 :=
      frobeniusLiftOneForm_eq_zero_of_mem π hπ p F hF hker hann hp2 hK c.2
    rw [hD, hφ]
    have := frobeniusLiftOneFormAux_smul y hy π hπ p F hF hker 0 0
    rwa [zero_smul, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul] at this
  | add a b ha hb =>
    rw [map_add, map_add, frobeniusLiftOneFormAux_add, ha, hb,
      frobeniusLiftOneForm_add π hπ p F hF hker hann hp2]
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, frobeniusLiftOneFormAux_add,
      frobeniusLiftOneFormAux_smul, frobeniusLiftOneFormAux_smul, ha,
      frobeniusLiftOneFormAux_coordinate, frobeniusLiftOneForm_mul π hπ p F hF hker hann hp2, add_comm]

/-- `φ` on `1`-forms, `S`-linear into the Frobenius-twisted exterior algebra. -/
noncomputable def frobeniusLiftOneFormMap : Ω[S⁄K] →ₗ[S] FrobeniusTwistedExterior K S p where
  toFun ω := ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω)
  map_add' ω η := by
    change ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker (ω + η)) =
      ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω) +
        ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker η)
    rw [frobeniusLiftOneFormAux_add, map_add]
  map_smul' c ω := by
    change ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker (c • ω)) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄K]) (c ^ p) *
        ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω)
    rw [frobeniusLiftOneFormAux_smul, map_smul, Algebra.smul_def]

/-- **The Deligne–Illusie map of a Frobenius lift**, a ring homomorphism of `⋀_S Ω[S⁄K]`. -/
noncomputable def frobeniusLiftExteriorHom :
    ExteriorAlgebra S Ω[S⁄K] →ₐ[S] FrobeniusTwistedExterior K S p :=
  ExteriorAlgebra.lift S ⟨frobeniusLiftOneFormMap y hy π hπ p F hF hker, fun ω => by
    change ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω) *
      ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω) = 0
    exact ExteriorAlgebra.ι_sq_zero _⟩

/-- The Deligne–Illusie map as a function of `⋀_S Ω[S⁄K]`. -/
noncomputable def frobeniusLiftExterior (x : ExteriorAlgebra S Ω[S⁄K]) : ExteriorAlgebra S Ω[S⁄K] :=
  twistedToExterior (frobeniusLiftExteriorHom y hy π hπ p F hF hker x)

theorem frobeniusLiftExterior_ι (ω : Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker (ExteriorAlgebra.ι S ω) =
      ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω) := by
  rw [frobeniusLiftExterior, frobeniusLiftExteriorHom, ExteriorAlgebra.lift_ι_apply]
  rfl

theorem frobeniusLiftExterior_one : frobeniusLiftExterior y hy π hπ p F hF hker 1 = 1 :=
  congrArg twistedToExterior (map_one _)

theorem frobeniusLiftExterior_add (x x' : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker (x + x') =
      frobeniusLiftExterior y hy π hπ p F hF hker x + frobeniusLiftExterior y hy π hπ p F hF hker x' :=
  congrArg twistedToExterior (map_add _ x x')

theorem frobeniusLiftExterior_mul (x x' : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker (x * x') =
      frobeniusLiftExterior y hy π hπ p F hF hker x * frobeniusLiftExterior y hy π hπ p F hF hker x' :=
  congrArg twistedToExterior (map_mul _ x x')

theorem frobeniusLiftExterior_smul (c : S) (x : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker (c • x) =
      c ^ p • frobeniusLiftExterior y hy π hπ p F hF hker x := by
  rw [frobeniusLiftExterior, map_smul, frobeniusTwisted_smul_eq]
  rfl

include hann hp2 hK in
theorem frobeniusLiftExterior_ι_D [Algebra.FiniteType K S] (a : S) :
    frobeniusLiftExterior y hy π hπ p F hF hker (ExteriorAlgebra.ι S (KaehlerDifferential.D K S a)) =
      ExteriorAlgebra.ι S (frobeniusLiftOneForm K π hπ p F hF hker a) := by
  rw [frobeniusLiftExterior_ι, frobeniusLiftOneFormAux_D y hy π hπ p F hF hker hann hp2 hK]

include hann hp2 hK in
/-- The values of the Deligne–Illusie map are closed. -/
theorem frobeniusLiftExterior_closed [Algebra.FiniteType K S] (x : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (frobeniusLiftExterior y hy π hπ p F hF hker x) = 0 := by
  induction x using kaehlerExterior_mul_induction with
  | h1 => rw [frobeniusLiftExterior_one, kaehlerDeRhamDiff_one]
  | hsmul f ω h =>
    rw [frobeniusLiftExterior_smul, kaehlerDeRhamDiff_smul, h, smul_zero, add_zero,
      kaehlerD_pow_char, map_zero, zero_mul]
  | hD g ω h =>
    rw [frobeniusLiftExterior_mul, frobeniusLiftExterior_ι_D y hy π hπ p F hF hker hann hp2 hK]
    have h2 := kaehlerDeRhamDiff_one_form_mul y hy (frobeniusLiftOneForm K π hπ p F hF hker g)
      (frobeniusLiftExterior y hy π hπ p F hF hker ω)
    rw [h, mul_zero, zero_add, frobeniusLiftOneForm_closed y hy π hπ p F hF hker, zero_mul] at h2
    exact h2
  | hadd ω ω' h h' => rw [frobeniusLiftExterior_add, map_add, h, h', add_zero]
  | h0 =>
    have := frobeniusLiftExterior_add y hy π hπ p F hF hker 0 0
    rw [add_zero, left_eq_add] at this
    rw [this, map_zero]

include hann hp2 hK in
/-- **The Deligne–Illusie map agrees with the inverse Cartier operator up to exact forms.** -/
theorem frobeniusLiftExterior_sub_inverseCartier_mem_range [Algebra.FiniteType K S] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (x : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker x - kaehlerInverseCartier y hy p x ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) :=
  cartier_comparison y hy p _ _ (frobeniusLiftExterior_one y hy π hπ p F hF hker)
    (kaehlerInverseCartier_one y hy p) (frobeniusLiftExterior_add y hy π hπ p F hF hker)
    (kaehlerInverseCartier_add y hy p) (frobeniusLiftExterior_smul y hy π hπ p F hF hker)
    (kaehlerInverseCartier_smul y hy p) (frobeniusLiftExterior_mul y hy π hπ p F hF hker)
    (kaehlerInverseCartier_mul y hy p)
    (frobeniusLiftExterior_closed y hy π hπ p F hF hker hann hp2 hK)
    (fun g => ⟨_, kaehlerInverseCartier_ι y hy p _, by
      rw [← kaehlerInverseCartier_ι]; exact kaehlerInverseCartier_closed y hy p hy0 _⟩)
    (fun g => by
      rw [frobeniusLiftExterior_ι_D y hy π hπ p F hF hker hann hp2 hK]
      exact frobeniusLiftOneForm_sub_inverseCartier_mem_range y hy π hπ p F hF hker g) x

include hann hp2 hK in
/-- **The Deligne–Illusie map of a Frobenius lift is a quasi-isomorphism on an étale chart**: over a
perfect field, for a domain with nonzero coordinates, every cocycle is `Φ_F(ω)` plus a coboundary
for a unique form `ω`. -/
theorem frobeniusLift_cartier_isomorphism [PerfectRing K p] [Algebra.FiniteType K S] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (z : ExteriorAlgebra S Ω[S⁄K])
    (hz : kaehlerDeRhamDiff y hy z = 0) :
    ∃! ω : ExteriorAlgebra S Ω[S⁄K],
      z - frobeniusLiftExterior y hy π hπ p F hF hker ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
  have hcomp := frobeniusLiftExterior_sub_inverseCartier_mem_range y hy π hπ p F hF hker hann hp2 hK hy0
  have hiff : ∀ ω, z - frobeniusLiftExterior y hy π hπ p F hF hker ω ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) ↔
      z - kaehlerInverseCartier y hy p ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
    intro ω
    have hrel : z - kaehlerInverseCartier y hy p ω = (z - frobeniusLiftExterior y hy π hπ p F hF hker ω) +
        (frobeniusLiftExterior y hy π hπ p F hF hker ω - kaehlerInverseCartier y hy p ω) := by abel
    constructor
    · intro h
      rw [hrel]
      exact Submodule.add_mem _ h (hcomp ω)
    · intro h
      have h2 : z - frobeniusLiftExterior y hy π hπ p F hF hker ω = (z - kaehlerInverseCartier y hy p ω) -
          (frobeniusLiftExterior y hy π hπ p F hF hker ω - kaehlerInverseCartier y hy p ω) := by abel
      rw [h2]
      exact Submodule.sub_mem _ h (hcomp ω)
  obtain ⟨ω, hω, huniq⟩ := kaehler_cartier_isomorphism y hy p hy0 z hz
  exact ⟨ω, (hiff ω).mpr hω, fun ω' h => huniq ω' ((hiff ω').mp h)⟩

end Extension

end MixedFujita
