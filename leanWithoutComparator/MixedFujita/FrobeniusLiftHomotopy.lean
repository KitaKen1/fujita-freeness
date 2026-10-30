/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftDecomposition

/-!
The homotopy between two Frobenius lifts (step 10, the gluing data of Deligne–Illusie).

Let `π : L → S` be a lift modulo `p²` (check-407) and `F₁, F₂` two Frobenius lifts on the same `L`.
For `x ∈ L` write `F₂ x - F₁ x = p w` and put `h̃ x = π w` (`frobeniusLiftDifference`). Then
* `h̃ = δ₂ - δ₁` (`frobeniusLiftDifference_eq_sub`),
* `h̃(x + p z) = h̃ x`, so `h̃` descends to `h : S → S` (`frobeniusLiftHomotopy`),
* `h` is additive and `h(a b) = a^p h(b) + b^p h(a)`: an honest Frobenius-semilinear derivation
  (no correction term, unlike `δ`),
* `φ₂(a) - φ₁(a) = d h(a)` (`frobeniusLiftOneForm_sub_eq_D_homotopy`).
On an étale chart `h` satisfies the chain rule `h(a) = Σ_j (∂_j a)^p h(y_j)`
(`frobeniusLiftHomotopyAux_D`), so it is a Frobenius-semilinear map `h' : Ω¹ → S` with
`d ∘ h' = φ₂' - φ₁'` on `1`-forms (`D_frobeniusLiftHomotopyAux`). These are the homotopies `h_{αβ}`
of Deligne–Illusie: on a cover with Frobenius lifts `F_α` of one global lift they satisfy
`h_{αβ} + h_{βγ} = h_{αγ}` because `h̃_{αβ} = δ_β - δ_α`.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Difference

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

include hF₁ hF₂ in
theorem frobeniusLift_sub_lift_mem (x : L) : π (F₂ x - F₁ x) = 0 := by
  rw [map_sub, hF₁, hF₂, sub_self]

/-- `h̃ x = π((F₂ x - F₁ x)/p)`. -/
noncomputable def frobeniusLiftDifference (x : L) : S :=
  π (Classical.choose (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x)))

theorem frobeniusLiftDifference_spec (x : L) :
    F₂ x - F₁ x = (p : L) *
      Classical.choose (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x)) :=
  Classical.choose_spec (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x))

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0)

include hann in
theorem frobeniusLiftDifference_eq {x z : L} (h : F₂ x - F₁ x = (p : L) * z) :
    frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x = π z := by
  have h2 := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker x
  have h3 : (p : L) * (Classical.choose (hker (F₂ x - F₁ x)
      (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x)) - z) = 0 := by
    rw [mul_sub, ← h2, ← h, sub_self]
  have h4 := hann _ h3
  rw [map_sub, sub_eq_zero] at h4
  exact h4

include hann in
theorem frobeniusLiftDifference_eq_sub (x : L) :
    frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x =
      frobeniusLiftDefect π p F₂ hF₂ hker x - frobeniusLiftDefect π p F₁ hF₁ hker x := by
  have h1 := frobeniusLiftDefect_spec π p F₁ hF₁ hker x
  have h2 := frobeniusLiftDefect_spec π p F₂ hF₂ hker x
  have h : F₂ x - F₁ x = (p : L) * (Classical.choose (hker (F₂ x - x ^ p)
      (frobeniusLift_sub_mem π p F₂ hF₂ x)) - Classical.choose (hker (F₁ x - x ^ p)
      (frobeniusLift_sub_mem π p F₁ hF₁ x))) := by
    rw [mul_sub, ← h1, ← h2]
    ring
  rw [frobeniusLiftDifference_eq π p F₁ F₂ hF₁ hF₂ hker hann h, map_sub]
  rfl

include hann in
theorem frobeniusLiftDifference_add (x y : L) :
    frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker (x + y) =
      frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x + frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker y := by
  have hx := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker x
  have hy := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker y
  have h : F₂ (x + y) - F₁ (x + y) = (p : L) * (Classical.choose (hker (F₂ x - F₁ x)
      (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x)) + Classical.choose (hker (F₂ y - F₁ y)
      (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ y))) := by
    rw [mul_add, ← hx, ← hy, map_add, map_add]
    ring
  rw [frobeniusLiftDifference_eq π p F₁ F₂ hF₁ hF₂ hker hann h, map_add]
  rfl

include hann in
theorem frobeniusLiftDifference_mul (x y : L) :
    frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker (x * y) =
      π x ^ p * frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker y +
        π y ^ p * frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x := by
  have hx := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker x
  have hy := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker y
  set wx := Classical.choose (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x))
  set wy := Classical.choose (hker (F₂ y - F₁ y) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ y))
  have h : F₂ (x * y) - F₁ (x * y) = (p : L) * (F₂ x * wy + F₁ y * wx) := by
    rw [map_mul, map_mul]
    linear_combination F₂ x * hy + F₁ y * hx
  rw [frobeniusLiftDifference_eq π p F₁ F₂ hF₁ hF₂ hker hann h, map_add, map_mul, map_mul, hF₂, hF₁]
  rfl

include hann in
theorem frobeniusLiftDifference_add_p_mul (x z : L) :
    frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker (x + (p : L) * z) =
      frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x := by
  rw [frobeniusLiftDifference_add π p F₁ F₂ hF₁ hF₂ hker hann]
  have h : F₂ ((p : L) * z) - F₁ ((p : L) * z) = (p : L) * (F₂ z - F₁ z) := by
    rw [map_mul, map_mul, map_natCast, map_natCast, mul_sub]
  rw [frobeniusLiftDifference_eq π p F₁ F₂ hF₁ hF₂ hker hann h, map_sub, hF₁, hF₂, sub_self, add_zero]

end Difference

section Homotopy

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {L : Type w} [CommRing L]
  (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

/-- **The homotopy** `h : S → S`, `h(π x) = π((F₂ x - F₁ x)/p)`. -/
noncomputable def frobeniusLiftHomotopy (a : S) : S :=
  frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker (Function.surjInv hπ a)

omit hp [CharP K p] in
include hann in
theorem frobeniusLiftHomotopy_lift (x : L) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (π x) =
      frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x := by
  obtain ⟨z, hz⟩ := hker (x - Function.surjInv hπ (π x)) (by rw [map_sub, Function.surjInv_eq hπ (π x), sub_self])
  have hx : x = Function.surjInv hπ (π x) + (p : L) * z := by rw [← hz]; ring
  rw [frobeniusLiftHomotopy]
  conv_rhs => rw [hx]
  rw [frobeniusLiftDifference_add_p_mul π p F₁ F₂ hF₁ hF₂ hker hann]

omit hp [CharP K p] in
include hann in
theorem frobeniusLiftHomotopy_add (a b : S) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (a + b) =
      frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a + frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker b := by
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ b
  rw [← map_add, frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_add π p F₁ F₂ hF₁ hF₂ hker hann]

omit hp [CharP K p] in
include hann in
/-- `h` is a Frobenius-semilinear derivation. -/
theorem frobeniusLiftHomotopy_mul (a b : S) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (a * b) =
      a ^ p * frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker b +
        b ^ p * frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a := by
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ b
  rw [← map_mul, frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_mul π p F₁ F₂ hF₁ hF₂ hker hann]

omit hp [CharP K p] in
include hann in
theorem frobeniusLiftHomotopy_algebraMap
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F₁ c' = c' ^ p ∧ F₂ c' = c' ^ p) (c : K) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (algebraMap K S c) = 0 := by
  obtain ⟨c', hc', h1, h2⟩ := hK c
  have h : F₂ c' - F₁ c' = (p : L) * 0 := by rw [h1, h2, sub_self, mul_zero]
  rw [← hc', frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_eq π p F₁ F₂ hF₁ hF₂ hker hann h, map_zero]

include hann hp2 in
/-- **`φ₂ - φ₁ = d h`.** -/
theorem frobeniusLiftOneForm_sub_eq_D_homotopy (a : S) :
    frobeniusLiftOneForm K π hπ p F₂ hF₂ hker a - frobeniusLiftOneForm K π hπ p F₁ hF₁ hker a =
      KaehlerDifferential.D K S (frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a) := by
  obtain ⟨x, rfl⟩ := hπ a
  rw [frobeniusLiftOneForm_lift π hπ p F₂ hF₂ hker hann hp2,
    frobeniusLiftOneForm_lift π hπ p F₁ hF₁ hker hann hp2,
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_eq_sub π p F₁ F₂ hF₁ hF₂ hker hann, map_sub]
  abel

end Homotopy

section Chart

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0)
  (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F₁ c' = c' ^ p ∧ F₂ c' = c' ^ p)

include hann hK in
/-- `h` vanishes on `K·S^p`. -/
theorem frobeniusLiftHomotopy_eq_zero_of_mem {c : S} (hc : c ∈ frobeniusSubalgebra K S p) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker c = 0 := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  have hpow : ∀ (a : S) (m : ℕ), frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (a ^ (m + 1)) =
      ((m + 1 : ℕ) : S) * (a ^ p) ^ m * frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a := by
    intro a m
    induction m with
    | zero => rw [zero_add, pow_one, pow_zero, Nat.cast_one, one_mul, one_mul]
    | succ m ih =>
      rw [pow_succ, frobeniusLiftHomotopy_mul π hπ p F₁ F₂ hF₁ hF₂ hker hann, ih,
        show (a ^ (m + 1)) ^ p = (a ^ p) ^ (m + 1) by rw [← pow_mul, ← pow_mul, mul_comm]]
      push_cast
      ring
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    have h := hpow a q
    rw [← hq, hpS, zero_mul, zero_mul] at h
    exact h
  | algebraMap c => exact frobeniusLiftHomotopy_algebraMap π hπ p F₁ F₂ hF₁ hF₂ hker hann hK c
  | add x z _ _ hx hz => rw [frobeniusLiftHomotopy_add π hπ p F₁ F₂ hF₁ hF₂ hker hann, hx, hz, add_zero]
  | mul x z _ _ hx hz =>
    rw [frobeniusLiftHomotopy_mul π hπ p F₁ F₂ hF₁ hF₂ hker hann, hx, hz, mul_zero, mul_zero, add_zero]

/-- The homotopy on `1`-forms through the étale basis: `Σ_j ω_j dy_j ↦ Σ_j ω_j^p h(y_j)`. -/
noncomputable def frobeniusLiftHomotopyAux (ω : Ω[S⁄K]) : S :=
  ∑ j, (etaleCoordinateBasis y hy).repr ω j ^ p *
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (etaleCoordFun y j)

theorem frobeniusLiftHomotopyAux_add (ω η : Ω[S⁄K]) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker (ω + η) =
      frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω +
        frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [frobeniusLiftHomotopyAux, map_add, Finsupp.add_apply,
    add_pow_prime_of_natCast_eq_zero hp.out hpS, add_mul, Finset.sum_add_distrib]

omit hp [CharP K p] in
theorem frobeniusLiftHomotopyAux_smul (c : S) (ω : Ω[S⁄K]) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker (c • ω) =
      c ^ p * frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω := by
  simp only [frobeniusLiftHomotopyAux, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum, mul_assoc]

omit [CharP K p] in
theorem frobeniusLiftHomotopyAux_coordinate (i : Fin n) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker
        (KaehlerDifferential.D K S (etaleCoordFun y i)) =
      frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (etaleCoordFun y i) := by
  classical
  have hb : KaehlerDifferential.D K S (etaleCoordFun y i) = etaleCoordinateBasis y hy i :=
    (etaleCoordinateBasis_apply y hy i).symm
  rw [frobeniusLiftHomotopyAux, hb, Finset.sum_eq_single i]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_pow, one_mul]
  · intro j _ hji
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne' hji.symm,
      zero_pow (Fact.out : p.Prime).ne_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

include hann hK in
/-- **Chain rule** `h(a) = Σ_j (∂_j a)^p h(y_j)`. -/
theorem frobeniusLiftHomotopyAux_D [Algebra.FiniteType K S] (a : S) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker (KaehlerDifferential.D K S a) =
      frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a := by
  obtain ⟨q, hq⟩ := exists_aeval_frobeniusSubalgebra_eq p y hy a
  have hq' : MvPolynomial.aeval (etaleCoordFun y) q = a := hq
  rw [← hq']
  clear hq hq'
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C]
    have hD : KaehlerDifferential.D K S (algebraMap (frobeniusSubalgebra K S p) S c) = 0 :=
      derivation_eq_zero_of_mem_frobeniusSubalgebra p (KaehlerDifferential.D K S) c.2
    have hh : frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker
        (algebraMap (frobeniusSubalgebra K S p) S c) = 0 :=
      frobeniusLiftHomotopy_eq_zero_of_mem π hπ p F₁ F₂ hF₁ hF₂ hker hann hK c.2
    rw [hD, hh]
    have := frobeniusLiftHomotopyAux_smul y hy π hπ p F₁ F₂ hF₁ hF₂ hker 0 0
    rwa [zero_smul, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul] at this
  | add a b ha hb =>
    rw [map_add, map_add, frobeniusLiftHomotopyAux_add, ha, hb,
      frobeniusLiftHomotopy_add π hπ p F₁ F₂ hF₁ hF₂ hker hann]
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, frobeniusLiftHomotopyAux_add,
      frobeniusLiftHomotopyAux_smul, frobeniusLiftHomotopyAux_smul, ha,
      frobeniusLiftHomotopyAux_coordinate, frobeniusLiftHomotopy_mul π hπ p F₁ F₂ hF₁ hF₂ hker hann,
      add_comm]

variable (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **The homotopy on `1`-forms**: `d(h'(ω)) = φ₂'(ω) - φ₁'(ω)`. -/
theorem D_frobeniusLiftHomotopyAux (ω : Ω[S⁄K]) :
    KaehlerDifferential.D K S (frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω) =
      frobeniusLiftOneFormAux y hy π hπ p F₂ hF₂ hker ω - frobeniusLiftOneFormAux y hy π hπ p F₁ hF₁ hker ω := by
  rw [frobeniusLiftHomotopyAux, frobeniusLiftOneFormAux, frobeniusLiftOneFormAux, map_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, kaehlerD_pow_char, smul_zero, add_zero, ← smul_sub,
    frobeniusLiftOneForm_sub_eq_D_homotopy π hπ p F₁ F₂ hF₁ hF₂ hker hann hp2]

end Chart

end MixedFujita
