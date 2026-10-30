/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierCoordinateIndependence

/-!
Frobenius lifts modulo `p²` and the Deligne–Illusie map in degree one (step 10).

Let `π : L → S` be a lift of `S` modulo `p²`: `π` is surjective with kernel `pL`, `p² = 0` in `L`,
and `p z = 0` forces `π z = 0` (flatness over `ℤ/p²`). Let `F : L → L` be a ring endomorphism lifting
the Frobenius, `π(F x) = π(x)^p`. For `x ∈ L` write `F x - x^p = p w` and put `δ x = π w`
(`frobeniusLiftDefect`; independent of `w`). Then
* `δ(x + y) = δ x + δ y - P(π x, π y)` with `P = ((a+b)^p - a^p - b^p)/p` (`frobeniusLiftDefect_add`),
* `δ(x y) = π(x)^p δ y + π(y)^p δ x` (`frobeniusLiftDefect_mul`),
* `δ(x + p z) = δ x + π(z)^p` (`frobeniusLiftDefect_add_p_mul`).
Hence `dδ` only depends on `π x`, and
`φ(a) = a^{p-1} da + d δ(ã)` (`ã` any lift of `a`; `frobeniusLiftOneForm`)
is additive (by the Frobenius defect identity of check-404), satisfies
`φ(ab) = a^p φ(b) + b^p φ(a)`, and vanishes on `K` when the elements of `K` have Frobenius-fixed
lifts. This is the map `F^*/p` of Deligne–Illusie. On an étale chart its values are closed
(`frobeniusLiftOneForm_closed`) and it agrees with the inverse Cartier operator up to an exact form
(`frobeniusLiftOneForm_sub_inverseCartier_mem_range`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Binomial

/-- `(x + y)^{q+1} = x^{q+1} + y^{q+1} + (q+1) P(x, y)` in every commutative ring, `q + 1` prime. -/
theorem add_pow_eq_frobeniusDefect {A : Type*} [CommRing A] {q : ℕ} (hp : (q + 1).Prime) (x y : A) :
    (x + y) ^ (q + 1) = x ^ (q + 1) + y ^ (q + 1) + ((q + 1 : ℕ) : A) * frobeniusDefect q x y := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ', frobeniusDefect, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range q, x ^ (k + 1) * y ^ (q + 1 - (k + 1)) * ((q + 1).choose (k + 1) : A) =
      ((q + 1 : ℕ) : A) * ((((q + 1).choose (k + 1) / (q + 1) : ℕ) : A) * (x ^ (k + 1) * y ^ (q - k))) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hdvd : q + 1 ∣ (q + 1).choose (k + 1) := hp.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
    have hc : ((q + 1).choose (k + 1) : A) =
        ((q + 1 : ℕ) : A) * (((q + 1).choose (k + 1) / (q + 1) : ℕ) : A) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    rw [show q + 1 - (k + 1) = q - k by omega, hc]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [pow_zero, one_mul, mul_one, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, Nat.sub_self]
  ring

theorem frobeniusDefect_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℕ) (x y : A) :
    f (frobeniusDefect q x y) = frobeniusDefect q (f x) (f y) := by
  simp only [frobeniusDefect, map_sum, map_mul, map_natCast, map_pow]

theorem frobeniusDefect_zero_right {A : Type*} [CommRing A] (q : ℕ) (x : A) :
    frobeniusDefect q x 0 = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [zero_pow (by have := Finset.mem_range.mp hk; omega), mul_zero, mul_zero]

end Binomial

section Lift

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

include hF in
theorem frobeniusLift_sub_mem (x : L) : π (F x - x ^ p) = 0 := by
  rw [map_sub, hF, map_pow, sub_self]

/-- The Frobenius defect `δ x = π((F x - x^p)/p)` of a Frobenius lift modulo `p²`. -/
noncomputable def frobeniusLiftDefect (x : L) : S :=
  π (Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x)))

theorem frobeniusLiftDefect_spec (x : L) :
    F x - x ^ p = (p : L) * Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x)) :=
  Classical.choose_spec (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x))

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0)

include hann in
theorem frobeniusLiftDefect_eq {x z : L} (h : F x - x ^ p = (p : L) * z) :
    frobeniusLiftDefect π p F hF hker x = π z := by
  have h2 := frobeniusLiftDefect_spec π p F hF hker x
  have h3 : (p : L) * (Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x)) - z) = 0 := by
    rw [mul_sub, ← h2, ← h, sub_self]
  have h4 := hann _ h3
  rw [map_sub, sub_eq_zero] at h4
  exact h4

variable [hp : Fact p.Prime] (hp2 : (p : L) * p = 0)

omit hp in
include hp2 in
theorem natCast_pow_eq_zero_of_two_le {m : ℕ} (hm : 2 ≤ m) : ((p : L)) ^ m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [pow_add, pow_two, hp2, mul_zero]

include hann in
theorem frobeniusLiftDefect_add (x y : L) :
    frobeniusLiftDefect π p F hF hker (x + y) = frobeniusLiftDefect π p F hF hker x +
      frobeniusLiftDefect π p F hF hker y - frobeniusDefect (p - 1) (π x) (π y) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
  set wx := Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x))
  set wy := Classical.choose (hker (F y - y ^ p) (frobeniusLift_sub_mem π p F hF y))
  have hx := frobeniusLiftDefect_spec π p F hF hker x
  have hy := frobeniusLiftDefect_spec π p F hF hker y
  have hbin := add_pow_eq_frobeniusDefect (hq ▸ hp.out) x y
  rw [← hq] at hbin
  have hsum : F (x + y) - (x + y) ^ p = (p : L) * (wx + wy - frobeniusDefect q x y) := by
    rw [map_add, hbin, mul_sub, mul_add, ← hx, ← hy]
    ring
  have hq1 : p - 1 = q := by omega
  rw [frobeniusLiftDefect_eq π p F hF hker hann hsum, map_sub, map_add, frobeniusDefect_map, hq1]
  rfl

omit hp in
include hann hp2 in
theorem frobeniusLiftDefect_mul (x y : L) :
    frobeniusLiftDefect π p F hF hker (x * y) = π x ^ p * frobeniusLiftDefect π p F hF hker y +
      π y ^ p * frobeniusLiftDefect π p F hF hker x := by
  set wx := Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x))
  set wy := Classical.choose (hker (F y - y ^ p) (frobeniusLift_sub_mem π p F hF y))
  have hx := frobeniusLiftDefect_spec π p F hF hker x
  have hy := frobeniusLiftDefect_spec π p F hF hker y
  have hFx : F x = x ^ p + (p : L) * wx := by rw [← hx]; ring
  have hFy : F y = y ^ p + (p : L) * wy := by rw [← hy]; ring
  have hprod : F (x * y) - (x * y) ^ p = (p : L) * (x ^ p * wy + y ^ p * wx) := by
    rw [map_mul, hFx, hFy, mul_pow]
    linear_combination (wx * wy) * hp2
  rw [frobeniusLiftDefect_eq π p F hF hker hann hprod, map_add, map_mul, map_mul, map_pow, map_pow]
  rfl

include hann hp2 in
theorem frobeniusLiftDefect_p_mul (z : L) :
    frobeniusLiftDefect π p F hF hker ((p : L) * z) = π z ^ p := by
  have h : F ((p : L) * z) - ((p : L) * z) ^ p = (p : L) * F z := by
    rw [map_mul, map_natCast, mul_pow, natCast_pow_eq_zero_of_two_le p hp2 hp.out.two_le, zero_mul,
      sub_zero]
  rw [frobeniusLiftDefect_eq π p F hF hker hann h, hF]

variable (hpS : (p : S) = 0)

include hann hp2 hpS in
theorem frobeniusLiftDefect_add_p_mul (x z : L) :
    frobeniusLiftDefect π p F hF hker (x + (p : L) * z) =
      frobeniusLiftDefect π p F hF hker x + π z ^ p := by
  rw [frobeniusLiftDefect_add π p F hF hker hann, frobeniusLiftDefect_p_mul π p F hF hker hann hp2,
    map_mul, map_natCast, hpS, zero_mul, frobeniusDefect_zero_right, sub_zero]

end Lift

section OneForm

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {L : Type w} [CommRing L]
  (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

omit hp in
theorem kaehlerD_pow_char (a : S) : KaehlerDifferential.D K S (a ^ p) = 0 := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, hpS, zero_smul]

include hann hp2 in
/-- `dδ(x)` only depends on `π x`. -/
theorem D_frobeniusLiftDefect_eq {x x' : L} (h : π x = π x') :
    KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker x) =
      KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker x') := by
  obtain ⟨z, hz⟩ := hker (x' - x) (by rw [map_sub, h, sub_self])
  have hx' : x' = x + (p : L) * z := by rw [← hz]; ring
  rw [hx', frobeniusLiftDefect_add_p_mul π p F hF hker hann hp2
    (natCast_char_eq_zero_of_algebra (K := K) p), map_add, kaehlerD_pow_char, add_zero]

variable (K) in
/-- **The Deligne–Illusie map in degree one**: `φ(a) = a^{p-1} da + d δ(ã)`. -/
noncomputable def frobeniusLiftOneForm (a : S) : Ω[S⁄K] :=
  a ^ (p - 1) • KaehlerDifferential.D K S a +
    KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker (Function.surjInv hπ a))

include hann hp2 in
theorem frobeniusLiftOneForm_lift (x : L) :
    frobeniusLiftOneForm K π hπ p F hF hker (π x) = π x ^ (p - 1) • KaehlerDifferential.D K S (π x) +
      KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker x) := by
  rw [frobeniusLiftOneForm, D_frobeniusLiftDefect_eq π p F hF hker hann hp2
    (Function.surjInv_eq hπ (π x))]

include hann hp2 in
theorem frobeniusLiftOneForm_add (a b : S) :
    frobeniusLiftOneForm K π hπ p F hF hker (a + b) =
      frobeniusLiftOneForm K π hπ p F hF hker a + frobeniusLiftOneForm K π hπ p F hF hker b := by
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ b
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
  have hq1 : p - 1 = q := by omega
  have hdef := derivation_frobeniusDefect (KaehlerDifferential.D K S) (hq ▸ hp.out) (π x) (π y)
  rw [← map_add, frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2,
    frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2, frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2,
    frobeniusLiftDefect_add π p F hF hker hann, map_add, map_sub, map_add, map_add, hq1, hdef]
  module

include hann hp2 in
theorem frobeniusLiftOneForm_mul (a b : S) :
    frobeniusLiftOneForm K π hπ p F hF hker (a * b) =
      a ^ p • frobeniusLiftOneForm K π hπ p F hF hker b + b ^ p • frobeniusLiftOneForm K π hπ p F hF hker a := by
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ b
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
  have hq1 : p - 1 = q := by omega
  have hDp : ∀ (c d : S), KaehlerDifferential.D K S (c ^ p * d) = c ^ p • KaehlerDifferential.D K S d :=
    fun c d => by rw [Derivation.leibniz, kaehlerD_pow_char, smul_zero, add_zero]
  rw [← map_mul, frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2,
    frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2, frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2,
    frobeniusLiftDefect_mul π p F hF hker hann hp2, map_add, hDp, hDp, map_mul, Derivation.leibniz, hq1]
  generalize KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker x) = Dx
  generalize KaehlerDifferential.D K S (frobeniusLiftDefect π p F hF hker y) = Dy
  rw [hq]
  module

include hann hp2 in
/-- `φ` vanishes on `K` when the elements of `K` have Frobenius-fixed lifts. -/
theorem frobeniusLiftOneForm_algebraMap
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p) (c : K) :
    frobeniusLiftOneForm K π hπ p F hF hker (algebraMap K S c) = 0 := by
  obtain ⟨c', hc', hFc'⟩ := hK c
  have hδ : frobeniusLiftDefect π p F hF hker c' = 0 := by
    have h : F c' - c' ^ p = (p : L) * 0 := by rw [hFc', sub_self, mul_zero]
    rw [frobeniusLiftDefect_eq π p F hF hker hann h, map_zero]
  rw [← hc', frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2, hδ, map_zero, add_zero, hc',
    Derivation.map_algebraMap, smul_zero]

end OneForm

section Chart

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L]
  (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

theorem kaehlerDeRhamDiff_ι_D (g : S) :
    kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) = 0 := by
  have := kaehlerDeRhamDiff_exact_mul y hy g 1
  rwa [mul_one, kaehlerDeRhamDiff_one, mul_zero, neg_zero] at this

theorem ι_D_mem_range (g : S) :
    ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
  refine ⟨g • 1, ?_⟩
  rw [kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_one, smul_zero, add_zero, mul_one]

omit hp [CharP K p] in
/-- The values of `φ` are closed `1`-forms. -/
theorem frobeniusLiftOneForm_closed (a : S) :
    kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S (frobeniusLiftOneForm K π hπ p F hF hker a)) = 0 := by
  rw [frobeniusLiftOneForm, map_add, map_add, map_smul, kaehlerDeRhamDiff_ι_D y hy, add_zero,
    kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_ι_D y hy, smul_zero, add_zero, Derivation.leibniz_pow,
    map_nsmul, map_smul, nsmul_eq_mul, mul_assoc, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero,
    smul_zero, mul_zero]

/-- **On an étale chart, `φ(a)` is the inverse Cartier image of `da` up to an exact form.** -/
theorem frobeniusLiftOneForm_sub_inverseCartier_mem_range [Algebra.FiniteType K S] (a : S) :
    ExteriorAlgebra.ι S (frobeniusLiftOneForm K π hπ p F hF hker a) -
        kaehlerInverseCartier y hy p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S a)) ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) := by
  have h1 := kaehlerInverseCartier_D_sub_mem_range y hy p a
  have h2 := ι_D_mem_range y hy (frobeniusLiftDefect π p F hF hker (Function.surjInv hπ a))
  have h := Submodule.sub_mem _ h2 h1
  rw [frobeniusLiftOneForm, map_add, map_smul]
  convert h using 1
  abel

end Chart

end MixedFujita
