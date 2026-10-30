/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalAdicOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
The order along a coordinate divisor is a monomial test valuation (step 6). Let R be a Noetherian
local domain, such as the local ring of a smooth variety at a point p, and h a prime element, the
local equation of a prime divisor E through p; the local ring of E is the localization S of R at
(h). For f in R the order of f in S is the largest k with h^k ∣ f in R: if s f = h^k g with
s ∉ (h), then h^k divides f, since h is prime. The completion of R is faithfully flat over R, so
h^k ∣ f in R exactly when it holds in the completion. If completion coordinates send h to the
variable X_i, as in a chart in which E is the coordinate hyperplane {y_i = 0}, then h^k ∣ f means
X_i^k divides the Taylor expansion of f, that is, its weighted order for the weight 1 on X_i and 0
on the other variables is at least k. Hence ord_E(f) is the monomial test valuation with weight
e_i: divisorial valuations of coordinate divisors are test valuations, and A(ord_E) = 1 + v(det J).
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

section PowerSeries

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- The weight with 1 on X_i and 0 on the other variables. -/
theorem weight_piSingle_one (i : σ) (d : σ →₀ ℕ) :
    Finsupp.weight (Pi.single i 1 : σ → ℕ) d = d i := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp [Finsupp.notMem_support_iff.mp hi]

/-- The monomial valuation with weight e_i is the X_i-adic order. -/
theorem natCast_le_weightedOrder_piSingle_iff (i : σ) (F : MvPowerSeries σ K) (k : ℕ) :
    (k : ℕ∞) ≤ F.weightedOrder (Pi.single i 1) ↔ (X i : MvPowerSeries σ K) ^ k ∣ F := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_weightedOrder
    rw [weight_piSingle_one]
    exact lt_of_lt_of_le (by exact_mod_cast hd) h
  · intro h
    apply le_weightedOrder
    intro d hd
    rw [weight_piSingle_one] at hd
    exact h d (by exact_mod_cast hd)

end PowerSeries

section Completion

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Divisibility is detected in the completion: the completion is faithfully flat. -/
theorem pow_dvd_iff_completion (h r : R) (k : ℕ) :
    h ^ k ∣ r ↔ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) h) ^ k ∣
      algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r := by
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨algebraMap R _ c, by rw [map_mul, map_pow]⟩
  · intro hd
    have hmem : r ∈ ((Ideal.span {h ^ k}).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := by
      rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, map_pow]
      exact hd
    rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton] at hmem
    exact hmem

end Completion

section Localization

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If h is prime, s ∉ (h) and s f = h^k g, then h^k ∣ f. -/
theorem pow_dvd_of_mul_eq_of_prime {h : R} (hp : Prime h) {s : R} (hs : ¬h ∣ s) :
    ∀ (k : ℕ) {f g : R}, s * f = h ^ k * g → h ^ k ∣ f := by
  intro k
  induction k with
  | zero => intro f g _; simp
  | succ k ih =>
    intro f g hfg
    have hdvd : h ∣ s * f := ⟨h ^ k * g, by rw [hfg]; ring⟩
    obtain ⟨f', rfl⟩ := (hp.dvd_or_dvd hdvd).resolve_left hs
    have h' : s * f' = h ^ k * g := by
      apply mul_left_cancel₀ hp.ne_zero
      calc h * (s * f') = s * (h * f') := by ring
        _ = h ^ (k + 1) * g := hfg
        _ = h * (h ^ k * g) := by ring
    obtain ⟨c, hc⟩ := ih h'
    exact ⟨c, by rw [hc]; ring⟩

/-- In the localization at the prime (h), a function lies in the k-th power of the maximal ideal
exactly when h^k divides it in R. -/
theorem algebraMap_mem_maximalIdeal_pow_iff {h : R} (hp : Prime h) [(Ideal.span {h}).IsPrime]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {h})]
    [IsLocalRing S] (f : R) (k : ℕ) :
    algebraMap R S f ∈ IsLocalRing.maximalIdeal S ^ k ↔ h ^ k ∣ f := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {h}) S, ← Ideal.map_pow,
    Ideal.span_singleton_pow,
    IsLocalization.mem_map_algebraMap_iff (Ideal.span {h}).primeCompl S]
  constructor
  · rintro ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hsa⟩
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have hinj := IsLocalization.injective S
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {h}))
    have heq : f * s = h ^ k * g := by
      apply hinj
      rw [map_mul]
      exact hsa
    have hs' : ¬h ∣ s := fun hd => hs (Ideal.mem_span_singleton.mpr hd)
    exact pow_dvd_of_mul_eq_of_prime hp hs' k (by rw [mul_comm]; exact heq)
  · intro hd
    exact ⟨⟨⟨f, Ideal.mem_span_singleton.mpr hd⟩, 1⟩, by simp⟩

end Localization

section Valuation

variable {σ K R : Type*} [Field K] [DecidableEq σ] [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [Algebra K R]

/-- The order along the coordinate divisor (h) is the monomial test valuation with weight e_i:
if completion coordinates send the prime element h to X_i, then for f in R the order of f in the
local ring of (h) is the weighted order of the Taylor expansion of f with weight 1 on X_i. -/
theorem localAdicOrder_localization_eq_weightedOrder
    (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃ₐ[K] MvPowerSeries σ K) {h : R}
    (hp : Prime h) (i : σ)
    (he : e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) h) = X i)
    [(Ideal.span {h}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {h})] [IsLocalRing S] (f : R) :
    localAdicOrder S (algebraMap R S f) =
      (e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) f)).weightedOrder
        (Pi.single i 1) := by
  have key : ∀ k : ℕ, ((k : ℕ∞) ≤ localAdicOrder S (algebraMap R S f) ↔
      (k : ℕ∞) ≤ (e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) f)).weightedOrder
        (Pi.single i 1)) := by
    intro k
    rw [localAdicOrder_nat_le_iff, algebraMap_mem_maximalIdeal_pow_iff hp S f k,
      natCast_le_weightedOrder_piSingle_iff, pow_dvd_iff_completion h f k, ← he, ← map_pow e]
    exact (map_dvd_iff e).symm
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun k hk => (key k).mp hk)
    (ENat.forall_natCast_le_iff_le.mp fun k hk => (key k).mpr hk)

end Valuation

end MixedFujita
