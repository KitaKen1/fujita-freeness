/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftHomotopy

/-!
Naturality of the Deligne–Illusie map (step 10, restriction to the opens of a Čech cover).

Let `S → T` be a map of `K`-algebras (for instance the restriction to a smaller affine open),
`π : L → S`, `π' : L' → T` lifts modulo `p²` and `ρ̃ : L → L'` a ring map lifting `S → T`, compatible
with Frobenius lifts `F`, `F'` (`ρ̃ ∘ F = F' ∘ ρ̃`). Then
* the Frobenius defects are compatible, `δ'(ρ̃ x) = ρ(δ x)` (`frobeniusLiftDefect_map`),
* `φ'(ρ a) = ρ_*(φ(a))` on `1`-forms (`frobeniusLiftOneForm_map`),
* the Deligne–Illusie maps commute with the induced map of exterior algebras of Kähler
  differentials, `Φ_{F'} ∘ ρ_* = ρ_* ∘ Φ_F` (`frobeniusLiftExterior_map`), on étale charts,
* the homotopies of two pairs of compatible Frobenius lifts are compatible,
  `h'(ρ a) = ρ(h a)` (`frobeniusLiftHomotopy_map`).
On a Čech cover these say that the maps `φ_α` and the homotopies `h_{αβ}`, defined on `U_α` and
`U_α ∩ U_β`, restrict to the smaller intersections, so they form Čech cochains.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v v' w w'

section Defect

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  {T : Type v'} [CommRing T] {L' : Type w'} [CommRing L'] (π' : L' →+* T)
  (F' : L' →+* L') (hF' : ∀ x, π' (F' x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (ρ : S →+* T) (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = ρ (π x)) (hρF : ∀ x, ρ' (F x) = F' (ρ' x))

include hann' hρ hρF in
/-- The Frobenius defects of compatible lifts are compatible. -/
theorem frobeniusLiftDefect_map (x : L) :
    frobeniusLiftDefect π' p F' hF' hker' (ρ' x) = ρ (frobeniusLiftDefect π p F hF hker x) := by
  have hx := frobeniusLiftDefect_spec π p F hF hker x
  set w := Classical.choose (hker (F x - x ^ p) (frobeniusLift_sub_mem π p F hF x)) with hw
  have h : F' (ρ' x) - (ρ' x) ^ p = (p : L') * ρ' w := by
    have h2 := congrArg ρ' hx
    rw [map_sub, map_pow, hρF, map_mul, map_natCast] at h2
    exact h2
  rw [frobeniusLiftDefect_eq π' p F' hF' hker' hann' h, hρ]
  rfl

end Defect

section DifferenceMap

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  {T : Type v'} [CommRing T] {L' : Type w'} [CommRing L'] (π' : L' →+* T)
  (F₁' F₂' : L' →+* L') (hF₁' : ∀ x, π' (F₁' x) = π' x ^ p) (hF₂' : ∀ x, π' (F₂' x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (ρ : S →+* T) (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = ρ (π x))
  (hρF₁ : ∀ x, ρ' (F₁ x) = F₁' (ρ' x)) (hρF₂ : ∀ x, ρ' (F₂ x) = F₂' (ρ' x))

include hann' hρ hρF₁ hρF₂ in
/-- The differences of compatible pairs of Frobenius lifts are compatible. -/
theorem frobeniusLiftDifference_map (x : L) :
    frobeniusLiftDifference π' p F₁' F₂' hF₁' hF₂' hker' (ρ' x) =
      ρ (frobeniusLiftDifference π p F₁ F₂ hF₁ hF₂ hker x) := by
  have hx := frobeniusLiftDifference_spec π p F₁ F₂ hF₁ hF₂ hker x
  set w := Classical.choose (hker (F₂ x - F₁ x) (frobeniusLift_sub_lift_mem π p F₁ F₂ hF₁ hF₂ x))
    with hw
  have h : F₂' (ρ' x) - F₁' (ρ' x) = (p : L') * ρ' w := by
    have h2 := congrArg ρ' hx
    rw [map_sub, hρF₁, hρF₂, map_mul, map_natCast] at h2
    exact h2
  rw [frobeniusLiftDifference_eq π' p F₁' F₂' hF₁' hF₂' hker' hann' h, hρ]
  rfl

end DifferenceMap

section OneForm

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {T : Type v'} [CommRing T]
  [Algebra K T] [Algebra S T] [IsScalarTower K S T]
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hann : ∀ z, (p : L) * z = 0 → π z = 0)
  (hp2 : (p : L) * p = 0)
  {L' : Type w'} [CommRing L'] (π' : L' →+* T) (hπ' : Function.Surjective π')
  (F' : L' →+* L') (hF' : ∀ x, π' (F' x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (hp2' : (p : L') * p = 0)
  (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = algebraMap S T (π x)) (hρF : ∀ x, ρ' (F x) = F' (ρ' x))

include hann hp2 hann' hp2' hρ hρF in
/-- **`φ` commutes with compatible maps of lifts.** -/
theorem frobeniusLiftOneForm_map (a : S) :
    frobeniusLiftOneForm K π' hπ' p F' hF' hker' (algebraMap S T a) =
      KaehlerDifferential.map K K S T (frobeniusLiftOneForm K π hπ p F hF hker a) := by
  obtain ⟨x, rfl⟩ := hπ a
  have h1 : algebraMap S T (π x) = π' (ρ' x) := (hρ x).symm
  rw [h1, frobeniusLiftOneForm_lift π' hπ' p F' hF' hker' hann' hp2',
    frobeniusLiftOneForm_lift π hπ p F hF hker hann hp2, map_add, map_smul, KaehlerDifferential.map_D,
    KaehlerDifferential.map_D,
    frobeniusLiftDefect_map π p F hF hker π' F' hF' hker' hann' (algebraMap S T) ρ' hρ hρF, ← h1]
  have hs : (π x ^ (p - 1)) • KaehlerDifferential.D K T (algebraMap S T (π x)) =
      (algebraMap S T (π x)) ^ (p - 1) • KaehlerDifferential.D K T (algebraMap S T (π x)) := by
    rw [← map_pow (algebraMap S T), algebraMap_smul]
  rw [hs]

end OneForm

section Exterior

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {T : Type v'} [CommRing T]
  [Algebra K T] [Algebra S T] [IsScalarTower K S T] {n m : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  (z : MvPolynomial (Fin m) K →ₐ[K] T) (hz : z.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hann : ∀ z, (p : L) * z = 0 → π z = 0)
  (hp2 : (p : L) * p = 0) (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p)
  {L' : Type w'} [CommRing L'] (π' : L' →+* T) (hπ' : Function.Surjective π')
  (F' : L' →+* L') (hF' : ∀ x, π' (F' x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (hp2' : (p : L') * p = 0) (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ F' c' = c' ^ p)
  (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = algebraMap S T (π x)) (hρF : ∀ x, ρ' (F x) = F' (ρ' x))

include hann hp2 hK hann' hp2' hK' hρ hρF in
/-- **The Deligne–Illusie maps commute with restriction**: `Φ_{F'} ∘ ρ_* = ρ_* ∘ Φ_F`. -/
theorem frobeniusLiftExterior_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (x : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior z hz π' hπ' p F' hF' hker' (kaehlerExteriorMap K S T x) =
      kaehlerExteriorMap K S T (frobeniusLiftExterior y hy π hπ p F hF hker x) := by
  have hzeroS : frobeniusLiftExterior y hy π hπ p F hF hker 0 = 0 := by
    have := frobeniusLiftExterior_add y hy π hπ p F hF hker 0 0
    rwa [add_zero, left_eq_add] at this
  have hzeroT : frobeniusLiftExterior z hz π' hπ' p F' hF' hker' 0 = 0 := by
    have := frobeniusLiftExterior_add z hz π' hπ' p F' hF' hker' 0 0
    rwa [add_zero, left_eq_add] at this
  induction x using kaehlerExterior_mul_induction with
  | h1 => rw [map_one, frobeniusLiftExterior_one, frobeniusLiftExterior_one, map_one]
  | hsmul f ω h =>
    rw [kaehlerExteriorMap_smul, frobeniusLiftExterior_smul, h, frobeniusLiftExterior_smul,
      kaehlerExteriorMap_smul, map_pow]
  | hD g ω h =>
    rw [map_mul, kaehlerExteriorMap_ι_D, frobeniusLiftExterior_mul,
      frobeniusLiftExterior_ι_D z hz π' hπ' p F' hF' hker' hann' hp2' hK', h,
      frobeniusLiftExterior_mul, frobeniusLiftExterior_ι_D y hy π hπ p F hF hker hann hp2 hK, map_mul,
      kaehlerExteriorMap_ι,
      frobeniusLiftOneForm_map π hπ p F hF hker hann hp2 π' hπ' F' hF' hker' hann' hp2' ρ' hρ hρF]
  | hadd ω ω' h h' =>
    rw [map_add, frobeniusLiftExterior_add, h, h', frobeniusLiftExterior_add, map_add]
  | h0 => rw [map_zero, hzeroT, hzeroS, map_zero]

end Exterior

section HomotopyMap

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {T : Type v'} [CommRing T]
  [Algebra K T] [Algebra S T] [IsScalarTower K S T]
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ)
  (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hann : ∀ z, (p : L) * z = 0 → π z = 0)
  {L' : Type w'} [CommRing L'] (π' : L' →+* T) (hπ' : Function.Surjective π')
  (F₁' F₂' : L' →+* L') (hF₁' : ∀ x, π' (F₁' x) = π' x ^ p) (hF₂' : ∀ x, π' (F₂' x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = algebraMap S T (π x))
  (hρF₁ : ∀ x, ρ' (F₁ x) = F₁' (ρ' x)) (hρF₂ : ∀ x, ρ' (F₂ x) = F₂' (ρ' x))

include hann hann' hρ hρF₁ hρF₂ in
/-- **The homotopies commute with compatible maps of lifts.** -/
theorem frobeniusLiftHomotopy_map (a : S) :
    frobeniusLiftHomotopy π' hπ' p F₁' F₂' hF₁' hF₂' hker' (algebraMap S T a) =
      algebraMap S T (frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker a) := by
  obtain ⟨x, rfl⟩ := hπ a
  rw [← hρ, frobeniusLiftHomotopy_lift π' hπ' p F₁' F₂' hF₁' hF₂' hker' hann',
    frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_map π p F₁ F₂ hF₁ hF₂ hker π' F₁' F₂' hF₁' hF₂' hker' hann'
      (algebraMap S T) ρ' hρ hρF₁ hρF₂]

end HomotopyMap

end MixedFujita
