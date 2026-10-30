/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieCoordinateIndependence

/-!
Reindexing the Frobenius lifts of the Deligne–Illusie map of a chart (step 10).

On a Čech intersection `U_x` the Frobenius lifts are indexed by the vertices of `x`; on a face
`x ∘ Fin.succAbove k` they are the lifts of `x` composed with the vertex map. A total index
cochain `α` for lifts indexed by `J'` gives one for `J` by composing the vertex sequences with
`e : J → J'` (`seqTotalReindex`). The product of total cochains commutes with this reindexing
(`seqTotalMul_reindex`, definitionally), and so do the degree-`1` Deligne–Illusie cocycle, its
products and the Deligne–Illusie map on `b`-forms: the map for the lifts `F ∘ e` is the map for
`F` read along `e` (`diSeqCocycle_reindex`, `diSeqProd_reindex`, `diSeqAlt_reindex`).
-/

@[expose] public section

namespace MixedFujita

universe u v w

section Reindex

variable {J J' : Type*} {A : Type*} [Ring A] (σ : A →+* A)

/-- **Reading a total index cochain along a map of index sets.** -/
def seqTotalReindex (e : J → J') (α : ℕ → (ℕ → J') → A) : ℕ → (ℕ → J) → A :=
  fun c t => α c (e ∘ t)

theorem seqTotalMul_reindex (e : J → J') (α β : ℕ → (ℕ → J') → A) :
    seqTotalMul σ (seqTotalReindex e α) (seqTotalReindex e β) =
      seqTotalReindex e (seqTotalMul σ α β) := rfl

theorem seqTotalOne_reindex (e : J → J') :
    seqTotalReindex e (seqTotalOne (J := J') (A := A)) = seqTotalOne := by
  funext c t
  cases c <;> rfl

theorem seqTotalProd_reindex (e : J → J') (l : List (ℕ → (ℕ → J') → A)) :
    seqTotalProd σ (l.map (seqTotalReindex e)) = seqTotalReindex e (seqTotalProd σ l) := by
  induction l with
  | nil => exact (seqTotalOne_reindex e).symm
  | cons α l ih => rw [List.map_cons, seqTotalProd_cons, seqTotalProd_cons, ih, seqTotalMul_reindex]

end Reindex

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J J' : Type*} (F : J' → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (e : J → J')

omit hp [CharP K p] in
/-- **The degree-`1` cocycle for the lifts `F ∘ e` is the cocycle for `F` read along `e`.** -/
theorem diSeqCocycle_reindex (ω : Ω[S⁄K]) :
    diSeqCocycle y hy π hπ p (fun j => F (e j)) (fun j => hF (e j)) hker ω =
      seqTotalReindex e (diSeqCocycle y hy π hπ p F hF hker ω) := by
  funext c t
  rcases c with _ | _ | c <;> rfl

omit hp [CharP K p] in
theorem diSeqProd_reindex (ωs : List Ω[S⁄K]) :
    diSeqProd y hy π hπ p (fun j => F (e j)) (fun j => hF (e j)) hker ωs =
      seqTotalReindex e (diSeqProd y hy π hπ p F hF hker ωs) := by
  rw [diSeqProd, diSeqProd, ← seqTotalProd_reindex, List.map_map]
  congr 1
  refine List.map_congr_left fun ω _ => ?_
  exact diSeqCocycle_reindex y hy π hπ p F hF hker e ω

variable (K S J J') in
/-- Reindexing total cochains with values in the Frobenius twist, as an `S`-linear map. -/
def twistedReindexLinear (e : J → J') :
    (ℕ → (ℕ → J') → FrobeniusTwistedExterior K S p) →ₗ[S]
      (ℕ → (ℕ → J) → FrobeniusTwistedExterior K S p) where
  toFun g := seqTotalReindex e g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem diSeqMultilinear_reindex (b : ℕ) :
    diSeqMultilinear y hy π hπ p (fun j => F (e j)) (fun j => hF (e j)) hker b =
      (twistedReindexLinear K S p J J' e).compMultilinearMap
        (diSeqMultilinear y hy π hπ p F hF hker b) :=
  MultilinearMap.ext fun m => by
    rw [LinearMap.compMultilinearMap_apply, diSeqMultilinear_apply, diSeqMultilinear_apply,
      diSeqProd_reindex]
    rfl

/-- **The Deligne–Illusie map on `b`-forms for the lifts `F ∘ e` is the map for `F` read along
`e`.** -/
theorem diSeqAlt_reindex (b : ℕ) :
    diSeqAlt y hy π hπ p (fun j => F (e j)) (fun j => hF (e j)) hker b =
      twistedReindexLinear K S p J J' e ∘ₗ diSeqAlt y hy π hπ p F hF hker b := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun ω => ?_)
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    diSeqAlt_ιMulti, diSeqAlt_ιMulti, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_zsmul_unit, diSeqMultilinear_reindex, LinearMap.compMultilinearMap_apply]

end MixedFujita
