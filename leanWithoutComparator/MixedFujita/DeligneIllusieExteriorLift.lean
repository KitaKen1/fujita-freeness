/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieSequenceLinear
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
The Deligne–Illusie map on `b`-forms of a chart (step 10).

By check 454 the product `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)` of the degree-`1` Deligne–Illusie cocycles is
additive and Frobenius-semilinear in each `ω_i`, i.e. an `S`-multilinear map into the total index
cochains with values in the Frobenius twist `FrobeniusTwistedExterior` of check 405
(`diSeqMultilinear`). Its antisymmetrization is alternating, so it factors through `⋀^b`
(`diSeqAlt`, by `MultilinearMap.alternatization` and `exteriorPower.alternatingMapLinearEquiv`):
`diSeqAlt (ω_1 ∧ ⋯ ∧ ω_b) = Σ_σ sgn σ · φ¹(ω_{σ 1}) ⋆ ⋯ ⋆ φ¹(ω_{σ b})` (`diSeqAlt_ιMulti`).
Up to the factor `b!`, this is the Deligne–Illusie map on `b`-forms.
-/

@[expose] public section

namespace MixedFujita

universe u v w

theorem list_ofFn_update {α : Type*} {b : ℕ} [DecidableEq (Fin b)] (m : Fin b → α) (i : Fin b)
    (v : α) :
    List.ofFn (Function.update m i v) = (List.ofFn m).take i ++ v :: (List.ofFn m).drop (i + 1) := by
  have hset : List.ofFn (Function.update m i v) = (List.ofFn m).set i v := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  rw [hset, List.set_eq_take_append_cons_drop]
  simp only [List.length_ofFn, Fin.is_lt, ↓reduceIte]

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- **The product of the degree-`1` Deligne–Illusie cocycles as a multilinear map** into the total
index cochains with values in the Frobenius twist. -/
noncomputable def diSeqMultilinear (b : ℕ) :
    MultilinearMap S (fun _ : Fin b => Ω[S⁄K]) (ℕ → (ℕ → J) → FrobeniusTwistedExterior K S p) where
  toFun m := diSeqProd y hy π hπ p F hF hker (List.ofFn m)
  map_update_add' m i x x' := by
    simp only [list_ofFn_update]
    exact diSeqProd_append_cons_add y hy π hπ p F hF hker _ _ x x'
  map_update_smul' m i c x := by
    simp only [list_ofFn_update]
    rw [diSeqProd_append_cons_smul y hy π hπ p F hF hker]
    funext a s
    exact (frobeniusTwisted_smul_eq p c _).symm

theorem diSeqMultilinear_apply (b : ℕ) (m : Fin b → Ω[S⁄K]) :
    diSeqMultilinear y hy π hπ p F hF hker b m = diSeqProd y hy π hπ p F hF hker (List.ofFn m) :=
  rfl

/-- **The Deligne–Illusie map on `b`-forms** (up to the factor `b!`): the antisymmetrized product
of the degree-`1` cocycles, lifted to `⋀^b`. -/
noncomputable def diSeqAlt (b : ℕ) :
    ⋀[S]^b Ω[S⁄K] →ₗ[S] (ℕ → (ℕ → J) → FrobeniusTwistedExterior K S p) :=
  exteriorPower.alternatingMapLinearEquiv
    (MultilinearMap.alternatization (diSeqMultilinear y hy π hπ p F hF hker b))

/-- **The value on `ω_1 ∧ ⋯ ∧ ω_b`**: `Σ_σ sgn σ · φ¹(ω_{σ 1}) ⋆ ⋯ ⋆ φ¹(ω_{σ b})`. -/
theorem diSeqAlt_ιMulti (b : ℕ) (ω : Fin b → Ω[S⁄K]) :
    diSeqAlt y hy π hπ p F hF hker b (exteriorPower.ιMulti S b ω) =
      ∑ σ : Equiv.Perm (Fin b), Equiv.Perm.sign σ •
        diSeqMultilinear y hy π hπ p F hF hker b (fun i => ω (σ i)) := by
  rw [diSeqAlt, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply]
  rfl

end MixedFujita
