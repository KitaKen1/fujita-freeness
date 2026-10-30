/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieOneCocycle
public import MixedFujita.IndexSequenceTotal

/-!
The degree-`1` Deligne–Illusie cocycle as a total index cochain, and its products (step 10).

For a family of Frobenius lifts `F_j` on one chart and a `1`-form `ω`, the cochains `P` and `H` of
check 449 form a total index cochain `φ¹(ω)` on sequences of vertices (check 451):
`P(s) = Φ_{F_{s 0}}(ω)` in Čech degree `0`, `H(s) = h_{F_{s 0} F_{s 1}}(ω)` in Čech degree `1` and
`0` above (`diSeqCocycle`). For the grade involution and the de Rham differential of the chart
(check 448) it is a `D`-cocycle (`seqTotalD_diSeqCocycle`: `dP = 0`, `δP = dH`, `δH = 0`). Hence
the product `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)` of a list of `1`-forms is a `D`-cocycle
(`seqTotalD_diSeqProd`, by check 451), and its component of Čech degree `0` is the Frobenius lift
`Φ_{F_{s 0}}(ω_1 ∧ ⋯ ∧ ω_b)` of check 408 (`diSeqProd_zero_eq_frobeniusLiftExterior`).
-/

@[expose] public section

namespace MixedFujita

universe u v w

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- **The degree-`1` Deligne–Illusie cocycle as a total index cochain**: `P` in Čech degree `0`
and `H` in Čech degree `1`. -/
noncomputable def diSeqCocycle (ω : Ω[S⁄K]) : ℕ → (ℕ → J) → ExteriorAlgebra S Ω[S⁄K]
  | 0 => fun s => diCocycleP y hy π hπ p F hF hker ω fun _ => s 0
  | 1 => fun s => diCocycleH y hy π hπ p F hF hker ω fun k => s k
  | _ + 2 => fun _ => 0

omit hp [CharP K p] in
theorem seqSupported_diSeqCocycle (ω : Ω[S⁄K]) (c : ℕ) :
    SeqSupported c (diSeqCocycle y hy π hπ p F hF hker ω c) := by
  intro s t h
  rcases c with _ | _ | c
  · simp only [diSeqCocycle, h 0 le_rfl]
  · simp only [diSeqCocycle]
    congr 1
    funext k
    exact h k (by have := k.isLt; omega)
  · rfl

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **The degree-`1` Deligne–Illusie cocycle is a `D`-cocycle** for the grade involution and the
de Rham differential: `dP = 0`, `δP = dH` and `δH = 0`. -/
theorem seqTotalD_diSeqCocycle [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (ω : Ω[S⁄K])
    (c : ℕ) (s : ℕ → J) :
    seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom (diSeqCocycle y hy π hπ p F hF hker ω) c s =
      0 := by
  rcases c with _ | _ | _ | c
  · simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, diSeqCocycle, pow_zero, one_mul,
      zero_add, LinearMap.toAddMonoidHom_coe]
    exact kaehlerDeRhamDiff_diCocycleP y hy π hπ p F hF hker hann hp2 hK ω _
  · have e0 : seqSkip 0 0 = 1 := rfl
    have e1 : seqSkip 1 0 = 0 := rfl
    simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Function.comp_apply, e0, e1, pow_zero, pow_one, one_mul,
      neg_one_mul, LinearMap.toAddMonoidHom_coe, diSeqCocycle, diCocycleP, diCocycleH,
      Fin.val_zero, Fin.val_one]
    rw [Algebra.algebraMap_eq_smul_one, kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_one, smul_zero,
      add_zero, mul_one, D_frobeniusLiftHomotopyAux y hy π hπ p (F (s 0)) (F (s 1)) (hF (s 0))
      (hF (s 1)) hker hann hp2, map_sub]
    abel
  · have e00 : seqSkip 0 0 = 1 := rfl
    have e01 : seqSkip 0 1 = 2 := rfl
    have e10 : seqSkip 1 0 = 0 := rfl
    have e11 : seqSkip 1 1 = 2 := rfl
    have e20 : seqSkip 2 0 = 0 := rfl
    have e21 : seqSkip 2 1 = 1 := rfl
    simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Function.comp_apply, e00, e01, e10, e11, e20, e21,
      diSeqCocycle, diCocycleH, Fin.val_zero, Fin.val_one, map_zero, mul_zero, add_zero]
    rw [frobeniusLiftHomotopyAux_cocycle y hy π hπ p (F (s 0)) (F (s 1)) (F (s 2)) (hF (s 0))
      (hF (s 1)) (hF (s 2)) hker hann ω, map_add]
    noncomm_ring
  · simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, diSeqCocycle, mul_zero,
      Finset.sum_const_zero, map_zero, add_zero]

/-- **The product `φ¹(ω_1) ⋆ ⋯ ⋆ φ¹(ω_b)`** of the degree-`1` cocycles of a list of `1`-forms. -/
noncomputable def diSeqProd (ωs : List Ω[S⁄K]) : ℕ → (ℕ → J) → ExteriorAlgebra S Ω[S⁄K] :=
  seqTotalProd (exteriorInvolute K S) (ωs.map (diSeqCocycle y hy π hπ p F hF hker))

omit hp [CharP K p] in
theorem seqSupported_diSeqProd (ωs : List Ω[S⁄K]) (c : ℕ) :
    SeqSupported c (diSeqProd y hy π hπ p F hF hker ωs c) :=
  seqSupported_seqTotalProd _ _ (fun α hα a => by
    obtain ⟨ω, -, rfl⟩ := List.mem_map.mp hα
    exact seqSupported_diSeqCocycle y hy π hπ p F hF hker ω a) c

include hann hp2 in
/-- **The product of the degree-`1` Deligne–Illusie cocycles is a `D`-cocycle.** -/
theorem seqTotalD_diSeqProd [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (ωs : List Ω[S⁄K])
    (c : ℕ) (s : ℕ → J) :
    seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom (diSeqProd y hy π hπ p F hF hker ωs) c s =
      0 :=
  seqTotalD_seqTotalProd (exteriorInvolute K S) exteriorInvolute_involute
    (kaehlerDeRhamDiff y hy).toAddMonoidHom (kaehlerDeRhamDiff_mul y hy)
    (kaehlerDeRhamDiff_exteriorInvolute y hy) _ (fun α hα => by
      obtain ⟨ω, -, rfl⟩ := List.mem_map.mp hα
      exact ⟨seqSupported_diSeqCocycle y hy π hπ p F hF hker ω,
        seqTotalD_diSeqCocycle y hy π hπ p F hF hker hann hp2 hK ω⟩) c s

omit hp [CharP K p] in
/-- The component of Čech degree `0` of the product is `Φ(ω_1) ∧ ⋯ ∧ Φ(ω_b)`. -/
theorem diSeqProd_zero (ωs : List Ω[S⁄K]) (s : ℕ → J) :
    diSeqProd y hy π hπ p F hF hker ωs 0 s = (ωs.map fun ω => ExteriorAlgebra.ι S
      (frobeniusLiftOneFormAux y hy π hπ p (F (s 0)) (hF (s 0)) hker ω)).prod := by
  rw [diSeqProd, seqTotalProd_zero, List.map_map]
  rfl

/-- **The component of Čech degree `0` of the product is the Frobenius lift of
`ω_1 ∧ ⋯ ∧ ω_b`.** -/
theorem diSeqProd_zero_eq_frobeniusLiftExterior (ωs : List Ω[S⁄K]) (s : ℕ → J) :
    diSeqProd y hy π hπ p F hF hker ωs 0 s =
      frobeniusLiftExterior y hy π hπ p (F (s 0)) (hF (s 0)) hker
        (ωs.map (ExteriorAlgebra.ι S)).prod := by
  rw [diSeqProd_zero]
  induction ωs with
  | nil => simp only [List.map_nil, List.prod_nil, frobeniusLiftExterior_one]
  | cons ω ωs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, frobeniusLiftExterior_mul,
      frobeniusLiftExterior_ι, ih]

end MixedFujita
