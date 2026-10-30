/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExteriorDeRhamGradedLeibniz
public import MixedFujita.FrobeniusLiftCocycle

/-!
The degree-`1` Deligne–Illusie cocycle on the index nerve of a chart (step 10).

On an étale chart with a family `F_j` (`j ∈ J`) of Frobenius lifts on the same lift modulo `p²`, a
`1`-form `ω` gives the index cochains `P(j) = Φ_{F_j}(ω)` (Čech degree `0`, de Rham degree `1`,
`diCocycleP`) and `H(j₀, j₁) = h_{j₀ j₁}(ω)` (Čech degree `1`, de Rham degree `0`, `diCocycleH`).
They form a cocycle for the total differential `D = δ + (-1)^a d`: `d P = 0` (closed values,
`kaehlerDeRhamDiff_diCocycleP`), `δ P = d H` (`d h_{j₀ j₁} = Φ_{j₁} - Φ_{j₀}`,
`indexCechD_diCocycleP`) and `δ H = 0` (the cocycle identity, `indexCechD_diCocycleH`). The
antisymmetrized cup products of these cocycles (checks 446–448) are the components of the
Deligne–Illusie map in higher degrees.
-/

@[expose] public section

namespace MixedFujita

universe u v w

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- The Čech-degree-`0` part of the degree-`1` Deligne–Illusie cocycle: `j ↦ Φ_{F_j}(ω)`. -/
noncomputable def diCocycleP (ω : Ω[S⁄K]) : (Fin 1 → J) → ExteriorAlgebra S Ω[S⁄K] :=
  fun j => ExteriorAlgebra.ι S (frobeniusLiftOneFormAux y hy π hπ p (F (j 0)) (hF (j 0)) hker ω)

/-- The Čech-degree-`1` part: `(j₀, j₁) ↦ h_{j₀ j₁}(ω)`. -/
noncomputable def diCocycleH (ω : Ω[S⁄K]) : (Fin 2 → J) → ExteriorAlgebra S Ω[S⁄K] :=
  fun j => algebraMap S _ (frobeniusLiftHomotopyAux y hy π hπ p (F (j 0)) (F (j 1)) (hF (j 0))
    (hF (j 1)) hker ω)

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **The cocycle has closed `C^{0,1}` part.** -/
theorem kaehlerDeRhamDiff_diCocycleP [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (ω : Ω[S⁄K])
    (j : Fin 1 → J) : kaehlerDeRhamDiff y hy (diCocycleP y hy π hπ p F hF hker ω j) = 0 := by
  rw [diCocycleP, ← frobeniusLiftExterior_ι]
  exact frobeniusLiftExterior_closed y hy π hπ p (F (j 0)) (hF (j 0)) hker hann hp2
    (fun c => (hK c).imp fun c' h => ⟨h.1, h.2 (j 0)⟩) _

include hann hp2 in
/-- **`δ P = d H`**: `Φ_{j₁}(ω) - Φ_{j₀}(ω) = d h_{j₀ j₁}(ω)`. -/
theorem indexCechD_diCocycleP (ω : Ω[S⁄K]) (j : Fin 2 → J) :
    indexCechD 0 (diCocycleP y hy π hπ p F hF hker ω) j =
      kaehlerDeRhamDiff y hy (diCocycleH y hy π hπ p F hF hker ω j) := by
  have e0 : (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 := by decide
  have e1 : (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 := by decide
  rw [indexCechD, Fin.sum_univ_two, diCocycleH, Algebra.algebraMap_eq_smul_one,
    kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_one, smul_zero, add_zero, mul_one,
    D_frobeniusLiftHomotopyAux y hy π hπ p (F (j 0)) (F (j 1)) (hF (j 0)) (hF (j 1)) hker hann hp2,
    map_sub]
  simp only [diCocycleP, Function.comp_apply, e0, e1, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_mul, neg_one_mul]
  abel

omit hp [CharP K p] in
include hann in
/-- **`δ H = 0`**: the cocycle identity `h₁₂ - h₀₂ + h₀₁ = 0`. -/
theorem indexCechD_diCocycleH (ω : Ω[S⁄K]) (j : Fin 3 → J) :
    indexCechD 1 (diCocycleH y hy π hπ p F hF hker ω) j = 0 := by
  have e00 : (Fin.succAbove (0 : Fin 3) 0 : Fin 3) = 1 := by decide
  have e01 : (Fin.succAbove (0 : Fin 3) 1 : Fin 3) = 2 := by decide
  have e10 : (Fin.succAbove (1 : Fin 3) 0 : Fin 3) = 0 := by decide
  have e11 : (Fin.succAbove (1 : Fin 3) 1 : Fin 3) = 2 := by decide
  have e20 : (Fin.succAbove (2 : Fin 3) 0 : Fin 3) = 0 := by decide
  have e21 : (Fin.succAbove (2 : Fin 3) 1 : Fin 3) = 1 := by decide
  rw [indexCechD, Fin.sum_univ_three]
  simp only [diCocycleH, Function.comp_apply, e00, e01, e10, e11, e20, e21]
  rw [frobeniusLiftHomotopyAux_cocycle y hy π hπ p (F (j 0)) (F (j 1)) (F (j 2)) (hF (j 0))
    (hF (j 1)) (hF (j 2)) hker hann ω, map_add]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul, neg_one_mul,
    even_two, Even.neg_one_pow]
  abel

end MixedFujita
