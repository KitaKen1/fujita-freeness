/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieExteriorLiftCocycle

/-!
The Deligne–Illusie map of a chart does not depend on the coordinates (step 10).

The maps `Φ_F` on `1`-forms (check 408) and `h_{F₁F₂}` (check 409) are defined through the
coordinate basis `dy_j` of a chart, but both are additive, Frobenius-semilinear
(`f(c ω) = c^p f(ω)`) and take intrinsic values on exact forms (`frobeniusLiftOneFormAux_D`,
`frobeniusLiftHomotopyAux_D`). Since the exact forms span `Ω[S⁄K]`, such a map is determined by
these values (`eq_of_frobeniusSemilinear_D`), so `Φ_F` and `h` agree for any two coordinate
systems `y`, `y'` on the same algebra (`frobeniusLiftOneFormAux_coord`,
`frobeniusLiftHomotopyAux_coord`). Hence so do the degree-`1` Deligne–Illusie cocycle, its
products and the Deligne–Illusie map on `b`-forms (`diSeqCocycle_coord`, `diSeqProd_coord`,
`diSeqAlt_coord`). On a Čech intersection the chart is the restriction of the chart of the first
index, and deleting the first index changes the chart; this is what makes the globalization
independent of that choice.
-/

@[expose] public section

namespace MixedFujita

universe u v w

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

/-- **An additive Frobenius-semilinear map on `Ω[S⁄K]` is determined by its values on exact
forms.** -/
theorem eq_of_frobeniusSemilinear_D (p : ℕ) [hp : Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module S M] (f g : Ω[S⁄K] → M) (hf : ∀ ω η, f (ω + η) = f ω + f η)
    (hg : ∀ ω η, g (ω + η) = g ω + g η) (hfs : ∀ (c : S) ω, f (c • ω) = c ^ p • f ω)
    (hgs : ∀ (c : S) ω, g (c • ω) = c ^ p • g ω)
    (hD : ∀ a, f (KaehlerDifferential.D K S a) = g (KaehlerDifferential.D K S a))
    (ω : Ω[S⁄K]) : f ω = g ω := by
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero =>
    have h1 : f 0 = 0 := by simpa [zero_pow hp.out.ne_zero] using hfs 0 0
    have h2 : g 0 = 0 := by simpa [zero_pow hp.out.ne_zero] using hgs 0 0
    rw [h1, h2]
  | add x z _ _ hx hz => rw [hf, hg, hx, hz]
  | smul c x _ hx => rw [hfs, hgs, hx]

variable {n n' : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  (y' : MvPolynomial (Fin n') K →ₐ[K] S) (hy' : y'.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **`Φ_F` on `1`-forms does not depend on the coordinates.** -/
theorem frobeniusLiftOneFormAux_coord [Algebra.FiniteType K S] (F : L →+* L)
    (hF : ∀ x, π (F x) = π x ^ p)
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p) (ω : Ω[S⁄K]) :
    frobeniusLiftOneFormAux y hy π hπ p F hF hker ω =
      frobeniusLiftOneFormAux y' hy' π hπ p F hF hker ω :=
  eq_of_frobeniusSemilinear_D p _ _ (frobeniusLiftOneFormAux_add y hy π hπ p F hF hker)
    (frobeniusLiftOneFormAux_add y' hy' π hπ p F hF hker)
    (frobeniusLiftOneFormAux_smul y hy π hπ p F hF hker)
    (frobeniusLiftOneFormAux_smul y' hy' π hπ p F hF hker) (fun a => by
      rw [frobeniusLiftOneFormAux_D y hy π hπ p F hF hker hann hp2 hK,
        frobeniusLiftOneFormAux_D y' hy' π hπ p F hF hker hann hp2 hK]) ω

omit hp2 in
include hann in
/-- **The homotopy `h_{F₁F₂}` on `1`-forms does not depend on the coordinates.** -/
theorem frobeniusLiftHomotopyAux_coord [Algebra.FiniteType K S] (F₁ F₂ : L →+* L)
    (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F₁ c' = c' ^ p ∧ F₂ c' = c' ^ p)
    (ω : Ω[S⁄K]) :
    frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω =
      frobeniusLiftHomotopyAux y' hy' π hπ p F₁ F₂ hF₁ hF₂ hker ω :=
  eq_of_frobeniusSemilinear_D p _ _ (frobeniusLiftHomotopyAux_add y hy π hπ p F₁ F₂ hF₁ hF₂ hker)
    (frobeniusLiftHomotopyAux_add y' hy' π hπ p F₁ F₂ hF₁ hF₂ hker)
    (fun c ω => by rw [frobeniusLiftHomotopyAux_smul, smul_eq_mul])
    (fun c ω => by rw [frobeniusLiftHomotopyAux_smul, smul_eq_mul]) (fun a => by
      rw [frobeniusLiftHomotopyAux_D y hy π hπ p F₁ F₂ hF₁ hF₂ hker hann hK,
        frobeniusLiftHomotopyAux_D y' hy' π hπ p F₁ F₂ hF₁ hF₂ hker hann hK]) ω

variable {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)

include hann hp2 in
/-- **The degree-`1` Deligne–Illusie cocycle does not depend on the coordinates.** -/
theorem diSeqCocycle_coord [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (ω : Ω[S⁄K]) :
    diSeqCocycle y hy π hπ p F hF hker ω = diSeqCocycle y' hy' π hπ p F hF hker ω := by
  funext c s
  rcases c with _ | _ | c
  · simp only [diSeqCocycle, diCocycleP]
    rw [frobeniusLiftOneFormAux_coord y hy y' hy' π hπ p hker hann hp2 (F (s 0)) (hF (s 0))
      (fun c => (hK c).imp fun c' h => ⟨h.1, h.2 (s 0)⟩)]
  · simp only [diSeqCocycle, diCocycleH, Fin.val_zero, Fin.val_one]
    rw [frobeniusLiftHomotopyAux_coord y hy y' hy' π hπ p hker hann (F (s 0)) (F (s 1))
      (hF (s 0)) (hF (s 1)) (fun c => (hK c).imp fun c' h => ⟨h.1, h.2 (s 0), h.2 (s 1)⟩)]
  · rfl

include hann hp2 in
/-- **The products of the Deligne–Illusie cocycles do not depend on the coordinates.** -/
theorem diSeqProd_coord [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (ωs : List Ω[S⁄K]) :
    diSeqProd y hy π hπ p F hF hker ωs = diSeqProd y' hy' π hπ p F hF hker ωs := by
  rw [diSeqProd, diSeqProd,
    show diSeqCocycle y hy π hπ p F hF hker = diSeqCocycle y' hy' π hπ p F hF hker from
      funext fun ω => diSeqCocycle_coord y hy y' hy' π hπ p hker hann hp2 F hF hK ω]

include hann hp2 in
/-- **The Deligne–Illusie map on `b`-forms does not depend on the coordinates.** -/
theorem diSeqAlt_coord [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (b : ℕ) :
    diSeqAlt y hy π hπ p F hF hker b = diSeqAlt y' hy' π hπ p F hF hker b := by
  have h : diSeqMultilinear y hy π hπ p F hF hker b = diSeqMultilinear y' hy' π hπ p F hF hker b :=
    MultilinearMap.ext fun m => by
      rw [diSeqMultilinear_apply, diSeqMultilinear_apply,
        diSeqProd_coord y hy y' hy' π hπ p hker hann hp2 F hF hK]
  rw [diSeqAlt, diSeqAlt, h]

end MixedFujita
