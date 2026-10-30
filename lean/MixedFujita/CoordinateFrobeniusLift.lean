/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftExistence
public import MixedFujita.LogChartFrobeniusCartier
public import Mathlib.RingTheory.Unramified.Basic

/-!
Coordinate Frobenius lifts (step 10, R4-6).

* `frobeniusLiftOneForm_of_eq_pow`: if a Frobenius lift fixes a lift `x` up to `p`-th powers,
  `F x = x^p`, then the Deligne–Illusie `1`-form of `a = π x` is `a^{p-1} da` (the defect of `x`
  vanishes).
* `map_frobeniusLiftOneFormAux_localLogBasis`: if the coordinates of a localized chart `c'` have
  lifts with `F ỹ_j = ỹ_j^p`, the Frobenius lift maps the local logarithmic basis to
  `C₀(θ_i) = θ_i` in the logarithmic directions and to `y_i^{p-1} θ_i` otherwise. This is the
  vertex-zero hypothesis `hΦ0` of check 491.
* `exists_coordinateFrobeniusLift`: on an algebra `L` over `W[Y_1, …, Y_n]` that is formally smooth,
  with a surjection `π : L → S` of square-zero kernel onto a ring of characteristic `p`, a Frobenius
  `σ` of `W` lifting the `p`-th power map extends to a Frobenius lift `F` of `L` with
  `F(Y_j) = Y_j^p`: apply check 424 to `W[Y]` with the twist `σ` on the coefficients and
  `Y_j ↦ Y_j^p` (`coordinateFrobeniusTwist`).
* `ringHom_eq_of_formallyUnramified`: two maps out of a formally unramified algebra that agree on
  the base and modulo a square-zero ideal are equal. It gives the compatibility `hRF` of the
  coordinate Frobenius lifts with restrictions.

For `W = W₂(κ)` (check 519) and `L = W₂(κ) ⊗_A B` with étale coordinates `A[Y] → B`, these build
the Frobenius lifts of the lift data of check 491.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v w

attribute [local instance] Classical.propDecidable

section Defect

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S) (p : ℕ)
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0)

include hann in
/-- The defect of a lift fixed up to `p`-th powers vanishes. -/
theorem frobeniusLiftDefect_eq_zero_of_eq_pow {x : L} (hx : F x = x ^ p) :
    frobeniusLiftDefect π p F hF hker x = 0 := by
  rw [frobeniusLiftDefect_eq π p F hF hker hann (z := 0) (by rw [hx, sub_self, mul_zero]),
    map_zero]

end Defect

section OneForm

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {L : Type w} [CommRing L]
  (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **The Deligne–Illusie `1`-form of a coordinate fixed by the Frobenius lift**: if `F x = x^p`
then `φ(π x) = (π x)^{p-1} d(π x)`. -/
theorem frobeniusLiftOneForm_of_eq_pow {x : L} (hx : F x = x ^ p) :
    frobeniusLiftOneForm K π hπ p F hF hker (π x) =
      π x ^ (p - 1) • KaehlerDifferential.D K S (π x) := by
  rw [frobeniusLiftOneForm_lift (K := K) π hπ p F hF hker hann hp2 x,
    frobeniusLiftDefect_eq_zero_of_eq_pow π p F hF hker hann hx, map_zero, add_zero]

end OneForm

section LogBasis

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (c' : EtaleChart K X n)
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c'.U)) (hπ : Function.Surjective π) (p : ℕ)
  [hp : Fact p.Prime] [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hy : ∀ j, ∃ y : L, π y = c'.coords (MvPolynomial.X j) ∧ F y = y ^ p)

omit [IsIntegral X] [CharP K p] in
/-- `a^p b^{p-1} = (a b)^{p-1} a`. -/
theorem pow_mul_pow_pred_eq (a b : Γ(X, c'.U)) :
    a ^ p * b ^ (p - 1) = (a * b) ^ (p - 1) * a := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  rw [hq, Nat.add_sub_cancel]
  ring

omit [IsIntegral X] in
include hann hp2 hy in
/-- **The coordinate Frobenius on the local logarithmic basis**:
`Φ_F(θ'_i) = (w_i y_i)^{p-1} θ'_i` for the weights `w_i` of the logarithmic basis. -/
theorem frobeniusLiftOneFormAux_localLogBasis (i : Fin n) :
    frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p F hF hker
        (localLogBasis σ c' hunit i) =
      ((localLogWeight σ c' hunit i : Γ(X, c'.U)) * c'.coords (MvPolynomial.X i)) ^ (p - 1) •
        localLogBasis σ c' hunit i := by
  obtain ⟨y, hyπ, hyF⟩ := hy i
  have h := frobeniusLiftOneForm_of_eq_pow (K := K) π hπ p F hF hker hann hp2 hyF
  rw [hyπ] at h
  rw [localLogBasis, Module.Basis.unitsSMul_apply, Units.smul_def, frobeniusLiftOneFormAux_smul,
    etaleCoordinateBasis_apply, frobeniusLiftOneFormAux_coordinate]
  change (localLogWeight σ c' hunit i : Γ(X, c'.U)) ^ p •
      frobeniusLiftOneForm K π hπ p F hF hker (c'.coords (MvPolynomial.X i)) = _
  rw [h, smul_smul, pow_mul_pow_pred_eq c' p, mul_smul]

include hann hp2 hy in
/-- **The coordinate Frobenius satisfies the vertex-zero hypothesis `hΦ0` of check 491**: in the
function field, `Φ_F(θ'_i) = C₀(θ_i)`. -/
theorem map_frobeniusLiftOneFormAux_localLogBasis
    (hcoords : ∀ j, sectionGermAlgHom (K := K) c'.U (c'.coords (MvPolynomial.X j)) =
      (etaleChartCoordinateRationalUnit c j : X.functionField)) (i : Fin n) :
    KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
        (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p F hF hker
          (localLogBasis σ c' hunit i)) =
      logCartierCoeff c σ p i • logChartBasis c σ i := by
  rw [frobeniusLiftOneFormAux_localLogBasis σ c' hunit π hπ p F hF hker hann hp2 hy i,
    LinearMap.map_smul, map_localLogBasis c σ c' hunit hcoords i,
    ← algebraMap_smul X.functionField]
  congr 1
  rw [logCartierCoeff, localLogWeight]
  by_cases hi : i ∈ logSetOf σ
  · simp only [hi, ↓reduceDIte, ↓reduceIte]
    rw [IsUnit.val_inv_mul, one_pow, map_one]
  · simp only [hi, ↓reduceDIte, ↓reduceIte, Units.val_one, one_mul]
    rw [map_pow, algebraMap_section_eq_sectionGermAlgHom (K := K), hcoords]

end LogBasis

section Existence

variable {W : Type u} [CommRing W] (σ : W →+* W) {n : ℕ} (p : ℕ)

/-- The Frobenius twist of `W[Y_1, …, Y_n]`: `σ` on the coefficients and `Y_j ↦ Y_j^p`. -/
noncomputable def coordinateFrobeniusTwist :
    MvPolynomial (Fin n) W →+* MvPolynomial (Fin n) W :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp σ) fun j => MvPolynomial.X j ^ p

theorem coordinateFrobeniusTwist_C (w : W) :
    coordinateFrobeniusTwist (n := n) σ p (MvPolynomial.C w) = MvPolynomial.C (σ w) :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem coordinateFrobeniusTwist_X (j : Fin n) :
    coordinateFrobeniusTwist σ p (MvPolynomial.X j) = MvPolynomial.X j ^ p :=
  MvPolynomial.eval₂Hom_X' _ _ _

variable {L : Type v} [CommRing L] [Algebra W L] [Algebra (MvPolynomial (Fin n) W) L]
  [IsScalarTower W (MvPolynomial (Fin n) W) L]
  {S : Type v} [CommRing S] [Fact p.Prime] [CharP S p]
  (π : L →+* S) (hπ : Function.Surjective π) (hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0)
  (hσ : ∀ w, π (algebraMap W L (σ w)) = π (algebraMap W L w) ^ p)

include hσ in
/-- The twist lifts the `p`-th power map modulo the kernel of `π`. -/
theorem coordinateFrobeniusTwist_lifts (a : MvPolynomial (Fin n) W) :
    π (algebraMap (MvPolynomial (Fin n) W) L (coordinateFrobeniusTwist σ p a)) =
      π (algebraMap (MvPolynomial (Fin n) W) L a) ^ p := by
  have h : π.comp ((algebraMap (MvPolynomial (Fin n) W) L).comp (coordinateFrobeniusTwist σ p)) =
      (frobenius S p).comp (π.comp (algebraMap (MvPolynomial (Fin n) W) L)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      simp only [RingHom.comp_apply, coordinateFrobeniusTwist_C, frobenius_def]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact hσ w
    · intro j
      simp only [RingHom.comp_apply, coordinateFrobeniusTwist_X, map_pow, frobenius_def]
  exact (RingHom.congr_fun h a).trans (frobenius_def p _)

include hπ hsq hσ in
/-- **Coordinate Frobenius lifts exist**: on a formally smooth `W[Y]`-algebra there is a Frobenius
lift which is `σ` on `W` and maps every coordinate to its `p`-th power. -/
theorem exists_coordinateFrobeniusLift [Algebra.FormallySmooth (MvPolynomial (Fin n) W) L] :
    ∃ F : L →+* L, (∀ x, π (F x) = π x ^ p) ∧
      (∀ w, F (algebraMap W L w) = algebraMap W L (σ w)) ∧
      ∀ j, F (algebraMap (MvPolynomial (Fin n) W) L (MvPolynomial.X j)) =
        algebraMap (MvPolynomial (Fin n) W) L (MvPolynomial.X j) ^ p := by
  obtain ⟨F, hF, hFA⟩ := exists_frobeniusLift_of_formallySmooth
    (coordinateFrobeniusTwist (n := n) σ p) p π hπ hsq
    (coordinateFrobeniusTwist_lifts (n := n) σ p π hσ)
  refine ⟨F, hF, fun w => ?_, fun j => ?_⟩
  · have h := hFA (MvPolynomial.C w)
    rw [coordinateFrobeniusTwist_C, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  · rw [hFA, coordinateFrobeniusTwist_X, map_pow]

end Existence

section Uniqueness

/-- **Maps out of a formally unramified algebra are determined modulo a square-zero ideal**: two
ring maps `L → L'` agreeing on the base and after `π' : L' → S'` with square-zero kernel are
equal. -/
theorem ringHom_eq_of_formallyUnramified {A : Type u} [CommRing A] {L : Type v} [CommRing L]
    [Algebra A L] [Algebra.FormallyUnramified A L] {L' : Type w} [CommRing L'] {S' : Type*}
    [CommRing S'] (π' : L' →+* S') (hsq : ∀ x y, π' x = 0 → π' y = 0 → x * y = 0)
    (F₁ F₂ : L →+* L') (hA : ∀ a, F₁ (algebraMap A L a) = F₂ (algebraMap A L a))
    (hπ : ∀ x, π' (F₁ x) = π' (F₂ x)) : F₁ = F₂ := by
  let _ : Algebra A L' := (F₁.comp (algebraMap A L)).toAlgebra
  let g₁ : L →ₐ[A] L' := { F₁ with commutes' := fun _ => rfl }
  let g₂ : L →ₐ[A] L' := { F₂ with commutes' := fun a => (hA a).symm }
  have hI : IsNilpotent (RingHom.ker π') := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    exact hsq x y hx hy
  have h := Algebra.FormallyUnramified.lift_unique_of_ringHom π' hI g₁ g₂ (RingHom.ext hπ)
  ext x
  exact congrArg (fun g : L →ₐ[A] L' => g x) h

end Uniqueness

end MixedFujita
