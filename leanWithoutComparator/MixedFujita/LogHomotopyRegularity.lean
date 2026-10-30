/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateFrobeniusLift
public import MixedFujita.FrobeniusLiftNaturality
public import MixedFujita.OpenRestrictionForms
public import MixedFujita.LogRegularForms

/-!
Regularity of the homotopies and Frobenius forms on the logarithmic basis (step 10, R4-6).

Let `c` be a chart on `U` and `c'` the chart on `U' ⊆ U` with the restricted coordinates, on which
the logarithmic coordinates are units. Let `F₁, F₂` be Frobenius lifts on lifts of the functions on
`U`, restricting to `F₁', F₂'` on lifts of the functions on `U'`.

* `frobeniusLiftHomotopy_eq_of_eq_mul`: if `Z = V Z'` with `F₁ Z = Z^p` and `F₂ Z' = Z'^p`, then
  `h(π Z) = (π Z')^p δ₂(V)`.
* `frobeniusLiftHomotopyAux_localLogBasis`: `h'(θ'_i) = w_i^p h(y_i)` for the weights of the local
  logarithmic basis.
* `algebraMap_frobeniusLiftHomotopyAux_localLogBasis_mem`: the homotopy `h'_{F₁'F₂'}(θ'_i)` is
  regular on `U`. In a non-logarithmic direction it is the restriction of `h_{F₁F₂}(y_i)`
  (check 412). In a logarithmic direction, if `y_i = u z` with `u` a unit and `z = π Z`, `Z = V Z'`
  as above with `π V` a unit, then `y_i^{-p} h(y_i) = u^{-p} h(u) + (π V)^{-p} δ₂(V)`.
* `logChartBasis_repr_frobeniusLiftOneFormAux_mem`: if `Φ_{F₀}(θ'_i) = C₀(θ_i)` and the homotopy
  `h'_{F₀F}(θ'_i)` is regular, then `Φ_F(θ'_i) = C₀(θ_i) + d h'_{F₀F}(θ'_i)` has regular
  logarithmic coefficients.

These are the hypotheses `hH` and `hΦ` of check 491, with the boundary relations of check 547.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v w w'

attribute [local instance] Classical.propDecidable

section Algebra

variable {S : Type v} [CommRing S] {L : Type w} [CommRing L] (π : L →+* S)
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] (F₁ F₂ : L →+* L)
  (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

omit [Fact p.Prime] in
include hann hp2 in
/-- **The homotopy at a boundary coordinate**: if `Z = V Z'` with `F₁ Z = Z^p` and `F₂ Z' = Z'^p`,
then `h(π Z) = (π Z')^p δ₂(V)`. -/
theorem frobeniusLiftHomotopy_eq_of_eq_mul {Z Z' V : L} (hZ : Z = V * Z') (hZ₁ : F₁ Z = Z ^ p)
    (hZ₂ : F₂ Z' = Z' ^ p) :
    frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (π Z) =
      π Z' ^ p * frobeniusLiftDefect π p F₂ hF₂ hker V := by
  rw [frobeniusLiftHomotopy_lift π hπ p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDifference_eq_sub π p F₁ F₂ hF₁ hF₂ hker hann,
    frobeniusLiftDefect_eq_zero_of_eq_pow π p F₁ hF₁ hker hann hZ₁, sub_zero, hZ,
    frobeniusLiftDefect_mul π p F₂ hF₂ hker hann hp2,
    frobeniusLiftDefect_eq_zero_of_eq_pow π p F₂ hF₂ hker hann hZ₂, mul_zero, zero_add]

end Algebra

section LogBasis

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Homotopy

variable {r : ℕ} (σ : Fin r → Option (Fin n)) (c' : EtaleChart K X n)
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c'.U)) (hπ : Function.Surjective π) (p : ℕ)
  [hp : Fact p.Prime] (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p)
  (hF₂ : ∀ x, π (F₂ x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

omit [IsIntegral X] in
/-- **The homotopy on the local logarithmic basis**: `h'(θ'_i) = w_i^p h(y_i)`. -/
theorem frobeniusLiftHomotopyAux_localLogBasis (i : Fin n) :
    frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π hπ p F₁ F₂ hF₁ hF₂ hker
        (localLogBasis σ c' hunit i) =
      (localLogWeight σ c' hunit i : Γ(X, c'.U)) ^ p *
        frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (c'.coords (MvPolynomial.X i)) := by
  rw [localLogBasis, Module.Basis.unitsSMul_apply, Units.smul_def, frobeniusLiftHomotopyAux_smul,
    etaleCoordinateBasis_apply, frobeniusLiftHomotopyAux_coordinate]

end Homotopy

section Regularity

variable (c c' : EtaleChart K X n) (hle : c'.U ≤ c.U)
  (hcc : ∀ j, c'.coords (MvPolynomial.X j) =
    (X.presheaf.map (homOfLE hle).op).hom (c.coords (MvPolynomial.X j)))
  {r : ℕ} (σ : Fin r → Option (Fin n))
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U)) (hπ : Function.Surjective π)
  {L' : Type w'} [CommRing L'] (π' : L' →+* Γ(X, c'.U)) (hπ' : Function.Surjective π')
  (p : ℕ) [hp : Fact p.Prime]
  (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
  (F₁' F₂' : L' →+* L') (hF₁' : ∀ x, π' (F₁' x) = π' x ^ p) (hF₂' : ∀ x, π' (F₂' x) = π' x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (hp2 : (p : L) * p = 0)
  (ρ : L →+* L') (hρ : ∀ x, π' (ρ x) = (X.presheaf.map (homOfLE hle).op).hom (π x))
  (hρF₁ : ∀ x, ρ (F₁ x) = F₁' (ρ x)) (hρF₂ : ∀ x, ρ (F₂ x) = F₂' (ρ x))

omit [X.Over (Spec (CommRingCat.of K))] in
/-- The germ of a unit is nonzero. -/
theorem germ_unit_ne_zero {U : X.Opens} [Nonempty U] (u : Γ(X, U)ˣ) :
    algebraMap Γ(X, U) X.functionField (u : Γ(X, U)) ≠ 0 := by
  intro h
  have h1 : algebraMap Γ(X, U) X.functionField ((u : Γ(X, U)) * (u⁻¹ : Γ(X, U)ˣ)) = 1 := by
    rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

include hcc hπ hF₁ hF₂ hker hann hann' hp2 hρ hρF₁ hρF₂ in
/-- **The homotopies on the local logarithmic basis are regular on the bigger chart.** -/
theorem algebraMap_frobeniusLiftHomotopyAux_localLogBasis_mem
    (hlog : ∀ i ∈ logSetOf σ, ∃ (u : Γ(X, c.U)ˣ) (Z Z' V : L),
      c.coords (MvPolynomial.X i) = u * π Z ∧ Z = V * Z' ∧ F₁ Z = Z ^ p ∧ F₂ Z' = Z' ^ p ∧
        IsUnit (π V))
    (i : Fin n) :
    haveI := c'.nonempty
    algebraMap Γ(X, c'.U) X.functionField
        (frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π' hπ' p F₁' F₂' hF₁' hF₂' hker'
          (localLogBasis σ c' hunit i)) ∈ chartRegularFunctions c := by
  let _ := openRestrictAlgebra K hle
  have := c.nonempty
  have := c'.nonempty
  have htow : ∀ a : Γ(X, c.U), algebraMap Γ(X, c'.U) X.functionField
      ((X.presheaf.map (homOfLE hle).op).hom a) = algebraMap Γ(X, c.U) X.functionField a := by
    intro a
    have := openRestrict_functionField_isScalarTower (K := K) hle
    exact (IsScalarTower.algebraMap_apply Γ(X, c.U) Γ(X, c'.U) X.functionField a).symm
  -- the homotopy of the restricted coordinate is the restriction of the homotopy
  have hmap : frobeniusLiftHomotopy π' hπ' p F₁' F₂' hF₁' hF₂' hker'
      (c'.coords (MvPolynomial.X i)) = (X.presheaf.map (homOfLE hle).op).hom
        (frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (c.coords (MvPolynomial.X i))) := by
    rw [hcc]
    exact frobeniusLiftHomotopy_map π hπ p F₁ F₂ hF₁ hF₂ hker hann π' hπ' F₁' F₂' hF₁' hF₂' hker'
      hann' ρ hρ hρF₁ hρF₂ _
  rw [frobeniusLiftHomotopyAux_localLogBasis, hmap, map_mul, map_pow, htow]
  by_cases hi : i ∈ logSetOf σ
  · obtain ⟨u, Z, Z', V, hu, hZ, hZ₁, hZ₂, hV⟩ := hlog i hi
    -- the inverse of the coordinate
    have hw : algebraMap Γ(X, c'.U) X.functionField (localLogWeight σ c' hunit i : Γ(X, c'.U)) *
        (algebraMap Γ(X, c.U) X.functionField (u : Γ(X, c.U)) *
          (algebraMap Γ(X, c.U) X.functionField (π V) *
            algebraMap Γ(X, c.U) X.functionField (π Z'))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hZ, ← hu, ← htow, ← hcc, ← map_mul]
      simp only [localLogWeight, hi, ↓reduceDIte, IsUnit.val_inv_mul, map_one]
    have hu' : algebraMap Γ(X, c.U) X.functionField ((u⁻¹ : Γ(X, c.U)ˣ) : Γ(X, c.U)) *
        algebraMap Γ(X, c.U) X.functionField (u : Γ(X, c.U)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hV' : algebraMap Γ(X, c.U) X.functionField ((hV.unit⁻¹ : Γ(X, c.U)ˣ) : Γ(X, c.U)) *
        algebraMap Γ(X, c.U) X.functionField (π V) = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    have hz : algebraMap Γ(X, c.U) X.functionField (π Z') ≠ 0 := by
      intro h0
      rw [h0, mul_zero, mul_zero, mul_zero] at hw
      exact zero_ne_one hw
    have hu0 := germ_unit_ne_zero u
    have hV0 : algebraMap Γ(X, c.U) X.functionField (π V) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hV'
      exact zero_ne_one hV'
    refine ⟨((hV.unit⁻¹ : Γ(X, c.U)ˣ) : Γ(X, c.U)) ^ p * frobeniusLiftDefect π p F₂ hF₂ hker V +
      ((u⁻¹ : Γ(X, c.U)ˣ) : Γ(X, c.U)) ^ p *
        frobeniusLiftHomotopy π hπ p F₁ F₂ hF₁ hF₂ hker (u : Γ(X, c.U)), ?_⟩
    change algebraMap Γ(X, c.U) X.functionField _ = _
    rw [hu, frobeniusLiftHomotopy_mul π hπ p F₁ F₂ hF₁ hF₂ hker hann,
      frobeniusLiftHomotopy_eq_of_eq_mul π hπ p F₁ F₂ hF₁ hF₂ hker hann hp2 hZ hZ₁ hZ₂, hZ,
      map_mul π]
    simp only [map_add, map_mul, map_pow]
    rw [eq_inv_of_mul_eq_one_left hw, eq_inv_of_mul_eq_one_left hu',
      eq_inv_of_mul_eq_one_left hV']
    simp only [inv_pow, mul_pow, mul_inv]
    field_simp
  · simp only [localLogWeight, hi, ↓reduceDIte, Units.val_one, map_one, one_pow, one_mul]
    exact ⟨_, rfl⟩

omit hp in
/-- The coefficient of `C₀(θ_i)` is regular. -/
theorem logCartierCoeff_mem_chartRegularFunctions (i : Fin n) :
    logCartierCoeff c σ p i ∈ chartRegularFunctions c := by
  rw [logCartierCoeff]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.pow_mem _ (coordinate_mem_chartRegularFunctions c i) _

end Regularity

section OneForm

variable (c c' : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L' : Type w'} [CommRing L'] (π' : L' →+* Γ(X, c'.U)) (hπ' : Function.Surjective π')
  (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  (F₀ F : L' →+* L') (hF₀ : ∀ x, π' (F₀ x) = π' x ^ p) (hF : ∀ x, π' (F x) = π' x ^ p)
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (hp2' : (p : L') * p = 0)

include hann' hp2' in
/-- **The Frobenius forms have regular logarithmic coefficients**, from the vertex-zero formula
`Φ_{F₀}(θ'_i) = C₀(θ_i)` and the regularity of the homotopy `h'_{F₀F}(θ'_i)`. -/
theorem logChartBasis_repr_frobeniusLiftOneFormAux_mem (i : Fin n)
    (hΦ0 : haveI := c'.nonempty
      KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
        (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π' hπ' p F₀ hF₀ hker'
          (localLogBasis σ c' hunit i)) =
      logCartierCoeff c σ p i • logChartBasis c σ i)
    (hH : haveI := c'.nonempty
      algebraMap Γ(X, c'.U) X.functionField
        (frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π' hπ' p F₀ F hF₀ hF hker'
          (localLogBasis σ c' hunit i)) ∈ chartRegularFunctions c) (t : Fin n) :
    haveI := c'.nonempty
    (logChartBasis c σ).repr (KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
        (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π' hπ' p F hF hker'
          (localLogBasis σ c' hunit i))) t ∈ chartRegularFunctions c := by
  have := c'.nonempty
  have hD := D_frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π' hπ' p F₀ F hF₀ hF hker' hann'
    hp2' (localLogBasis σ c' hunit i)
  rw [eq_add_of_sub_eq hD.symm, map_add, KaehlerDifferential.map_D, hΦ0, map_add,
    Finsupp.add_apply]
  obtain ⟨b, hb⟩ := hH
  refine Subalgebra.add_mem _ ?_ ?_
  · rw [← hb]
    exact logChartBasis_repr_kaehlerD_mem c σ b t
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
    refine Subalgebra.mul_mem _ (logCartierCoeff_mem_chartRegularFunctions c σ p i) ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _

end OneForm

end LogBasis

end MixedFujita
