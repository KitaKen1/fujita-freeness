/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.FormalTestSNCBadComponent

/-!
Realization of a profile by a tuple of sections, in terms of rational functions that do not
depend on the point (step 9). Let f be a local equation of D at y. The coefficient of the pullback
of the zero divisor of a section s along a prime divisor whose centre contains y is the order of
f · s, a rational function independent of y. So for a nonnegative rational profile β with common
exponents e_i β_i = M, a tuple of combinations Σ_k c_ik b_k realizes β at y exactly when the
threshold of the functions (Σ_k c_ik f b_k)^(e_i), β_i > 0, is at most 1/M at y in the model form
(`isRealizedProfile_iff_modelThresholdBadAt`). Realization is preserved by changes of the tuple
that only add multiples of sections with larger entries of β (`isRealizedProfile_triangular`): the
order of a sum is at least the least order of its terms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Sum

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- At a point with a discrete valuation ring as local ring, a lower bound for the orders of the
nonzero terms of a nonzero sum bounds the order of the sum. -/
theorem le_scheme_ord_sum {ι : Type*} (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (s : Finset ι) (f : ι → X.functionField) (r : ℝ)
    (h : ∀ l ∈ s, f l ≠ 0 → r ≤ (X.ord (f l) x : ℝ)) (hs : ∑ l ∈ s, f l ≠ 0) :
    r ≤ (X.ord (∑ l ∈ s, f l) x : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hs ⊢
    by_cases hfa : f a = 0
    · rw [hfa, zero_add] at hs ⊢
      exact ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) hs
    by_cases hrest : ∑ l ∈ s, f l = 0
    · rw [hrest, add_zero] at hs ⊢
      exact h a (Finset.mem_insert_self a s) hfa
    have h1 := h a (Finset.mem_insert_self a s) hfa
    have h2 := ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) hrest
    have h3 := Scheme.ord_add (x := x) hs
    have h4 : r ≤ ((min (X.ord (f a) x) (X.ord (∑ l ∈ s, f l) x) : ℤ) : ℝ) := by
      rw [Int.cast_min]
      exact le_min h1 h2
    exact h4.trans (by exact_mod_cast h3)

end Sum

section Base

variable {K : Type u} [Field K] {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
  [U.Over (Spec (CommRingCat.of K))]

/-- A nonzero constant has order zero. -/
theorem scheme_ord_algebraMap_base {a : K} (ha : a ≠ 0) (e : U) :
    U.ord (algebraMap K U.functionField a) e = 0 := by
  have : Nonempty (⊤ : U.Opens) := ⟨⟨e, trivial⟩⟩
  have hu : IsUnit (Scheme.Modules.baseRingToGlobalSections K U a) :=
    (isUnit_iff_ne_zero.mpr ha).map _
  have h := Scheme.ord_of_isUnit (X := U) (U := ⊤) hu (x := e) trivial
  exact h

end Base

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

omit [IsIntegral Y] in
theorem stalk_algebraMap_base_eq {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    (y : Y) (a : K) :
    algebraMap (Y.presheaf.stalk y) Y.functionField (algebraMap K (Y.presheaf.stalk y) a) =
      algebraMap K Y.functionField a := by
  rw [IsScalarTower.algebraMap_apply K Γ(Y, ⊤) (Y.presheaf.stalk y),
    ← IsScalarTower.algebraMap_apply Γ(Y, ⊤) (Y.presheaf.stalk y) Y.functionField]
  rfl

/-- The rational function f · s of a section, at a point where f is a local equation. -/
theorem algebraMap_cartierLocalCoefficient_sum_smul (D : CartierDivisor Y) (y : Y)
    (f : Y.functionFieldˣ) (hf : D.IsLocalEquationAt y f) {m : ℕ} (c : Fin m → K)
    (b : Fin m → Γ(D.sheaf, ⊤)) :
    algebraMap (Y.presheaf.stalk y) Y.functionField
        (cartierLocalCoefficient D y f hf (∑ k, c k • b k)) =
      ∑ k, algebraMap K Y.functionField (c k) *
        ((f : Y.functionField) * cartierSectionRational D (b k)) := by
  rw [cartierLocalCoefficient_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, stalk_algebraMap_base_eq, cartierLocalCoefficient_image]

/-- Realization of a nonnegative rational profile by combinations of sections, as a failure of
the threshold of powers of fixed rational functions in the model form. -/
theorem isRealizedProfile_iff_modelThresholdBadAt (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (y : Y) (f : Y.functionFieldˣ)
    (hf : D.IsLocalEquationAt y f) {N m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤)) (β : Fin N → ℚ)
    (hβ : ∀ i, 0 ≤ β i) {M : ℕ} {ex : Fin N → ℕ} (hex1 : ∀ i, 0 < β i → 1 ≤ ex i)
    (hexM : ∀ i, 0 < β i → ((ex i : ℕ) : ℝ) * ((β i : ℚ) : ℝ) = M) (c : Fin N × Fin m → K) :
    IsRealizedProfile cY fY d D₀ D y (fun i => ∑ k, c (i, k) • b k) (fun i => (β i : ℝ)) ↔
      ModelThresholdBadAt cY fY d D₀ y (fun j : {i : Fin N // 0 < β i} =>
        (∑ k, algebraMap K Y.functionField (c (j.1, k)) *
          ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1)) M := by
  classical
  have heval : ∀ j : {i : Fin N // 0 < β i},
      (∑ k, algebraMap K Y.functionField (c (j.1, k)) *
          ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1) =
        (algebraMap (Y.presheaf.stalk y) Y.functionField
          (cartierLocalCoefficient D y f hf (∑ k, c (j.1, k) • b k))) ^ (ex j.1) := by
    intro j
    rw [algebraMap_cartierLocalCoefficient_sum_smul]
  have hne : ∀ j : {i : Fin N // 0 < β i},
      (∑ k, algebraMap K Y.functionField (c (j.1, k)) *
          ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1) ≠ 0 ↔
        (∑ k, c (j.1, k) • b k) ≠ 0 := by
    intro j
    rw [heval, ← cartierLocalCoefficient_ne_zero_iff D y f hf]
    have h0 : ∀ a : Y.presheaf.stalk y,
        algebraMap (Y.presheaf.stalk y) Y.functionField a = 0 ↔ a = 0 := fun a =>
      ⟨fun h => IsFractionRing.injective _ _ (h.trans (map_zero _).symm), fun h => by
        rw [h, map_zero]⟩
    constructor
    · intro h1 h2
      apply h1
      rw [(h0 _).mpr h2, zero_pow (by have := hex1 j.1 j.2; omega)]
    · intro h1 h2
      exact h1 ((h0 _).mp (pow_eq_zero_iff (by have := hex1 j.1 j.2; omega) |>.mp h2))
  have hord : ∀ {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] (σ : U ⟶ Y)
      [IsDominant σ] (e : U) (j : {i : Fin N // 0 < β i}) (hs : (∑ k, c (j.1, k) • b k) ≠ 0),
      U.ord ((dominantFunctionFieldMap σ).hom
        ((∑ k, algebraMap K Y.functionField (c (j.1, k)) *
          ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1))) e =
        (ex j.1 : ℤ) * U.ord ((dominantFunctionFieldMap σ).hom
          (algebraMap (Y.presheaf.stalk y) Y.functionField
            (cartierLocalCoefficient D y f hf (∑ k, c (j.1, k) • b k)))) e := by
    intro U _ _ σ _ e j hs
    have h0 : (dominantFunctionFieldMap σ).hom (algebraMap (Y.presheaf.stalk y) Y.functionField
        (cartierLocalCoefficient D y f hf (∑ k, c (j.1, k) • b k))) ≠ 0 := by
      rw [map_ne_zero_iff _ (dominantFunctionFieldMap σ).hom.injective]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
        ((cartierLocalCoefficient_ne_zero_iff D y f hf _).mpr hs)
    rw [heval, map_pow, scheme_ord_pow h0]
  constructor
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx, hA, hval⟩
    refine ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx, hA, fun j hj => ?_⟩
    have hs := (hne j).mp hj
    have hv := hval j.1 hs
    beta_reduce at hv
    rw [cartierPullback_zeroDivisor_coefficient_eq_ord σ D y f hf _ hs (e : U) hx] at hv
    rw [hord σ (e : U) j hs, ← hexM j.1 j.2]
    push_cast
    have hex0 : (0 : ℝ) ≤ (ex j.1 : ℝ) := Nat.cast_nonneg _
    nlinarith
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx, hA, hval⟩
    refine ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx, hA, fun i hs => ?_⟩
    beta_reduce
    by_cases hβi : 0 < β i
    · have hv := hval ⟨i, hβi⟩ ((hne ⟨i, hβi⟩).mpr hs)
      rw [hord σ (e : U) ⟨i, hβi⟩ hs, ← hexM i hβi] at hv
      rw [cartierPullback_zeroDivisor_coefficient_eq_ord σ D y f hf _ hs (e : U) hx]
      have hex0 : (0 : ℝ) < (ex i : ℝ) := by exact_mod_cast hex1 i hβi
      push_cast at hv
      nlinarith
    · have h0 : β i = 0 := le_antisymm (not_lt.mp hβi) (hβ i)
      rw [h0, Rat.cast_zero, zero_mul]
      exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
        (cartierPullback_isEffective σ _ (cartierSectionZeroDivisor_isEffective _ _ hs)) _

/-- Realization is preserved by changes of the tuple that only add multiples of sections whose
entries of the profile are at least as large. -/
theorem isRealizedProfile_triangular (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (β : Fin N → ℝ)
    (L : Matrix (Fin N) (Fin N) K) (hL : ∀ i l, L i l ≠ 0 → β i ≤ β l)
    (h : IsRealizedProfile cY fY d D₀ D y s β) :
    IsRealizedProfile cY fY d D₀ D y (fun i => ∑ l, L i l • s l) β := by
  classical
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, hval⟩ := h
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, fun i hs => ?_⟩
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : IsDiscreteValuationRing (U.presheaf.stalk (e : U)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) e
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt y
  set A := ((d : ℝ) + cartierCoefficient
    (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d with hAdef
  rw [cartierPullback_zeroDivisor_coefficient_eq_ord σ D y f hf _ hs (e : U) hcl,
    algebraMap_cartierLocalCoefficient_sum_smul, map_sum]
  apply le_scheme_ord_sum (e : U) Finset.univ _ (β i * A) ?_ ?_
  · intro l _ hl
    have hLl : L i l ≠ 0 := by
      intro h0
      apply hl
      rw [h0, map_zero, zero_mul, map_zero]
    have hsl : s l ≠ 0 := by
      intro h0
      apply hl
      rw [h0, map_zero, mul_zero, mul_zero, map_zero]
    have hrat : (dominantFunctionFieldMap σ).hom
        ((f : Y.functionField) * cartierSectionRational D (s l)) ≠ 0 := by
      rw [map_ne_zero_iff _ (dominantFunctionFieldMap σ).hom.injective]
      exact mul_ne_zero (Units.ne_zero f)
        (fun h0 => hsl (cartierSectionRational_injective D (h0.trans (map_zero _).symm)))
    have hconst : (dominantFunctionFieldMap σ).hom (algebraMap K Y.functionField (L i l)) =
        algebraMap K U.functionField (L i l) :=
      (dominantFunctionFieldAlgHom (K := K) σ).commutes (L i l)
    rw [map_mul, Scheme.ord_mul (by rw [hconst]; exact (map_ne_zero _).mpr hLl) hrat, hconst,
      scheme_ord_algebraMap_base hLl, zero_add]
    have hv := hval l hsl
    rw [cartierPullback_zeroDivisor_coefficient_eq_ord σ D y f hf _ hsl (e : U) hcl,
      cartierLocalCoefficient_image] at hv
    have hle : β i * A ≤ β l * A := mul_le_mul_of_nonneg_right (hL i l hLl) hpos.le
    exact hle.trans hv
  · rw [← map_sum, map_ne_zero_iff _ (dominantFunctionFieldMap σ).hom.injective,
      ← algebraMap_cartierLocalCoefficient_sum_smul D y f hf]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      ((cartierLocalCoefficient_ne_zero_iff D y f hf _).mpr hs)

end MixedFujita
