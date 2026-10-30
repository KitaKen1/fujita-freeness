/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierInitialBasis

/-!
Choose actual nonzero Cartier sections realizing specified members of the
actual initial-exponent set, then construct the tau-normalized products.
Thus the equality-case product no longer needs a supplied family of
sections with a stipulated initial-exponent property. A verified rational
slice certificate, given completion coordinates and finite dimensionality
are still needed; their geometric existence and lifting remain unfinished.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

variable (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
  [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]

noncomputable def cartierExponentSections {n : ℕ} {ι : Type*}
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (i : ι) : Γ((j • A).sheaf, ⊤) := by
  classical
  exact if hi : i ∈ E then cartierInitialSection A x f hf m coordinates j (p i) (hp i hi)
    else 0

theorem cartierExponentSections_spec {n : ℕ} {ι : Type*}
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (i : ι) (hi : i ∈ E) :
    IsInitialMonomial m (cartierTaylorCoordinates (j • A) x (f ^ j)
      (cartierLocalEquation_pow A x f hf j) coordinates
      (cartierExponentSections A x f hf m coordinates j E p hp i)) (p i) := by
  classical
  simp only [cartierExponentSections, dite_eq_left hi]
  exact cartierInitialSection_spec A x f hf m coordinates j (p i) (hp i hi)

theorem cartierExponentSections_ne_zero {n : ℕ} {ι : Type*}
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (i : ι) (hi : i ∈ E) :
    cartierExponentSections A x f hf m coordinates j E p hp i ≠ 0 := by
  classical
  simp only [cartierExponentSections, dite_eq_left hi]
  exact cartierInitialSection_ne_zero A x f hf m coordinates j (p i) (hp i hi)

noncomputable def cartierExponentTauProduct {n : ℕ} {ι L : Type*} [Fintype L]
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (q : L → ι → ℚ≥0) (r a : ℕ) (l : L) (hq : (∑ i ∈ E, q l i) = 1) :
    Γ((equalitySectionDegree r j (sharedRationalDenominator E q) a • A).sheaf, ⊤) :=
  equalityCartierProduct E q A j r a l hq
    (cartierExponentSections A x f hf m coordinates j E p hp)

theorem cartierExponentTauProduct_ne_zero {n : ℕ} {ι L : Type*} [Fintype L]
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (q : L → ι → ℚ≥0) (r a : ℕ) (l : L) (hq : (∑ i ∈ E, q l i) = 1) :
    cartierExponentTauProduct A x f hf m coordinates j E p hp q r a l hq ≠ 0 :=
  equalityCartierProduct_ne_zero E q A j r a l hq _
    (cartierExponentSections_ne_zero A x f hf m coordinates j E p hp)

theorem cartierExponentTauProduct_initialMonomial {n : ℕ} {ι L : Type*} [Fintype L]
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (q : L → ι → ℚ≥0) (r a : ℕ) (l : L) (hq : (∑ i ∈ E, q l i) = 1) :
    IsInitialMonomial m (cartierTaylorCoordinates _ x
      (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
      (cartierLocalEquation_pow A x f hf _) coordinates
      (cartierExponentTauProduct A x f hf m coordinates j E p hp q r a l hq))
      ((r * a) • ∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) :=
  equalityCartierProduct_initialMonomial E q A j r a l hq x f hf coordinates _ p m
    (cartierExponentSections_spec A x f hf m coordinates j E p hp)

theorem cartierExponentTauProduct_isEffective {n : ℕ} {ι L : Type*} [Fintype L]
    (m : MonomialOrder (Fin n))
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (j : ℕ) (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf m coordinates j)
    (q : L → ι → ℚ≥0) (r a : ℕ) (l : L) (hq : (∑ i ∈ E, q l i) = 1) :
    (cartierSectionZeroDivisor _
      (cartierExponentTauProduct A x f hf m coordinates j E p hp q r a l hq)
      (cartierExponentTauProduct_ne_zero A x f hf m coordinates j E p hp q r a l hq)).IsEffective :=
  cartierSectionZeroDivisor_isEffective _ _ _

theorem cartierExponentTauProduct_slice_data {n : ℕ} {ι L : Type*} [Fintype L]
    [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    {j r a b : ℕ} (E : Finset ι) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ i ∈ E, p i ∈ cartierGradedInitialExponents A x f hf
      (MonomialOrder.degLex (σ := Fin n)) coordinates j)
    (q : L → ι → ℚ≥0) (l : L) (hq : (∑ i ∈ E, q l i) = 1)
    (β : Fin n →₀ ℕ) (hβ : (∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) = β)
    {δ : ℚ} (k v : Fin n) (hr : 0 < r) (hj : 0 < j) (ha : 0 < a) (hb : 0 < b)
    (hslice : ∀ i, (β i : ℚ) / ((sharedRationalDenominator E q : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k v i) :
    ∃ hs : cartierExponentTauProduct A x f hf (MonomialOrder.degLex (σ := Fin n))
        coordinates j E p hp q r a l hq ≠ 0,
      (cartierSectionZeroDivisor _
        (cartierExponentTauProduct A x f hf (MonomialOrder.degLex (σ := Fin n))
          coordinates j E p hp q r a l hq) hs).IsEffective ∧
      cartierSectionVanishingOrder _ x
        (cartierExponentTauProduct A x f hf (MonomialOrder.degLex (σ := Fin n))
          coordinates j E p hp q r a l hq) =
            (n * equalityHeight r j (sharedRationalDenominator E q) b : ℕ) ∧
      (cartierTaylorCoordinates _ x
        (f ^ equalitySectionDegree r j (sharedRationalDenominator E q) a)
        (cartierLocalEquation_pow A x f hf _) coordinates
        (cartierExponentTauProduct A x f hf (MonomialOrder.degLex (σ := Fin n))
          coordinates j E p hp q r a l hq)).order =
            (n * equalityHeight r j (sharedRationalDenominator E q) b : ℕ) := by
  refine ⟨cartierExponentTauProduct_ne_zero A x f hf _ coordinates j E p hp q r a l hq,
    cartierSectionZeroDivisor_isEffective _ _ _, ?_, ?_⟩
  · exact equalityCartierProduct_slice_vanishingOrder E q A l hq x f hf coordinates _ p
      (cartierExponentSections_spec A x f hf _ coordinates j E p hp)
      β hβ k v hr hj ha hb hslice
  · exact equalityCartierProduct_slice_order E q A l hq x f hf coordinates _ p
      (cartierExponentSections_spec A x f hf _ coordinates j E p hp)
      β hβ k v hr hj ha hb hslice

end MixedFujita
