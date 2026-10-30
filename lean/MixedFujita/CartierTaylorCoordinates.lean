/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierLocalCoefficient
public import MixedFujita.FixedCoefficientTaylorLift
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
The actual global Cartier sections map to their actual completed local
coefficients over the base field. A given K-algebra coordinate isomorphism
from the completion to power series then constructs the Taylor linear map;
its injectivity follows from Noetherianity. Local frame changes multiply
the Taylor series by an actual power-series unit and preserve its order.
The existence of the coordinate isomorphism for a smooth K-point is an
unproved geometric input, not a theorem supplied by this module.
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

@[instance_reducible]
noncomputable def cartierBaseGlobalAlgebra (K : Type u) [Field K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] : Algebra K Γ(X, ⊤) :=
  (Scheme.Modules.baseRingToGlobalSections K X).toAlgebra

attribute [local instance] cartierBaseGlobalAlgebra

@[instance_reducible]
noncomputable def cartierBaseLocalAlgebra (K : Type u) [Field K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((algebraMap Γ(X, ⊤) (X.presheaf.stalk x)).comp
    (Scheme.Modules.baseRingToGlobalSections K X)).toAlgebra

attribute [local instance] cartierBaseLocalAlgebra

omit [IsIntegral X] in
theorem cartierBaseLocalScalarTower (x : X) :
    IsScalarTower K Γ(X, ⊤) (X.presheaf.stalk x) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem cartierBaseSectionScalarTower (D : CartierDivisor X) :
    IsScalarTower K Γ(X, ⊤) Γ(D.sheaf, ⊤) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] cartierBaseLocalScalarTower cartierBaseSectionScalarTower

noncomputable def cartierBaseCompletedCoefficient (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    Γ(D.sheaf, ⊤) →ₗ[K]
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  (cartierCompletedLocalCoefficient D x f hf).restrictScalars K

noncomputable def cartierTaylorCoordinates {n : ℕ} (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    Γ(D.sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin n) K :=
  coordinates.toLinearMap.comp (cartierBaseCompletedCoefficient D x f hf)

theorem cartierTaylorCoordinates_apply {n : ℕ} (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (s : Γ(D.sheaf, ⊤)) :
    cartierTaylorCoordinates D x f hf coordinates s =
      coordinates (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) (cartierLocalCoefficient D x f hf s)) := rfl

theorem cartierTaylorCoordinates_injective {n : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    Function.Injective (cartierTaylorCoordinates D x f hf coordinates) :=
  coordinates.injective.comp (cartierCompletedLocalCoefficient_injective D x f hf)

theorem cartierTaylorCoordinates_ne_zero_iff {n : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (s : Γ(D.sheaf, ⊤)) :
    cartierTaylorCoordinates D x f hf coordinates s ≠ 0 ↔ s ≠ 0 :=
  map_ne_zero_iff _ (cartierTaylorCoordinates_injective D x f hf coordinates)

theorem cartierTaylorCoordinates_change_frame {n : ℕ} (D : CartierDivisor X)
    (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    ∃ v : (MvPowerSeries (Fin n) K)ˣ, ∀ s : Γ(D.sheaf, ⊤),
      cartierTaylorCoordinates D x f hf coordinates s =
        (v : MvPowerSeries (Fin n) K) * cartierTaylorCoordinates D x g hg coordinates s := by
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x f g hf hg
  refine ⟨Units.map (coordinates.toMonoidHom.comp
    (algebraMap (X.presheaf.stalk x) (AdicCompletion
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).toMonoidHom) v,
    fun s => ?_⟩
  rw [cartierTaylorCoordinates_apply, hv s, map_mul, map_mul, cartierTaylorCoordinates_apply]
  rfl

omit [X.Over (Spec (CommRingCat.of K))] [IsIntegral X] in
theorem powerSeries_order_unit_mul {σ : Type*} (v : (MvPowerSeries σ K)ˣ)
    (φ : MvPowerSeries σ K) : ((v : MvPowerSeries σ K) * φ).order = φ.order := by
  have lower (u : (MvPowerSeries σ K)ˣ) (ψ : MvPowerSeries σ K) :
      ψ.order ≤ ((u : MvPowerSeries σ K) * ψ).order := by
    calc
      ψ.order = 0 + ψ.order := (zero_add _).symm
      _ ≤ (u : MvPowerSeries σ K).order + ψ.order := add_le_add zero_le le_rfl
      _ ≤ _ := MvPowerSeries.le_order_mul
  apply le_antisymm
  · have hv' : ((v⁻¹ : (MvPowerSeries σ K)ˣ) : MvPowerSeries σ K) *
        (v : MvPowerSeries σ K) = 1 := Units.inv_mul v
    simpa only [← mul_assoc, hv', one_mul] using lower v⁻¹ ((v : MvPowerSeries σ K) * φ)
  · exact lower v φ

theorem cartierTaylorCoordinates_order_change_frame {n : ℕ} (D : CartierDivisor X)
    (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (s : Γ(D.sheaf, ⊤)) :
    (cartierTaylorCoordinates D x f hf coordinates s).order =
      (cartierTaylorCoordinates D x g hg coordinates s).order := by
  obtain ⟨v, hv⟩ := cartierTaylorCoordinates_change_frame D x f g hf hg coordinates
  rw [hv s, powerSeries_order_unit_mul]

theorem fixedCoefficientCartierZeroDivisor {n : ℕ} {ι : Type u}
    (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (d : ℕ) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → Γ(D.sheaf, ⊤)) (a : ι → K) {t : K} (ht : t ≠ 0)
    (hs : ∀ l ∈ I, (d : ℕ∞) ≤ (cartierTaylorCoordinates D x f hf coordinates (s l)).order)
    (hw : ∀ l ∈ I, ∀ q ∈ (taylorLeadingLinearMap d
      (cartierTaylorCoordinates D x f hf coordinates) (s l)).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (hF : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d
        (cartierTaylorCoordinates D x f hf coordinates) (s l)) a) ≠ 0) :
    ∃ hn : correctedTaylorCombination I w p s a t ≠ 0,
      (cartierSectionZeroDivisor D (correctedTaylorCombination I w p s a t) hn).IsEffective ∧
      cartierSectionZeroDivisor D (correctedTaylorCombination I w p s a t) hn - D =
        principalCartierDivisor X
          (cartierSectionUnit D (correctedTaylorCombination I w p s a t) hn) ∧
      (cartierTaylorCoordinates D x f hf coordinates
        (correctedTaylorCombination I w p s a t)).order = (d : ℕ∞) := by
  obtain ⟨ho, hn, _, _⟩ := fixedCoefficientTaylorCombination_exact_order d
    (cartierTaylorCoordinates D x f hf coordinates) I w p s a ht hs hw hF
  exact ⟨hn, cartierSectionZeroDivisor_isEffective D _ hn,
    cartierSectionZeroDivisor_sub D _ hn, ho⟩

end MixedFujita
