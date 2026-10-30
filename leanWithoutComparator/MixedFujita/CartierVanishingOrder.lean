/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierTaylorCoordinates
public import MixedFujita.LocalAdicOrder

/-!
Construct the intrinsic maximal-ideal vanishing order of an actual global
Cartier section, independently of its chosen local equation. For any given
completion-coordinate K-algebra isomorphism, its actual Taylor order equals
this intrinsic order and is independent of the coordinate choice. Nonzero
sections have finite order at Noetherian stalks. The actual effective zero
divisor has an actual regular local equation with this same order. The
fixed-coefficient construction now supplies the precise membership in
m^d and nonmembership in m^(d+1) of that regular local equation.
Smooth coordinate existence, Hilbert-Samuel multiplicity, blow-up strict
transforms and exceptional-divisor restriction are not proved here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierSectionVanishingOrder (D : CartierDivisor X)
    (x : X) (s : Γ(D.sheaf, ⊤)) : ℕ∞ :=
  localAdicOrder (X.presheaf.stalk x) (cartierLocalCoefficient D x
    (Classical.choose (D.exists_isLocalEquationAt x))
    (Classical.choose_spec (D.exists_isLocalEquationAt x)) s)

theorem cartierSectionVanishingOrder_eq_localCoefficient (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s =
      localAdicOrder (X.presheaf.stalk x) (cartierLocalCoefficient D x f hf s) := by
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x
    (Classical.choose (D.exists_isLocalEquationAt x)) f
    (Classical.choose_spec (D.exists_isLocalEquationAt x)) hf
  change localAdicOrder _ _ = _
  rw [hv s, localAdicOrder_unit_mul]

theorem cartierSectionVanishingOrder_nat_le_iff (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (d : ℕ) :
    (d : ℕ∞) ≤ cartierSectionVanishingOrder D x s ↔
      cartierLocalCoefficient D x f hf s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ d := by
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    localAdicOrder_nat_le_iff]

theorem cartierSectionVanishingOrder_eq_nat_iff (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (d : ℕ) :
    cartierSectionVanishingOrder D x s = (d : ℕ∞) ↔
      cartierLocalCoefficient D x f hf s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ d ∧
      cartierLocalCoefficient D x f hf s ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (d + 1) := by
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    localAdicOrder_eq_nat_iff]

theorem cartierSectionVanishingOrder_eq_top_iff (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)] (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s = ⊤ ↔ s = 0 := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf, localAdicOrder_eq_top_iff]
  exact map_eq_zero_iff _ (cartierLocalCoefficient_injective D x f hf)

theorem cartierSectionVanishingOrder_lt_top_iff (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)] (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s < ⊤ ↔ s ≠ 0 := by
  rw [lt_top_iff_ne_top, ne_eq, cartierSectionVanishingOrder_eq_top_iff]

theorem cartierSectionZeroDivisor_regular_localEquation (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ r : X.presheaf.stalk x, r ≠ 0 ∧
      algebraMap (X.presheaf.stalk x) X.functionField r =
        ((f * cartierSectionUnit D s hs : X.functionFieldˣ) : X.functionField) ∧
      (cartierSectionZeroDivisor D s hs).IsLocalEquationAt x (f * cartierSectionUnit D s hs) ∧
      localAdicOrder (X.presheaf.stalk x) r = cartierSectionVanishingOrder D x s := by
  refine ⟨cartierLocalCoefficient D x f hf s,
    (cartierLocalCoefficient_ne_zero_iff D x f hf s).mpr hs, ?_,
    cartierSectionZeroDivisor_localEquation D s hs x f hf,
    (cartierSectionVanishingOrder_eq_localCoefficient D x f hf s).symm⟩
  simpa only [Units.val_mul, cartierSectionUnit_val] using
    cartierLocalCoefficient_image D x f hf s

section Coordinates

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem cartierTaylorCoordinates_order_eq_vanishingOrder {n : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (s : Γ(D.sheaf, ⊤)) :
    (cartierTaylorCoordinates D x f hf coordinates s).order =
      cartierSectionVanishingOrder D x s := by
  rw [cartierTaylorCoordinates_apply, cartierSectionVanishingOrder_eq_localCoefficient D x f hf]
  exact completionCoordinates_order_eq_localAdicOrder coordinates.toRingEquiv _

theorem cartierTaylorCoordinates_order_change_coordinates {n m : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f g : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (coordinates' : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin m) K) (s : Γ(D.sheaf, ⊤)) :
    (cartierTaylorCoordinates D x f hf coordinates s).order =
      (cartierTaylorCoordinates D x g hg coordinates' s).order := by
  rw [cartierTaylorCoordinates_order_eq_vanishingOrder,
    cartierTaylorCoordinates_order_eq_vanishingOrder]

theorem cartierTaylorCoordinates_nat_le_order_iff {n : ℕ} (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (s : Γ(D.sheaf, ⊤)) (d : ℕ) :
    (d : ℕ∞) ≤ (cartierTaylorCoordinates D x f hf coordinates s).order ↔
      cartierLocalCoefficient D x f hf s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ d := by
  rw [cartierTaylorCoordinates_order_eq_vanishingOrder,
    cartierSectionVanishingOrder_nat_le_iff D x f hf]

theorem fixedCoefficientCartierVanishingOrder {n : ℕ} {ι : Type u}
    (D : CartierDivisor X) (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
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
      cartierSectionVanishingOrder D x (correctedTaylorCombination I w p s a t) = (d : ℕ∞) ∧
      cartierLocalCoefficient D x f hf (correctedTaylorCombination I w p s a t) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ d ∧
      cartierLocalCoefficient D x f hf (correctedTaylorCombination I w p s a t) ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (d + 1) := by
  obtain ⟨hn, heff, _, ho⟩ := fixedCoefficientCartierZeroDivisor
    D x f hf coordinates d I w p s a ht hs hw hF
  rw [cartierTaylorCoordinates_order_eq_vanishingOrder] at ho
  obtain ⟨hm, hnext⟩ := (cartierSectionVanishingOrder_eq_nat_iff
    D x f hf _ d).mp ho
  exact ⟨hn, heff, ho, hm, hnext⟩

end Coordinates

end MixedFujita
