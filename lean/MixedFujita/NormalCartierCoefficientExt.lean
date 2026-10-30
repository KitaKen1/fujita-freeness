/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FloorDivisorLifting
public import MixedFujita.PointClosureHyperplaneEquivalence

/-!
On a normal scheme a Cartier divisor is determined by its coefficients (step 12).

Let X be a normal locally Noetherian integral scheme. Two Cartier divisors with the same
coefficient at every codimension-one point are equal: local equations at a point t have equal
orders at the codimension-one points near t, so their ratio and its inverse are regular at t by
Hartogs, and a unit of the local ring times a local equation is a local equation. In particular a
Cartier divisor whose coefficients vanish outside a family of distinct prime divisors ξ_k with
member divisors E_k is the integral combination Σ (coefficient at ξ_k) E_k.
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

attribute [local instance] Classical.propDecidable

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a normal scheme two Cartier divisors with the same coefficients are equal. -/
theorem cartierDivisor_eq_of_forall_coefficient_eq
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D E : CartierDivisor X)
    (h : ∀ z : CodimensionOnePoint X,
      cartierCoefficient D (z : X) = cartierCoefficient E (z : X)) : D = E := by
  have hdvr : ∀ z : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := fun z => by
    let := hnorm (z : X)
    exact normal_codimensionOne_stalk_DVR z
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt t
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt t
  obtain ⟨V, htV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  obtain ⟨V', htV', hV'⟩ := CartierDivisor.isLocalEquationAt_iff.mp hg
  have : Nonempty V := ⟨⟨t, htV⟩⟩
  have : Nonempty V' := ⟨⟨t, htV'⟩⟩
  obtain ⟨u, hu⟩ := normal_scheme_equal_orders_unit_ratio hnorm t (V ⊓ V') ⟨htV, htV'⟩ f g (by
    intro z hz
    rw [← cartierCoefficient_eq_ord
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV hz.1),
      ← cartierCoefficient_eq_ord
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV' hz.2)]
    exact h z)
  exact ⟨f, hf, isLocalEquationAt_stalkUnit_mul hg u hu⟩

/-- On a normal scheme a Cartier divisor whose coefficients vanish outside a family of distinct
prime divisors is the integral combination of the member divisors with its coefficients. -/
theorem cartierDivisor_eq_member_combination
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (E : Fin r → CartierDivisor X)
    (hEc : ∀ (i : Fin r) (z : CodimensionOnePoint X),
      cartierCoefficient (E i) (z : X) = if (z : X) = ξ i then 1 else 0)
    (D : CartierDivisor X)
    (hD : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient D (z : X) = 0) :
    D = ∑ k, cartierCoefficient D (ξ k) • E k := by
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm
  intro z
  rcases cartierCoefficient_member_combination ξ hinj E hEc (fun k => cartierCoefficient D (ξ k))
    z with ⟨k, hzk, hco⟩ | ⟨hz, hco⟩
  · rw [hco, hzk]
  · rw [hco]
    exact hD z hz

end MixedFujita
