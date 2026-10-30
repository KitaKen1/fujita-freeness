/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionSNCPerturbation

/-!
The actual effective zero Cartier divisor is the sum of the distinct prime components with
coefficient one, as an actual Weil divisor. This converts the enumerated geometric family
and the coefficient indicator into a divisor identity usable by perturbation arguments.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The project-local Cartier coefficient agrees with the actual Weil-divisor coefficient. -/
theorem cartier_toWeilDivisor_coeff_eq_cartierCoefficient (D : CartierDivisor X)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff D.toWeilDivisor x = cartierCoefficient D (x : X) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (x : X)
  rw [CartierDivisor.coeff_toWeilDivisor,
    cartier_orderAt_eq_scheme_ord_of_localEquation D x f hf,
    cartierCoefficient_eq_ord hf]

/-- The exact reduced prime decomposition of an actual zero Cartier divisor. -/
theorem cartierSectionZeroDivisor_toWeil_eq_sum_components
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {q : ℕ} (η : Fin q → X) (hinj : Function.Injective η)
    (hη : ∀ j, Order.coheight (η j) = 1)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0) :
    (cartierSectionZeroDivisor D s hs).toWeilDivisor =
      ∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X) := by
  classical
  apply WeilDivisor.ext
  intro x
  rw [cartier_toWeilDivisor_coeff_eq_cartierCoefficient, hcoeff]
  change (if (x : X) ∈ Set.range η then 1 else 0) =
    (∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X)) x
  rw [Finsupp.finsetSum_apply]
  by_cases hx : (x : X) ∈ Set.range η
  · rw [ite_eq_left hx]
    obtain ⟨j, hj⟩ := hx
    have hxj : (⟨η j, hη j⟩ : CodimensionOnePoint X) = x := Subtype.ext hj
    symm
    rw [Finset.sum_eq_single j]
    · rw [hxj]
      exact WeilDivisor.coeff_ofPoint_self x
    · intro k hk hkj
      apply WeilDivisor.coeff_ofPoint_of_ne
      intro heq
      apply hkj
      exact hinj ((congrArg Subtype.val heq).symm.trans hj.symm)
    · simp
  · rw [ite_eq_right hx]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply WeilDivisor.coeff_ofPoint_of_ne
    intro heq
    apply hx
    exact ⟨j, (congrArg Subtype.val heq).symm⟩

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- A base-point-free finite system actually supplies a nonzero reduced prime SNC divisor,
including its full Weil-divisor decomposition and the coefficient formula for perturbation. -/
theorem cartierSections_exists_reduced_prime_snc_divisor [CharZero K]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) :
    ∃ (t : ι → K) (hst : (∑ i, t i • s i) ≠ 0) (q : ℕ) (η : Fin q → X)
      (hη : ∀ j, Order.coheight (η j) = 1),
      Function.Injective η ∧
      Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
        (X ↘ Spec (CommRingCat.of K))) ∧
      cartierSectionZeroLocus D (∑ i, t i • s i) = ⋃ j, closure ({η j} : Set X) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (cartierSectionZeroDivisor D (∑ i, t i • s i) hst).toWeilDivisor =
        ∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D (∑ i, t i • s i) hst) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) := by
  obtain ⟨p, hp, ⟨t, ht⟩, hgood⟩ := cartierSections_general_reduced_prime_snc D s hs ξ hξ
  obtain ⟨hst, q, η, hsm, hinj, hη, hrange, hcover, hdis, hsnc, hcoeff⟩ := hgood t ht
  exact ⟨t, hst, q, η, hη, hinj, hsm, hcover, hsnc,
    cartierSectionZeroDivisor_toWeil_eq_sum_components D _ hst η hinj hη hcoeff, hcoeff⟩

end MixedFujita
