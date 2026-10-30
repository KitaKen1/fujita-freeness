/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GloballyGeneratedKltPerturbation

/-!
Ordinary global generation produces one actual signed SNC boundary perturbation
that simultaneously avoids any finite set of arbitrary scheme points. The new
support, coefficient bounds and all-model klt are proved for this same section.
No system forced to vanish at a prescribed point is asserted here.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- One actual cut supplies the full signed SNC boundary data while avoiding any finite set. -/
theorem cartierIsGloballyGenerated_exists_signed_snc_perturbation_avoiding
    (B H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range ξ →
      cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ))
    (Z : Set X) (hZ : Z.Finite) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι H s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      Function.Injective (Fin.append ξ η) ∧
      (∀ i, Order.coheight (Fin.append ξ η i) = 1) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range (Fin.append ξ η) →
        cartierCoefficient (B + k • cartierSectionZeroDivisor H s hs) (x : X) = 0) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (B + k • cartierSectionZeroDivisor H s hs) (x : X) < (d : ℤ)) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  classical
  obtain ⟨s, hs, q, η, hsm, hηinj, hη, hcover, hsnc', hcoeff, havoid⟩ :=
    cartierIsGloballyGenerated_exists_reduced_prime_snc_avoiding H hH ξ hsnc
      (Z ∪ Set.range ξ) (hZ.union (Set.finite_range ξ))
  have hdis := cartierSection_component_ranges_disjoint H s ξ η hcover
    (fun i => havoid (ξ i) (Or.inr ⟨i, rfl⟩))
  have hinj' : Function.Injective (Fin.append ξ η) :=
    Fin.append_injective_iff.mpr ⟨hinj, hηinj, fun i j h =>
      Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨j, h.symm⟩⟩
  have hprime : ∀ i, Order.coheight (Fin.append ξ η i) = 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hξ j
    · simpa using hη j
  refine ⟨s, hs, q, η, hsm, hinj', hprime, hsnc', ?_,
    cartierSection_signed_perturbation_coefficient_lt B H s hs ξ η hdis hsupport hcoeff d k hk hB,
    fun x hx => havoid x (Or.inl hx)⟩
  intro x hx
  have hold : (x : X) ∉ Set.range ξ := by
    rintro ⟨i, hi⟩
    exact hx ⟨Fin.castAdd q i, by simpa using hi⟩
  have hnew : (x : X) ∉ Set.range η := by
    rintro ⟨j, hj⟩
    exact hx ⟨Fin.natAdd r j, by simpa using hj⟩
  rw [cartierCoefficient_add, cartierCoefficient_nsmul, hsupport x hold, hcoeff x,
    ite_eq_right hnew, mul_zero, add_zero]

variable [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- Finite point avoidance and actual signed all-model klt hold for the same section. -/
theorem cartierIsGloballyGenerated_exists_klt_perturbation_avoiding
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (B H : CartierDivisor X)
    (hH : CartierIsGloballyGenerated H) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range ξ →
      cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ))
    (Z : Set X) (hZ : Z.Finite) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      LogPairIsKlt c f d (d • (smoothCanonicalDivisor c + principalCartierDivisor X f) +
        (B + k • cartierSectionZeroDivisor H s hs)) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  obtain ⟨s, hs, q, η, _, hinj', hprime, hsnc', hsupp, hupper, havoid⟩ :=
    cartierIsGloballyGenerated_exists_signed_snc_perturbation_avoiding B H hH
      ξ hinj hξ hsnc hsupport d k hk hB Z hZ
  exact ⟨s, hs, isSNCFamily_logPairIsKlt c f d (by omega)
    (B + k • cartierSectionZeroDivisor H s hs) (Fin.append ξ η) hinj' hprime hsnc'
    hsupp (fun i => hupper ⟨Fin.append ξ η i, hprime i⟩), havoid⟩

end MixedFujita
