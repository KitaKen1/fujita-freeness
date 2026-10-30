/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalGenerationFiniteFamily
public import MixedFujita.CartierSectionBoundaryCoefficients

/-!
Ordinary global generation, rather than a separately supplied finite linear system, now
constructs actual reduced SNC cuts avoiding a finite set. For an old boundary supported
on an SNC family, a single actual section provides its prime decomposition and all
normalized coefficient bounds, including signed old boundaries. The compactness shortcut
does not assume finite-dimensionality of the full global-section space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [IsNoetherian X]

/-- Usual global generation gives an actual smooth reduced SNC section avoiding any finite set. -/
theorem cartierIsGloballyGenerated_exists_reduced_prime_snc_avoiding
    (D : CartierDivisor X) (hD : CartierIsGloballyGenerated D) {n r : ℕ}
    (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) (Z : Set X) (hZ : Z.Finite) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      Function.Injective η ∧ (∀ j, Order.coheight (η j) = 1) ∧
      cartierSectionZeroLocus D s = ⋃ j, closure ({η j} : Set X) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus D s) := by
  classical
  obtain ⟨m, v, hv⟩ := cartierIsGloballyGenerated_exists_fin_basePointFree D hD
  obtain ⟨p, hp, ⟨t, ht⟩, hgood⟩ :=
    cartierSections_general_reduced_prime_snc_avoiding D v hv ξ hξ Z hZ
  obtain ⟨hs, q, η, hsm, hinj, hη, hcover, hsnc, hcoeff, havoid⟩ := hgood t ht
  exact ⟨∑ i, t i • v i, hs, q, η, hsm, hinj, hη, hcover, hsnc, hcoeff, havoid⟩

/-- One actual cut from an ordinarily globally generated divisor supplies both effective and
signed normalized boundary bounds. No finite family or H⁰ finiteness is a supplied hypothesis. -/
theorem cartierIsGloballyGenerated_exists_boundary_compatible_perturbation
    (B D : CartierDivisor X) (hD : CartierIsGloballyGenerated D) {n r : ℕ}
    (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X)
      (hη : ∀ j, Order.coheight (η j) = 1),
      Function.Injective η ∧
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      cartierSectionZeroLocus D s = ⋃ j, closure ({η j} : Set X) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ i, ξ i ∉ cartierSectionZeroLocus D s) ∧
      Disjoint (Set.range ξ) (Set.range η) ∧
      (cartierSectionZeroDivisor D s hs).toWeilDivisor =
        ∑ j, WeilDivisor.ofPoint (⟨η j, hη j⟩ : CodimensionOnePoint X) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) ∧
      (∀ (d k : ℕ), k < d →
        (∀ x : CodimensionOnePoint X,
          0 ≤ cartierCoefficient B (x : X) ∧ cartierCoefficient B (x : X) < (d : ℤ)) →
        ∀ x : CodimensionOnePoint X,
          0 ≤ (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d ∧
          (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d < 1) ∧
      (∀ (d k : ℕ), k < d →
        (∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) →
        ∀ x : CodimensionOnePoint X,
          (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d < 1) := by
  classical
  obtain ⟨m, v, hv⟩ := cartierIsGloballyGenerated_exists_fin_basePointFree D hD
  obtain ⟨t, hs, q, η, hη, hinj, hsm, hcover, hsnc, havoid, hdis, hWeil, hcoeff, hbounds⟩ :=
    cartierSections_exists_boundary_compatible_perturbation B D v hv ξ hξ hsupport
  refine ⟨∑ i, t i • v i, hs, q, η, hη, hinj, hsm, hcover, hsnc, havoid, hdis,
    hWeil, hcoeff, ?_, ?_⟩
  · intro d k hk hB
    exact cartierSection_perturbation_rational_coefficient_bounds B D _ hs ξ η
      hdis hsupport hcoeff d k hk hB
  · intro d k hk hB
    exact cartierSection_signed_perturbation_rational_coefficient_lt_one B D _ hs ξ η
      hdis hsupport hcoeff d k hk hB

/-- Ordinary global generation also supplies an actual effective perturbed log-pair
presentation on a smooth scheme, with all normalized ambient boundary coefficients in [0,1). -/
theorem cartierIsGloballyGenerated_exists_effective_logPair_perturbation
    {n r : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (B D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X,
      0 ≤ cartierCoefficient B (x : X) ∧ cartierCoefficient B (x : X) < (d : ℤ)) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      LogPairBoundaryEffective c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) ∧
      (∀ x : CodimensionOnePoint X,
        0 ≤ (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d ∧
        (cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) : ℚ) / d < 1) := by
  obtain ⟨s, hs, q, η, hη, hinj, hsm, hcover, hsnc, havoid, hdis, hWeil,
    hcoeff, hinterval, hsigned⟩ :=
    cartierIsGloballyGenerated_exists_boundary_compatible_perturbation B D hD ξ hξ hsupport
  exact ⟨s, hs, q, η, hsm, hsnc,
    cartierSection_perturbation_logPairBoundaryEffective c₀ f₀ d B D s hs η hcoeff
      (fun x => (hB x).1) k,
    hinterval d k hk hB⟩

end MixedFujita
