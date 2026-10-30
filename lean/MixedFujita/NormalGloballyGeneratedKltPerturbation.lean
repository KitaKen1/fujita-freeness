/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalSNCBoundaryKlt
public import MixedFujita.CartierGloballyGeneratedBoundaryPerturbation

/-!
Ordinary global generation now supplies an actual reduced SNC section and an
all-model klt perturbation. The source is smooth and its stalk normality remains
explicit. No finite linear system, local boundary product, geometric Jacobian
bound or klt conclusion is supplied as an input. The signed version accommodates
crepant boundaries; constructing the resolution and comparing the crepant pair
with a singular source are separate.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- An ordinarily globally generated divisor supplies an actual SNC perturbation
whose signed boundary is klt on every proper smooth birational model. -/
theorem normal_cartierIsGloballyGenerated_exists_klt_perturbation
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (B D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) ∧
      LogPairIsKlt c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) := by
  classical
  obtain ⟨s, hs, q, η, hη, hηinj, hsm, hcover, hsnc', havoid, hdis, hWeil,
    hcoeff, hinterval, hsigned⟩ :=
    cartierIsGloballyGenerated_exists_boundary_compatible_perturbation B D hD ξ hsnc hsupport
  have hinj' : Function.Injective (Fin.append ξ η) :=
    Fin.append_injective_iff.mpr ⟨hinj, hηinj, fun i j h =>
      Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨j, h.symm⟩⟩
  have hprime : ∀ i, Order.coheight (Fin.append ξ η i) = 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hξ j
    · simpa using hη j
  have hsupp' : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range (Fin.append ξ η) →
        cartierCoefficient (B + k • cartierSectionZeroDivisor D s hs) (x : X) = 0 := by
    intro x hx
    have hold : (x : X) ∉ Set.range ξ := by
      rintro ⟨i, hi⟩
      exact hx ⟨Fin.castAdd q i, by simpa using hi⟩
    have hnew : (x : X) ∉ Set.range η := by
      rintro ⟨j, hj⟩
      exact hx ⟨Fin.natAdd r j, by simpa using hj⟩
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, hsupport x hold, hcoeff x,
      ite_eq_right hnew, mul_zero, add_zero]
  have hupper := cartierSection_signed_perturbation_coefficient_lt B D s hs ξ η hdis
    hsupport hcoeff d k hk hB
  exact ⟨s, hs, q, η, hsm, hsnc', hcoeff,
    normal_isSNCFamily_logPairIsKlt hnorm c₀ f₀ d (by omega)
      (B + k • cartierSectionZeroDivisor D s hs) (Fin.append ξ η) hinj' hprime hsnc'
      hsupp' (fun i => hupper ⟨Fin.append ξ η i, hprime i⟩)⟩

/-- With effective old coefficients the same construction gives an effective all-model klt pair. -/
theorem normal_cartierIsGloballyGenerated_exists_effective_klt_perturbation
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (B D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
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
      LogPairIsKlt c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) := by
  obtain ⟨s, hs, q, η, hsm, hsnc', hcoeff, hklt⟩ :=
    normal_cartierIsGloballyGenerated_exists_klt_perturbation hnorm c₀ f₀ B D hD ξ hinj hξ
      hsnc hsupport d k hk (fun x => (hB x).2)
  exact ⟨s, hs, q, η, hsm, hsnc',
    cartierSection_perturbation_logPairBoundaryEffective c₀ f₀ d B D s hs η hcoeff
      (fun x => (hB x).1) k, hklt⟩

end MixedFujita
