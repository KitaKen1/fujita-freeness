/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SemiampleIitakaZero

/-!
Global generation with at most one independent section makes an actual Cartier divisor
principal. This argument needs neither projectivity nor algebraic closedness. Finite
dimensionality is explicit: a finite `finrank` alone would not exclude an infinite-dimensional
section space. Two consecutive principal multiples then make the divisor itself principal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- A globally generated divisor with a finite section space of dimension at most one is
principal, without projectivity or algebraic closedness. -/
theorem principal_of_globallyGenerated_of_finrank_le_one (D : CartierDivisor X)
    [FiniteDimensional K Γ(D.sheaf, ⊤)] (hgg : CartierIsGloballyGenerated D)
    (hle : Module.finrank K Γ(D.sheaf, ⊤) ≤ 1) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  classical
  obtain ⟨s₀, hs₀⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgg
  have hspan : Submodule.span K {s₀} = ⊤ := by
    have h1 : Module.finrank K (Submodule.span K {s₀}) = 1 := finrank_span_singleton hs₀
    have h2 : Module.finrank K Γ(D.sheaf, ⊤) = 1 :=
      le_antisymm hle (h1 ▸ Submodule.finrank_le _)
    apply Submodule.eq_top_of_finrank_eq
    rw [h1, h2]
  have hmul : ∀ s : Γ(D.sheaf, ⊤), ∃ c : K, c • s₀ = s := fun s =>
    Submodule.mem_span_singleton.mp (hspan ▸ Submodule.mem_top)
  have hunit : ∀ (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
      IsUnit (cartierLocalCoefficient D x f hf s₀) := by
    intro x f hf
    obtain ⟨s, hs⟩ := hgg x
    obtain ⟨c, rfl⟩ := hmul s
    rw [cartierLocalCoefficient_smul_base] at hs
    have hu := isUnit_of_mul_isUnit_right hs
    obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x f _ hf
      (Classical.choose_spec (D.exists_isLocalEquationAt x))
    rw [hv s₀]
    exact v.isUnit.mul hu
  refine ⟨(cartierSectionUnit D s₀ hs₀)⁻¹, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  refine ⟨(cartierSectionUnit D s₀ hs₀)⁻¹, ?_,
    CartierDivisor.isLocalEquationAt_principalCartierDivisor x _⟩
  refine isLocalEquationAt_of_eq_unit_mul hf (hunit x f hf).unit ?_
  have hr : cartierSectionRational D s₀ ≠ 0 := fun h => hs₀
    (cartierSectionRational_injective _ (h.trans (map_zero _).symm))
  rw [IsUnit.unit_spec, cartierLocalCoefficient_image, Units.val_inv_eq_inv_val,
    cartierSectionUnit_val, mul_assoc, mul_inv_cancel₀ hr, mul_one]

omit [X.Over (Spec (CommRingCat.of K))] in
/-- Consecutive principal multiples make the divisor itself principal. -/
theorem principal_of_consecutive_multiples (D : CartierDivisor X) (q : ℕ)
    (hq : ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ)
    (hq1 : ∃ φ : X.functionFieldˣ, (q + 1) • D = principalCartierDivisor X φ) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  obtain ⟨φ₀, h₀⟩ := hq
  obtain ⟨φ₁, h₁⟩ := hq1
  refine ⟨φ₁ * φ₀⁻¹, ?_⟩
  have hD : D = (q + 1) • D - q • D := by
    rw [add_nsmul, one_nsmul]
    abel
  rw [hD, h₁, h₀, principalCartierDivisor_mul, principalCartierDivisor_inv]
  abel

/-- If all sufficiently large integer multiples are globally generated and have finite section
spaces of dimension at most one, the divisor itself is principal. -/
theorem principal_of_eventually_globallyGenerated_of_finrank_le_one (D : CartierDivisor X)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hfin : ∀ q : ℕ, FiniteDimensional K Γ((q • D).sheaf, ⊤))
    (hle : ∀ q : ℕ, Module.finrank K Γ((q • D).sheaf, ⊤) ≤ 1) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  obtain ⟨q₀, hq₀⟩ := hgg
  have hprin (q : ℕ) (hq : q₀ ≤ q) :
      ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ := by
    letI := hfin q
    exact principal_of_globallyGenerated_of_finrank_le_one (K := K) (q • D)
      (hq₀ q hq) (hle q)
  exact principal_of_consecutive_multiples D q₀ (hprin q₀ le_rfl) (hprin (q₀ + 1) (by omega))

end MixedFujita
