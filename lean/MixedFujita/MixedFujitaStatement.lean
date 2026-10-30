/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalDivisor
public import MixedFujita.CartierNefDefinition
public import MixedFujita.CartierSectionProducts

/-!
The statement of F1, the mixed Fujita freeness, and the invariance of global generation under
principal divisors (step 1). The section f⁻¹ of O(div f) has local coefficient 1 at every point for
the local equation f, so multiplying sections of D by it gives sections of D + div f with the same
local coefficients: global generation is invariant under adding principal divisors. Since another
reference chart changes K_X by a principal divisor, whether K_X + L_1 + ⋯ + L_s + N is globally
generated does not depend on the chart. F1 states that on a smooth projective variety of dimension
n ≥ 1 over an uncountable algebraically closed field of characteristic zero, for ample divisors
L_1, …, L_s with s ≥ n + 1 and a nef divisor N, the divisor K_X + L_1 + ⋯ + L_s + N is globally
generated. Projectivity is implied by the ampleness of the L_i; ℂ is such a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section Principal

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- The section f⁻¹ of O(div f). -/
noncomputable def principalUnitSection (f : X.functionFieldˣ) :
    Γ((principalCartierDivisor X f).sheaf, ⊤) :=
  Scheme.Modules.Hom.app (CartierDivisor.unitToSheafPrincipalCartierDivisor X f) ⊤ (1 : Γ(X, ⊤))

theorem principalUnitSection_rational (f : X.functionFieldˣ) :
    cartierSectionRational (principalCartierDivisor X f) (principalUnitSection f) =
      ((f⁻¹ : X.functionFieldˣ) : X.functionField) := by
  rw [cartierSectionRational_apply, principalUnitSection,
    CartierDivisor.unitToSheafPrincipalCartierDivisor_app,
    rationalFunctionsEquiv_rationalFunctionsMul_app, rationalFunctionsEquiv_toRationalFunctions_app,
    map_one, mul_one]

theorem principalUnitSection_localCoefficient (f : X.functionFieldˣ) (x : X) :
    cartierLocalCoefficient (principalCartierDivisor X f) x f
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor x f) (principalUnitSection f) = 1 := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [cartierLocalCoefficient_image, principalUnitSection_rational, map_one, Units.mul_inv]

/-- Global generation survives adding a principal divisor. -/
theorem cartierIsGloballyGenerated_add_principal {D : CartierDivisor X} (f : X.functionFieldˣ)
    (hD : CartierIsGloballyGenerated D) :
    CartierIsGloballyGenerated (D + principalCartierDivisor X f) := by
  intro x
  obtain ⟨s, hs⟩ := hD x
  have hg := Classical.choose_spec (D.exists_isLocalEquationAt x)
  have hf := CartierDivisor.isLocalEquationAt_principalCartierDivisor x f
  refine ⟨cartierSectionProduct D (principalCartierDivisor X f) s (principalUnitSection f), ?_⟩
  have h1 : cartierLocalCoefficient (D + principalCartierDivisor X f) x
      (Classical.choose (D.exists_isLocalEquationAt x) * f) (hg.mul hf)
      (cartierSectionProduct D (principalCartierDivisor X f) s (principalUnitSection f)) =
        cartierLocalCoefficient D x (Classical.choose (D.exists_isLocalEquationAt x)) hg s := by
    rw [cartierSectionProduct_localCoefficient D (principalCartierDivisor X f) x _ f hg hf s
      (principalUnitSection f), principalUnitSection_localCoefficient, mul_one]
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (D + principalCartierDivisor X f) x
    (Classical.choose ((D + principalCartierDivisor X f).exists_isLocalEquationAt x))
    (Classical.choose (D.exists_isLocalEquationAt x) * f)
    (Classical.choose_spec ((D + principalCartierDivisor X f).exists_isLocalEquationAt x))
    (hg.mul hf)
  rw [hv, h1]
  exact (Units.isUnit v).mul hs

/-- Global generation depends only on the linear equivalence class. -/
theorem cartierIsGloballyGenerated_add_principal_iff (D : CartierDivisor X)
    (f : X.functionFieldˣ) :
    CartierIsGloballyGenerated (D + principalCartierDivisor X f) ↔ CartierIsGloballyGenerated D := by
  constructor
  · intro h
    have h' := cartierIsGloballyGenerated_add_principal f⁻¹ h
    have heq : D + principalCartierDivisor X f + principalCartierDivisor X f⁻¹ = D := by
      rw [add_assoc, ← principalCartierDivisor_mul, mul_inv_cancel, principalCartierDivisor_one,
        add_zero]
    rwa [heq] at h'
  · exact cartierIsGloballyGenerated_add_principal f

end Principal

section Statement

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseOpenAlgebra

/-- Whether K_X + E is globally generated does not depend on the reference chart of K_X. -/
theorem canonicalDivisor_add_isGloballyGenerated_iff {n : ℕ} (c₀ c₁ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) :
    CartierIsGloballyGenerated (canonicalDivisor n c₁ hcover + E) ↔
      CartierIsGloballyGenerated (canonicalDivisor n c₀ hcover + E) := by
  rw [canonicalDivisor_change_reference c₀ c₁ hcover]
  have heq : canonicalDivisor n c₀ hcover + principalCartierDivisor X
      (etaleChartCanonicalEquation c₁ c₀) + E =
        canonicalDivisor n c₀ hcover + E + principalCartierDivisor X
          (etaleChartCanonicalEquation c₁ c₀) := by abel
  rw [heq, cartierIsGloballyGenerated_add_principal_iff]

end Statement

attribute [local instance] cartierBaseOpenAlgebra

/-- F1, the mixed Fujita freeness: on a smooth projective variety of dimension n ≥ 1 over an
uncountable algebraically closed field of characteristic zero, for ample divisors L_1, …, L_s with
s ≥ n + 1 and a nef divisor N, the divisor K_X + L_1 + ⋯ + L_s + N is globally generated, for the
canonical divisor of any reference étale chart. -/
def MixedFujitaFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (s : ℕ), n + 1 ≤ s → ∀ (L : Fin s → CartierDivisor X), (∀ i, CartierIsAmpleProj K (L i)) →
      ∀ N : CartierDivisor X, CartierIsNef K N →
        CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N)

end MixedFujita
