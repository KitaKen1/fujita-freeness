/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierNefDefinition
public import MixedFujita.ProjectiveIntegralHilbert

/-!
Big divisors. A Cartier divisor D on an integral scheme of dimension d over a field is big if
h^0(m D) ≥ c m^d for some c > 0 and infinitely many m. Adding a principal divisor does not change
the sections: multiplication by g identifies Γ(D + div g) with Γ(D) as vector spaces over the
base field. Every ample divisor in the projective sense on an integral scheme of dimension d ≥ 1
over an infinite field is big: if m A = J + div f then h^0(k m A) = h^0(k J), and
h^0(k J)/k^d tends to r/d! with r ≥ 1 the degree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierSectionRational_sectionMk (D : CartierDivisor Y) (r : Y.functionField)
    (h : (rationalFunctionsEquiv (X := Y) ⊤).symm r ∈ D.sections ⊤) :
    cartierSectionRational D (CartierDivisor.sectionMk _ h) = r := by
  rw [cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk,
    LinearEquiv.apply_symm_apply]

theorem cartierSectionRational_sectionMk_of_mem (D : CartierDivisor Y)
    (x : Γ(rationalFunctions Y, ⊤)) (h : x ∈ D.sections ⊤) :
    cartierSectionRational D (CartierDivisor.sectionMk x h) = rationalFunctionsEquiv ⊤ x := by
  rw [cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk]

theorem cartierPrincipalShift_mem (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    (rationalFunctionsEquiv (X := Y) ⊤).symm
      ((g : Y.functionField) * cartierSectionRational _ s) ∈ D.sections ⊤ := by
  have h := (cartierSections_mem_principalShift D g ⊤ _).mp
    ((D + principalCartierDivisor Y g).sheafι_app_mem ⊤ s)
  convert h using 1
  apply (rationalFunctionsEquiv (X := Y) ⊤).injective
  rw [LinearEquiv.apply_symm_apply, rationalFunctionsEquiv_rationalFunctionsMul_app,
    cartierSectionRational_apply]

theorem cartierPrincipalShift_mem_inv (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (t : Γ(D.sheaf, ⊤)) :
    (rationalFunctionsEquiv (X := Y) ⊤).symm
      (((g⁻¹ : Y.functionFieldˣ) : Y.functionField) * cartierSectionRational D t) ∈
        (D + principalCartierDivisor Y g).sections ⊤ := by
  apply (cartierSections_mem_principalShift D g ⊤ _).mpr
  convert D.sheafι_app_mem ⊤ t using 1
  apply (rationalFunctionsEquiv (X := Y) ⊤).injective
  rw [rationalFunctionsEquiv_rationalFunctionsMul_app, LinearEquiv.apply_symm_apply,
    ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
    cartierSectionRational_apply]

section Base

variable [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

/-- Multiplication by g, from the sections of D + div g to those of D. -/
noncomputable def cartierPrincipalShiftLinear (D : CartierDivisor Y) (g : Y.functionFieldˣ) :
    Γ((D + principalCartierDivisor Y g).sheaf, ⊤) →ₗ[K] Γ(D.sheaf, ⊤) where
  toFun s := CartierDivisor.sectionMk _ (cartierPrincipalShift_mem D g s)
  map_add' s₁ s₂ := by
    apply cartierSectionRational_injective
    simp only [map_add, cartierSectionRational_sectionMk_of_mem, LinearEquiv.apply_symm_apply, mul_add]
  map_smul' c s := by
    apply cartierSectionRational_injective
    change cartierSectionRational D (CartierDivisor.sectionMk _
        (cartierPrincipalShift_mem D g ((algebraMap K Γ(Y, ⊤) c) • s))) =
      cartierSectionRational D ((algebraMap K Γ(Y, ⊤) c) •
        CartierDivisor.sectionMk _ (cartierPrincipalShift_mem D g s))
    rw [cartierSectionRational_sectionMk, map_smul, map_smul, cartierSectionRational_sectionMk,
      mul_smul_comm]

theorem cartierPrincipalShiftLinear_rational (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    cartierSectionRational D (cartierPrincipalShiftLinear (K := K) D g s) =
      (g : Y.functionField) * cartierSectionRational _ s :=
  cartierSectionRational_sectionMk D _ _

theorem cartierPrincipalShiftLinear_bijective (D : CartierDivisor Y) (g : Y.functionFieldˣ) :
    Function.Bijective (cartierPrincipalShiftLinear (K := K) D g) := by
  constructor
  · intro s s' h
    have h' := congrArg (cartierSectionRational D) h
    rw [cartierPrincipalShiftLinear_rational, cartierPrincipalShiftLinear_rational] at h'
    exact cartierSectionRational_injective _ (mul_left_cancel₀ (Units.ne_zero g) h')
  · intro t
    refine ⟨CartierDivisor.sectionMk _ (cartierPrincipalShift_mem_inv D g t), ?_⟩
    apply cartierSectionRational_injective
    rw [cartierPrincipalShiftLinear_rational, cartierSectionRational_sectionMk, ← mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- The sections of D + div g and of D are isomorphic over the base field. -/
noncomputable def cartierPrincipalShiftEquiv (D : CartierDivisor Y) (g : Y.functionFieldˣ) :
    Γ((D + principalCartierDivisor Y g).sheaf, ⊤) ≃ₗ[K] Γ(D.sheaf, ⊤) :=
  LinearEquiv.ofBijective _ (cartierPrincipalShiftLinear_bijective (K := K) D g)

theorem finrank_add_principal (D : CartierDivisor Y) (g : Y.functionFieldˣ) :
    Module.finrank K Γ((D + principalCartierDivisor Y g).sheaf, ⊤) =
      Module.finrank K Γ(D.sheaf, ⊤) :=
  (cartierPrincipalShiftEquiv (K := K) D g).finrank_eq

variable (K) in
/-- Big: h^0(m D) ≥ c m^d for some c > 0 and infinitely many m, with d the dimension. -/
def CartierIsBig (D : CartierDivisor Y) : Prop :=
  ∃ d : ℕ, topologicalKrullDim Y = d ∧ ∃ c : ℝ, 0 < c ∧
    ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ Module.finrank K Γ((m • D).sheaf, ⊤)

/-- Every ample divisor in the projective sense is big. -/
theorem cartierIsAmpleProj_isBig [Infinite K] {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) : CartierIsBig K A := by
  obtain ⟨m, hm, n, e, _, he, g, hg, hggen, f, hmA⟩ := hA
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hn hd
  set J := projectiveHyperplaneCartier e g hg hggen with hJ
  have hdiv : ∀ k : ℕ, (k * m) • A = k • J + principalCartierDivisor Y (f ^ k) := by
    intro k
    rw [mul_nsmul', hmA, nsmul_add, principalCartierDivisor_power]
  have hrank : ∀ k : ℕ, Module.finrank K Γ(((k * m) • A).sheaf, ⊤) =
      Module.finrank K Γ((k • J).sheaf, ⊤) := by
    intro k
    rw [hdiv k, finrank_add_principal]
  have hℓ : (0 : ℝ) < r / d.factorial := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds (half_lt_self hℓ)))
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨d, hn, (r / d.factorial) / 2 / (m : ℝ) ^ d, by positivity, ?_⟩
  rw [frequently_atTop]
  intro a
  set k := max a (max k₀ 1) with hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
  have hkk₀ : k₀ ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨k * m, le_trans (le_max_left _ _) (Nat.le_mul_of_pos_right k hm), ?_⟩
  rw [hrank k]
  have h1 := hk₀ k hkk₀
  have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    positivity
  rw [lt_div_iff₀ hkpos] at h1
  have hcalc : (r / d.factorial) / 2 / (m : ℝ) ^ d * ((k * m : ℕ) : ℝ) ^ d =
      (r / d.factorial) / 2 * (k : ℝ) ^ d := by
    push_cast
    rw [mul_pow]
    field_simp
  rw [hcalc]
  linarith

end Base

end MixedFujita
