/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierBigDefinition
public import MixedFujita.CartierSectionProducts
public import MixedFujita.CartierSectionPowers
public import MixedFujita.CartierAmpleDefinition

/-!
Operations preserving bigness (step 12, the numerical statement (27) of the manuscript).

Multiplication by a fixed nonzero section t of O(E) is an injective linear map over the base field
from the sections of O(D) to the sections of O(D + E). Hence h⁰(D) ≤ h⁰(D + E) when the sections
of O(D + E) are finite-dimensional, and finite-dimensionality passes from O(D + E) to O(D).
Effective divisors and globally generated divisors have nonzero sections. Consequently, for a big
divisor D:

* D + div g is big;
* e D is big for e ≥ 1, when the sections of the multiples of D are finite-dimensional;
* D + G is big when O(G) has a nonzero section and the sections of the multiples of D + G are
  finite-dimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- An effective Cartier divisor has a nonzero global section. -/
theorem exists_section_ne_zero_of_isEffective (E : CartierDivisor Y) (hE : E.IsEffective) :
    ∃ t : Γ(E.sheaf, ⊤), t ≠ 0 := by
  have hne : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hmem : (rationalFunctionsEquiv (X := Y) ⊤).symm (1 : Y.functionField) ∈ E.sections ⊤ := by
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x _
    obtain ⟨f, hf, hreg⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
    refine ⟨f, hf, ?_⟩
    rw [LinearEquiv.apply_symm_apply, mul_one]
    exact hreg
  refine ⟨CartierDivisor.sectionMk _ hmem, fun h => ?_⟩
  have h1 := cartierSectionRational_sectionMk E 1 hmem
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- A globally generated Cartier divisor has a nonzero global section. -/
theorem exists_section_ne_zero_of_isGloballyGenerated (D : CartierDivisor Y)
    (hD : CartierIsGloballyGenerated D) : ∃ t : Γ(D.sheaf, ⊤), t ≠ 0 := by
  obtain ⟨s, hs⟩ := hD (genericPoint Y)
  refine ⟨s, fun h => ?_⟩
  rw [h, map_zero] at hs
  exact not_isUnit_zero hs

section Base

variable [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

/-- Multiplication by a fixed section of O(E), as a linear map over the base field from the
sections of O(D) to the sections of O(D + E). -/
noncomputable def cartierSectionProductLinear (D E : CartierDivisor Y) (t : Γ(E.sheaf, ⊤)) :
    Γ(D.sheaf, ⊤) →ₗ[K] Γ((D + E).sheaf, ⊤) where
  toFun s := cartierSectionProduct D E s t
  map_add' s₁ s₂ := by
    apply cartierSectionRational_injective
    rw [map_add, cartierSectionProduct_rational, cartierSectionProduct_rational,
      cartierSectionProduct_rational, map_add, add_mul]
  map_smul' c s := by
    apply cartierSectionRational_injective
    change cartierSectionRational (D + E)
        (cartierSectionProduct D E ((algebraMap K Γ(Y, ⊤) c) • s) t) =
      cartierSectionRational (D + E) ((algebraMap K Γ(Y, ⊤) c) • cartierSectionProduct D E s t)
    rw [cartierSectionProduct_rational, map_smul, map_smul, cartierSectionProduct_rational,
      smul_mul_assoc]

theorem cartierSectionProductLinear_injective (D E : CartierDivisor Y) (t : Γ(E.sheaf, ⊤))
    (ht : t ≠ 0) : Function.Injective (cartierSectionProductLinear (K := K) D E t) := by
  intro s₁ s₂ h
  have h' : cartierSectionRational (D + E) (cartierSectionProduct D E s₁ t) =
      cartierSectionRational (D + E) (cartierSectionProduct D E s₂ t) :=
    congrArg (cartierSectionRational (D + E)) h
  rw [cartierSectionProduct_rational, cartierSectionProduct_rational] at h'
  have ht' : cartierSectionRational E t ≠ 0 :=
    (map_ne_zero_iff _ (cartierSectionRational_injective E)).mpr ht
  exact cartierSectionRational_injective D (mul_right_cancel₀ ht' h')

/-- Finite-dimensionality of the sections passes from N = D + E to D when O(E) has a nonzero
section. -/
theorem finiteDimensional_of_eq_add_of_section (D E N : CartierDivisor Y) (hN : N = D + E)
    (t : Γ(E.sheaf, ⊤)) (ht : t ≠ 0) (hfin : FiniteDimensional K Γ(N.sheaf, ⊤)) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  subst hN
  exact FiniteDimensional.of_injective (cartierSectionProductLinear (K := K) D E t)
    (cartierSectionProductLinear_injective D E t ht)

/-- h⁰(D) ≤ h⁰(N) when N = D + E, O(E) has a nonzero section and the sections of O(N) are
finite-dimensional. -/
theorem finrank_le_of_eq_add_of_section (D E N : CartierDivisor Y) (hN : N = D + E)
    (t : Γ(E.sheaf, ⊤)) (ht : t ≠ 0) (hfin : FiniteDimensional K Γ(N.sheaf, ⊤)) :
    Module.finrank K Γ(D.sheaf, ⊤) ≤ Module.finrank K Γ(N.sheaf, ⊤) := by
  subst hN
  exact LinearMap.finrank_le_finrank_of_injective
    (cartierSectionProductLinear_injective (K := K) D E t ht)

/-- Bigness is invariant under adding a principal divisor. -/
theorem cartierIsBig_add_principal {D : CartierDivisor Y} (hD : CartierIsBig K D)
    (g : Y.functionFieldˣ) : CartierIsBig K (D + principalCartierDivisor Y g) := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  refine ⟨d, hd, c, hc, hfreq.mono fun m hm => ?_⟩
  rw [nsmul_add, ← principalCartierDivisor_power, finrank_add_principal]
  exact hm

/-- A positive multiple of a big divisor is big, when the sections of its multiples are
finite-dimensional. -/
theorem cartierIsBig_nsmul {D : CartierDivisor Y} (hD : CartierIsBig K D) (e : ℕ) (he : 1 ≤ e)
    (hfin : ∀ m : ℕ, FiniteDimensional K Γ((m • D).sheaf, ⊤)) : CartierIsBig K (e • D) := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  refine ⟨d, hd, c, hc, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun m hm => ?_
  obtain ⟨hm, hm1⟩ := hm
  have hpos : 0 < Module.finrank K Γ((m • D).sheaf, ⊤) := by
    have h0 : (0 : ℝ) < c * (m : ℝ) ^ d :=
      mul_pos hc (pow_pos (by exact_mod_cast hm1) d)
    exact_mod_cast h0.trans_le hm
  have := hfin m
  obtain ⟨s, hs⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hdiv : m • (e • D) = m • D + (e - 1) • (m • D) := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.add_sub_cancel, nsmul_left_comm, succ_nsmul']
  have hfin' : FiniteDimensional K Γ((m • (e • D)).sheaf, ⊤) := by
    rw [← mul_nsmul']
    exact hfin (m * e)
  have hle := finrank_le_of_eq_add_of_section (K := K) (m • D) ((e - 1) • (m • D)) (m • (e • D))
    hdiv (cartierSectionPower (m • D) s (e - 1)) (cartierSectionPower_ne_zero (m • D) s hs (e - 1))
    hfin'
  exact hm.trans (by exact_mod_cast hle)

/-- Adding a divisor with a nonzero section to a big divisor gives a big divisor, when the
sections of the multiples of the sum are finite-dimensional. -/
theorem cartierIsBig_add_of_section {D G : CartierDivisor Y} (hD : CartierIsBig K D)
    (t : Γ(G.sheaf, ⊤)) (ht : t ≠ 0)
    (hfin : ∀ m : ℕ, FiniteDimensional K Γ((m • (D + G)).sheaf, ⊤)) :
    CartierIsBig K (D + G) := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  refine ⟨d, hd, c, hc, hfreq.mono fun m hm => ?_⟩
  have hle := finrank_le_of_eq_add_of_section (K := K) (m • D) (m • G) (m • (D + G))
    (nsmul_add D G m) (cartierSectionPower G t m) (cartierSectionPower_ne_zero G t ht m) (hfin m)
  exact hm.trans (by exact_mod_cast hle)

end Base

end MixedFujita
