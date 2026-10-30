/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierSectionLifting
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
The round-down of a real divisor supported on a family of prime divisors, and the lifting of
section 6.3 of the manuscript in terms of it (step 12).

Let ξ_1, …, ξ_r be distinct codimension-one points of T with Cartier divisors E_k having
coefficient one at ξ_k and zero at every other codimension-one point. Integral combinations
Σ a_k E_k have coefficient a_k at ξ_k and zero outside the family. For real numbers Γ_k (the
coefficients of the divisor Γ = B_T + Ψ of the manuscript) put ⌊Γ⌋ = Σ ⌊Γ_k⌋ E_k and let S be a
nonempty set of indices such that

* the members of S map to one closed point x of Y and Γ_k = 1 for k in S;
* Γ_k < 1 for every other member whose closure meets the closure of a member of S;
* Γ_k ≥ 0 for the members which are not exceptional over Y.

If H¹(T, O(ρ*P − ⌊Γ⌋)) = 0, the Cartier divisor P of Y has a global section generating it at x.
The divisors of the manuscript are C = −⌊Γ⌋ + S and Q = ρ*P − ⌊Γ⌋.
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

section Coefficients

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient at a point, as an additive map on Cartier divisors. -/
noncomputable def cartierCoefficientHom (ξ : X) : CartierDivisor X →+ ℤ where
  toFun D := cartierCoefficient D ξ
  map_zero' := cartierCoefficient_zero ξ
  map_add' D E := cartierCoefficient_add D E ξ

theorem cartierCoefficient_sum {ι : Type*} (s : Finset ι) (D : ι → CartierDivisor X) (ξ : X) :
    cartierCoefficient (∑ i ∈ s, D i) ξ = ∑ i ∈ s, cartierCoefficient (D i) ξ :=
  map_sum (cartierCoefficientHom ξ) D s

theorem cartierCoefficient_zsmul (D : CartierDivisor X) (a : ℤ) (ξ : X) :
    cartierCoefficient (a • D) ξ = a * cartierCoefficient D ξ := by
  have h := map_zsmul (cartierCoefficientHom ξ) a D
  rwa [smul_eq_mul] at h

/-- The coefficients of an integral combination of the member divisors of a family of distinct
prime divisors: a_k at ξ_k, zero outside the family. -/
theorem cartierCoefficient_member_combination {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (E : Fin r → CartierDivisor X)
    (hEc : ∀ (i : Fin r) (z : CodimensionOnePoint X),
      cartierCoefficient (E i) (z : X) = if (z : X) = ξ i then 1 else 0)
    (a : Fin r → ℤ) (z : CodimensionOnePoint X) :
    (∃ k, (z : X) = ξ k ∧ cartierCoefficient (∑ i, a i • E i) (z : X) = a k) ∨
      ((z : X) ∉ Set.range ξ ∧ cartierCoefficient (∑ i, a i • E i) (z : X) = 0) := by
  have hsum : cartierCoefficient (∑ i, a i • E i) (z : X) =
      ∑ i, a i * (if (z : X) = ξ i then 1 else 0) := by
    rw [cartierCoefficient_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [cartierCoefficient_zsmul, hEc i z]
  by_cases hz : (z : X) ∈ Set.range ξ
  · obtain ⟨k, hk⟩ := hz
    refine Or.inl ⟨k, hk.symm, ?_⟩
    rw [hsum, Finset.sum_eq_single k]
    · rw [ite_eq_left hk.symm, mul_one]
    · intro j _ hjk
      rw [ite_eq_right fun h => hjk (hinj (h.symm.trans hk.symm)), mul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · refine Or.inr ⟨hz, ?_⟩
    rw [hsum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [ite_eq_right fun h => hz ⟨i, h.symm⟩, mul_zero]

end Coefficients

section Lifting

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian T]

/-- The lifting of section 6.3 in terms of the round-down. Let ρ : T → Y be a proper birational
morphism of normal schemes, P a Cartier divisor of Y, ξ_k distinct prime divisors of T with member
divisors E_k, and Γ_k real numbers. Let S be a nonempty set of indices whose members map to the
closed point x of Y, with Γ_k = 1 on S, Γ_k < 1 for the other members meeting a member of S and
Γ_k ≥ 0 for the members not exceptional over Y. If H¹(T, O(ρ*P − Σ ⌊Γ_k⌋ E_k)) = 0, then P has a
global section generating it at x. -/
theorem exists_section_generating_of_floor_vanishing
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ Y) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (P : CartierDivisor Y) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (E : Fin r → CartierDivisor T)
    (hE : ∀ i, (E i).IsEffective)
    (hEc : ∀ (i : Fin r) (z : CodimensionOnePoint T),
      cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0)
    (Γ : Fin r → ℝ) (S : Set (Fin r)) (hS : S.Nonempty) (x : Y) (hx : IsClosed ({x} : Set Y))
    (hSx : ∀ k ∈ S, ρ (ξ k) = x) (hSΓ : ∀ k ∈ S, Γ k = 1)
    (hmeet : ∀ k, k ∉ S →
      (∃ k' ∈ S, (closure ({ξ k} : Set T) ∩ closure ({ξ k'} : Set T)).Nonempty) → Γ k < 1)
    (hexc : ∀ k, Order.coheight (ρ (ξ k)) = 1 → 0 ≤ Γ k)
    (hvan : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ P - ∑ k, ⌊Γ k⌋ • E k).sheaf 1)) :
    ∃ (g : Y.functionField) (f : Y.functionFieldˣ) (u : (Y.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (Y.presheaf.stalk x) Y.functionField u = f * g := by
  obtain ⟨k₀, hk₀⟩ := hS
  -- the indicator of S, the divisors S and C
  let σ : Fin r → ℤ := fun k => if k ∈ S then 1 else 0
  have hσS : ∀ k, k ∈ S → σ k = 1 := fun k hk => ite_eq_left hk
  have hσN : ∀ k, k ∉ S → σ k = 0 := fun k hk => ite_eq_right hk
  have hfloorS : ∀ k, k ∈ S → ⌊Γ k⌋ = 1 := fun k hk => by
    rw [hSΓ k hk]
    exact Int.floor_one
  let Sd : CartierDivisor T := ∑ k, σ k • E k
  let C : CartierDivisor T := ∑ k, (σ k - ⌊Γ k⌋) • E k
  have hSd : Sd.IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 => h1.add h2)
      CartierDivisor.isEffective_zero
    intro k _
    by_cases hk : k ∈ S
    · rw [hσS k hk, one_zsmul]
      exact hE k
    · rw [hσN k hk, zero_zsmul]
      exact CartierDivisor.isEffective_zero
  have hQ : cartierPullback ρ P + C - Sd = cartierPullback ρ P - ∑ k, ⌊Γ k⌋ • E k := by
    have hC : C = Sd - ∑ k, ⌊Γ k⌋ • E k := by
      change ∑ k, (σ k - ⌊Γ k⌋) • E k = ∑ k, σ k • E k - ∑ k, ⌊Γ k⌋ • E k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_zsmul, sub_eq_add_neg]
    rw [hC]
    abel
  have hvan' : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ P + C - Sd).sheaf 1) := by
    rw [hQ]
    exact hvan
  have hcoefSd := cartierCoefficient_member_combination ξ hinj E hEc σ
  have hcoefC := cartierCoefficient_member_combination ξ hinj E hEc fun k => σ k - ⌊Γ k⌋
  -- the support of S and the neighbourhood on which C is effective
  let Z : Set T := ⋃ k ∈ S, closure ({ξ k} : Set T)
  have hZ : IsClosed Z := (Set.toFinite S).isClosed_biUnion fun k _ => isClosed_closure
  let N : Set (Fin r) := {k | σ k - ⌊Γ k⌋ < 0}
  have hNclosed : IsClosed (⋃ k ∈ N, closure ({ξ k} : Set T)) :=
    (Set.toFinite N).isClosed_biUnion fun k _ => isClosed_closure
  let W₀ : T.Opens := ⟨(⋃ k ∈ N, closure ({ξ k} : Set T))ᶜ, hNclosed.isOpen_compl⟩
  have hSdZ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Z → cartierCoefficient Sd (z : T) = 0 := by
    intro z hz
    rcases hcoefSd z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      apply hσN
      intro hk
      exact hz (Set.mem_biUnion hk (by rw [hzk]; exact subset_closure rfl))
    · exact hco
  have hZW₀ : Z ⊆ W₀ := by
    intro t ht
    obtain ⟨k', hk', htk'⟩ := Set.mem_iUnion₂.mp ht
    change t ∉ ⋃ k ∈ N, closure ({ξ k} : Set T)
    intro htN
    obtain ⟨k, hkN, htk⟩ := Set.mem_iUnion₂.mp htN
    have hneg : σ k - ⌊Γ k⌋ < 0 := hkN
    by_cases hk : k ∈ S
    · rw [hσS k hk, hfloorS k hk] at hneg
      exact lt_irrefl _ hneg
    · have hlt : Γ k < 1 := hmeet k hk ⟨k', hk', t, htk, htk'⟩
      have hfl : ⌊Γ k⌋ < 1 := Int.floor_lt.mpr (by exact_mod_cast hlt)
      rw [hσN k hk] at hneg
      omega
  have hCW₀ : ∀ z : CodimensionOnePoint T, (z : T) ∈ W₀ → 0 ≤ cartierCoefficient C (z : T) := by
    intro z hz
    rcases hcoefC z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      by_contra hneg
      apply hz
      exact Set.mem_biUnion (show k ∈ N from not_le.mp hneg)
        (by rw [hzk]; exact subset_closure rfl)
    · exact hco.ge
  have hCexc : ∀ z : CodimensionOnePoint T, Order.coheight (ρ (z : T)) = 1 →
      cartierCoefficient C (z : T) ≤ 0 := by
    intro z hzρ
    rcases hcoefC z with ⟨k, hzk, hco⟩ | ⟨-, hco⟩
    · rw [hco]
      rw [hzk] at hzρ
      have hfl : 0 ≤ ⌊Γ k⌋ := Int.floor_nonneg.mpr (hexc k hzρ)
      by_cases hk : k ∈ S
      · rw [hσS k hk, hfloorS k hk]
        exact le_of_eq (sub_self _)
      · rw [hσN k hk]
        omega
    · exact hco.le
  have hξZ : ξ k₀ ∈ Z := Set.mem_biUnion hk₀ (subset_closure rfl)
  have hSdξ : 1 ≤ cartierCoefficient Sd (ξ k₀) := by
    rcases hcoefSd ⟨ξ k₀, hξ k₀⟩ with ⟨k, hzk, hco⟩ | ⟨hz, -⟩
    · have hkk : k₀ = k := hinj hzk
      rw [hco, ← hkk, hσS k₀ hk₀]
    · exact absurd ⟨k₀, rfl⟩ hz
  have hCξ : cartierCoefficient C (ξ k₀) = 0 := by
    rcases hcoefC ⟨ξ k₀, hξ k₀⟩ with ⟨k, hzk, hco⟩ | ⟨hz, -⟩
    · have hkk : k₀ = k := hinj hzk
      rw [hco, ← hkk, hσS k₀ hk₀, hfloorS k₀ hk₀]
      exact sub_self _
    · exact absurd ⟨k₀, rfl⟩ hz
  have hZρ : ∀ t ∈ Z, ρ t = ρ (ξ k₀) := by
    intro t ht
    obtain ⟨k, hk, htk⟩ := Set.mem_iUnion₂.mp ht
    have h1 : ρ t ∈ closure ({ρ (ξ k)} : Set Y) := by
      have h := image_closure_subset_closure_image ρ.continuous (Set.mem_image_of_mem ρ htk)
      rwa [Set.image_singleton] at h
    rw [hSx k hk, hx.closure_eq] at h1
    rw [hSx k₀ hk₀]
    exact h1
  obtain ⟨g, f, u, hg, hf, hu⟩ := exists_section_generating_of_lifting hnormY hnormT ρ hρ P C Sd
    hSd hvan' Z hZ hSdZ W₀ hZW₀ hCW₀ hCexc ⟨ξ k₀, hξ k₀⟩ hξZ hSdξ hCξ hZρ
  have hxk : ρ (ξ k₀) = x := hSx k₀ hk₀
  subst hxk
  exact ⟨g, f, u, hg, hf, hu⟩

end Lifting

end MixedFujita
