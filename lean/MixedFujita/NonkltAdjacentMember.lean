/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModelChartJacobian

/-!
From the connectedness lemma to a component meeting the strict transform (step 9).

On a principalizing model ρ : T → X of the pair (X, H + 𝔞/M), with members ξ_s of the simple
normal crossing family whose coefficients in ρ^*H, K_{T/X} and the principalized ideal are h_s,
k_s and a_s, the boundary Δ_T = Σ (h_s − k_s + a_s/M) ξ_s has non-klt part the members with
M (h_s − k_s) + a_s ≥ M. The connectedness lemma (Kollár–Shokurov) says that the non-klt members
meet the fibre over a point x in a connected set. The strict transform ξ_{s₀} = H' (h = 1, k = 0,
a = 0) and a bad member ξ_{s₁} (M (1 + k) ≤ a, found by the minimum formula, check-333) are both
non-klt and meet the fibre over x ∈ H, so some other non-klt member ξ_r meets H' over x
(`exists_adjacent_nonklt_member`, from check-330); its coefficients satisfy the adjunction
inequality M (1 + k_r − h_r) ≤ a_r of the strict transform charts (check-334) at a point of
ξ_r ∩ H' over x.
-/

@[expose] public section

namespace MixedFujita

section Adjacent

/-- If the non-klt members meet the fibre over a closed point x in a preconnected set, a bad member
and the strict transform both meeting the fibre give a non-klt member different from the strict
transform which meets it over x, with the adjunction inequality. -/
theorem exists_adjacent_nonklt_member {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
    (ρ : T → Y) (hρ : Continuous ρ) {r : ℕ} (ξ : Fin r → T) (x : Y) (hx : IsClosed ({x} : Set Y))
    (M : ℤ) (hM : 0 < M) (h k a : Fin r → ℤ)
    (hconn : IsPreconnected (⋃ s ∈ {s | M ≤ M * (h s - k s) + a s},
      closure ({ξ s} : Set T) ∩ ρ ⁻¹' {x}))
    (s₀ s₁ : Fin r) (hh₀ : h s₀ = 1) (hk₀ : k s₀ = 0) (ha₀ : a s₀ = 0) (hh₁ : 0 ≤ h s₁)
    (hk₁ : 0 ≤ k s₁) (hbad : M * (1 + k s₁) ≤ a s₁)
    (hx₀ : x ∈ ρ '' closure ({ξ s₀} : Set T)) (hx₁ : x ∈ ρ '' closure ({ξ s₁} : Set T)) :
    ∃ r', r' ≠ s₀ ∧ M * (1 + k r' - h r') ≤ a r' ∧
      ∃ t, t ∈ closure ({ξ r'} : Set T) ∧ t ∈ closure ({ξ s₀} : Set T) ∧ ρ t = x := by
  classical
  let N : Set (Fin r) := {s | M ≤ M * (h s - k s) + a s}
  let Z : N → Set T := fun s => closure ({ξ s.1} : Set T) ∩ ρ ⁻¹' {x}
  have hZ : ∀ s, IsClosed (Z s) := fun s => isClosed_closure.inter (hx.preimage hρ)
  have hU : (⋃ s, Z s) = ⋃ s ∈ N, closure ({ξ s} : Set T) ∩ ρ ⁻¹' {x} := by
    ext p
    simp only [Set.mem_iUnion, Z, Subtype.exists, exists_prop]
  have hs₀ : s₀ ∈ N := by
    change M ≤ M * (h s₀ - k s₀) + a s₀
    rw [hh₀, hk₀, ha₀]
    linarith
  have hs₁ : s₁ ∈ N := by
    change M ≤ M * (h s₁ - k s₁) + a s₁
    nlinarith
  have hne : s₁ ≠ s₀ := by
    intro he
    have : a s₁ = 0 := he ▸ ha₀
    nlinarith
  obtain ⟨t₀, ht₀, hρt₀⟩ := hx₀
  obtain ⟨t₁, ht₁, hρt₁⟩ := hx₁
  obtain ⟨i, hi, p, hpi, hp₀⟩ := exists_ne_inter_nonempty_of_isPreconnected Z hZ (hU ▸ hconn)
    ⟨s₀, hs₀⟩ ⟨t₀, ht₀, hρt₀⟩ ⟨s₁, hs₁⟩ (fun he => hne (congrArg Subtype.val he))
    ⟨t₁, ht₁, hρt₁⟩
  refine ⟨i.1, fun he => hi (Subtype.ext he), ?_, p, hpi.1, hp₀.1, hpi.2⟩
  have hiN : M ≤ M * (h i.1 - k i.1) + a i.1 := i.2
  linarith

end Adjacent

end MixedFujita
