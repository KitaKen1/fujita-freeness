/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerClosedSupport

/-! 基底の閉集合のNoether帰納と非被約連接支持の分解。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Noetherian induction on closed BASE subsets, while retaining all
nilpotent coherent layers on the arbitrary proper source. -/
theorem cartierPulledModuleMixedEulerDifference_vanish_of_integral_base_supports
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [NoetherianSpace X] [QuasiSeparatedSpace X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hint : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      Set.range i ≠ Set.univ → ∀ N : Y.Modules, N.IsCoherent →
        CohomologyAux.VanishesOff N (p ⁻¹' Set.range i) →
          cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (T : Set X) (hT : IsClosed T) (hTne : T ≠ Set.univ)
    (M : Y.Modules) [M.IsCoherent] (hM : CohomologyAux.VanishesOff M (p ⁻¹' T)) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  suffices HH : ∀ T : TopologicalSpace.Closeds X, (T : Set X) ≠ Set.univ →
      ∀ N : Y.Modules, N.IsCoherent → CohomologyAux.VanishesOff N (p ⁻¹' (T : Set X)) →
        cartierPulledModuleMixedEulerDifference K p N D E = 0 from
    HH ⟨T, hT⟩ hTne M inferInstance hM
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  intro hTne N hN hNT
  let := hN
  by_cases hne : (T : Set X).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.preimage_empty] at hNT
    exact cartierPulledModuleMixedEulerDifference_zero_sections K p N
      (fun V s => hNT V (Set.disjoint_empty _) s) D E
  by_cases hpre : IsPreirreducible (T : Set X)
  · obtain ⟨Z, i, hi, hZ, hrange⟩ :=
      CohomologyAux.exists_integral_closedImmersion (T : Set X) T.2 ⟨hne, hpre⟩
    exact hint Z i hi hZ (by simpa only [hrange] using hTne) N hN
      (by simpa only [hrange] using hNT)
  · obtain ⟨u, v, hu, hv, hTu, hTv, huv⟩ : ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧
        ((T : Set X) ∩ u).Nonempty ∧ ((T : Set X) ∩ v).Nonempty ∧
        ¬ ((T : Set X) ∩ (u ∩ v)).Nonempty := by
      simpa [IsPreirreducible] using hpre
    let T₁ : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ uᶜ, T.2.inter hu.isClosed_compl⟩
    let T₂ : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ vᶜ, T.2.inter hv.isClosed_compl⟩
    have hlt₁ : T₁ < T := lt_of_le_of_ne (fun x hx => hx.1) fun he => by
      obtain ⟨x, hxT, hxu⟩ := hTu
      have : x ∈ (T₁ : Set X) := he ▸ hxT
      exact this.2 hxu
    have hlt₂ : T₂ < T := lt_of_le_of_ne (fun x hx => hx.1) fun he => by
      obtain ⟨x, hxT, hxv⟩ := hTv
      have : x ∈ (T₂ : Set X) := he ▸ hxT
      exact this.2 hxv
    have hunion : (T : Set X) ⊆ (T₁ : Set X) ∪ (T₂ : Set X) := fun x hx => by
      by_contra h
      simp only [Set.mem_union, not_or] at h
      exact huv ⟨x, hx, not_not.mp fun h' => h.1 ⟨hx, h'⟩,
        not_not.mp fun h' => h.2 ⟨hx, h'⟩⟩
    have hne₁ : (T₁ : Set X) ≠ Set.univ := fun h => hTne
      (Set.eq_univ_of_univ_subset (h ▸ hlt₁.le))
    have hne₂ : (T₂ : Set X) ≠ Set.univ := fun h => hTne
      (Set.eq_univ_of_univ_subset (h ▸ hlt₂.le))
    refine CohomologyAux.prop_of_vanishesOff_union
      (fun N : Y.Modules => cartierPulledModuleMixedEulerDifference K p N D E = 0)
      (fun S hS h₁ h₂ h₃ hP₁ hP₃ => ?_)
      (T₁ := p ⁻¹' (T₁ : Set X)) (T₂ := p ⁻¹' (T₂ : Set X)) (T₂.2.preimage p.continuous)
      (fun N' hN' h' => ih T₁ hlt₁ hne₁ N' hN' h')
      (fun N' hN' h' => ih T₂ hlt₂ hne₂ N' hN' h') N ?_
    · let := h₁
      let := h₂
      let := h₃
      have h := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E hS
      simpa only [hP₁, hP₃, add_zero] using h
    · rw [← Set.preimage_union]
      exact hNT.mono (Set.preimage_mono hunion)

end MixedFujita
