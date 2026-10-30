/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalTestOpenLift
public import MixedFujita.RationalThresholdLogCanonical

/-!
Actual base-open restriction preserves dominance on integral schemes. Klt and
log-canonical base-point tests are unchanged when the base is embedded as an
open subscheme, because the specialization guard is reflected by the embedding.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual restriction of a dominant map to a nonempty base open is dominant. -/
theorem isDominant_morphismRestrict_integral {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [IsDominant g]
    (V : Y.Opens) [Nonempty V] :
    letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
    IsDominant (g ∣_ V) := by
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ⁻¹ᵁ V).ι :=
    ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hgen : (g ∣_ V) (genericPoint (g ⁻¹ᵁ V).toScheme) = genericPoint V.toScheme := by
    apply V.ι.isOpenEmbedding.injective
    have h := congrArg (fun m : (g ⁻¹ᵁ V).toScheme ⟶ Y =>
      m (genericPoint (g ⁻¹ᵁ V).toScheme)) (morphismRestrict_ι g V)
    simp only [Scheme.Hom.comp_apply] at h
    rw [dominant_map_genericPoint (g ⁻¹ᵁ V).ι, dominant_map_genericPoint g] at h
    exact h.trans (dominant_map_genericPoint V.ι).symm
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  have hs : ({genericPoint V.toScheme} : Set V.toScheme) ⊆ Set.range (g ∣_ V) :=
    Set.singleton_subset_iff.mpr ⟨genericPoint (g ⁻¹ᵁ V).toScheme, hgen⟩
  simpa only [(genericPoint_spec V.toScheme).def] using closure_mono hs

/-- Actual Cartier pullback commutes with the open base-change square. -/
theorem cartierPullback_morphismRestrict {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [IsDominant g]
    (V : Y.Opens) [Nonempty V] (H : CartierDivisor Y) :
    letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
    letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ⁻¹ᵁ V).ι :=
      ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
    cartierPullback (g ⁻¹ᵁ V).ι (cartierPullback g H) =
      cartierPullback (g ∣_ V) (cartierPullback V.ι H) := by
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ⁻¹ᵁ V).ι :=
    ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
  rw [← cartierPullback_comp, ← cartierPullback_comp]
  simpa only [morphismRestrict_ι]

variable {K : Type u} [Field K] {n : ℕ} {X Y Z : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- The actual specialization guard is reflected by an open base immersion. -/
theorem mem_closure_singleton_open_immersion_iff
    (j : Z ⟶ Y) [IsOpenImmersion j] (x z : Z) :
    j z ∈ closure ({j x} : Set Y) ↔ z ∈ closure ({x} : Set Z) := by
  rw [← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
  exact j.isOpenEmbedding.isInducing.specializes_iff

theorem logPairIsKltOverBasePoint_comp_open_immersion_iff
    (g : X ⟶ Z) (j : Z ⟶ Y) [IsOpenImmersion j] (z : Z)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsKltOverBasePoint (g ≫ j) (j z) c f d D ↔
      LogPairIsKltOverBasePoint g z c f d D := by
  constructor
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht hz
    apply h T ρ hρ cT t ht
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using
      (mem_closure_singleton_open_immersion_iff j ((ρ ≫ g) t) z).mpr hz
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht hz
    apply h T ρ hρ cT t ht
    apply (mem_closure_singleton_open_immersion_iff j ((ρ ≫ g) t) z).mp
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using hz

theorem logPairIsLogCanonicalOverBasePoint_comp_open_immersion_iff
    (g : X ⟶ Z) (j : Z ⟶ Y) [IsOpenImmersion j] (z : Z)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsLogCanonicalOverBasePoint (g ≫ j) (j z) c f d D ↔
      LogPairIsLogCanonicalOverBasePoint g z c f d D := by
  constructor
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht hz
    apply h T ρ hρ cT t ht
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using
      (mem_closure_singleton_open_immersion_iff j ((ρ ≫ g) t) z).mpr hz
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht hz
    apply h T ρ hρ cT t ht
    apply (mem_closure_singleton_open_immersion_iff j ((ρ ≫ g) t) z).mp
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using hz

end MixedFujita
