/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleFixedSectionFrameUnits

/-! 任意SGA整数冪の有限affine実枠被覆の内部構成。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A compact source has a finite affine cover carrying actual frames
of each specified SGA integer power. Empty sources are included. -/
theorem sga_exists_finite_affine_frame_cover
    {X : Scheme.{u}} [CompactSpace X] (L : X.LineBundle) (n : ℤ) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
      (_e : ∀ i, (L.toModules n).over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))),
      (⨆ i, U i) = ⊤ := by
  classical
  have hex (x : X) : ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((L.toModules n).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [L.iSup_eq_top]; trivial)
    obtain ⟨U, hU, hxU, hUk⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hk
    exact ⟨U, hU, hxU, ⟨moduleOverFrameRestrictIso _ (L.U k) (sgaLineBundleOverFrameIso L n k) U hUk⟩⟩
  choose U hU hxU he using hex
  obtain ⟨B, hB⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨B, inferInstance, fun i => U i.val, fun i => hU i.val,
    fun i => Classical.choice (he i.val), ?_⟩
  apply top_unique
  intro x _
  obtain ⟨y, hyB, hxy⟩ := Set.mem_iUnion₂.mp (hB (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨y, hyB⟩, hxy⟩

end MixedFujita
