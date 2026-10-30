/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! proper写像の有限な閉ファイバーから有限近傍と全体有限性を内部構成。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Properness lets finite CLOSED fibers suffice for actual finiteness;
finite neighborhoods are constructed by the existing Zariski main theorem. -/
theorem properMap_isFinite_of_finite_closed_fibers
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) [IsProper f]
    (h : ∀ y : Y, IsClosed {y} → (f ⁻¹' {y}).Finite) : IsFinite f := by
  classical
  let I := {y : Y // IsClosed ({y} : Set Y)}
  choose U hU hfin using fun y : I => exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y.val (h y.val y.property)
  have hcover : (⨆ y : I, U y) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({y} : Set Y))).exists_closed_singleton
      ⟨y, subset_closure (Set.mem_singleton y)⟩
    have hspec : y ⤳ z := specializes_iff_mem_closure.mpr hz
    exact Opens.mem_iSup.mpr ⟨⟨z, hzc⟩, hspec.mem_open (U ⟨z, hzc⟩).isOpen (hU _)⟩
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) U hcover).mpr hfin

end MixedFujita
