/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleOpenFrameGerms
public import MixedFujita.SGANaturalSectionModuleDictionary

/-! 同一実切断の単元非消滅の任意局所枠への保存。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Unit nonvanishing of one fixed actual global section is independent
of the chosen local rank-one frame, without changing the section. -/
theorem moduleSection_frame_unit_of_frame_unit
    {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) (x : X)
    (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))
    (hs : IsUnit (moduleOverFrameGlobalCoefficientGerm M U e x hxU s)) :
    IsUnit (moduleOverFrameGlobalCoefficientGerm M V d x hxV s) := by
  let W := V ⊓ U
  let eW := moduleOverFrameRestrictIso M U e W inf_le_right
  let dW := moduleOverFrameRestrictIso M V d W inf_le_left
  have hxW : x ∈ W := ⟨hxV, hxU⟩
  have heW : IsUnit (moduleOverFrameGlobalCoefficientGerm M W eW x hxW s) := by
    simpa only [eW, moduleOverFrameGlobalCoefficientGerm_restrict] using hs
  obtain ⟨v, hv⟩ := moduleOverFrameGlobalCoefficientGerm_change_frame M W dW eW x hxW
  have hdW : IsUnit (moduleOverFrameGlobalCoefficientGerm M W dW x hxW s) := by
    rw [hv s]
    exact v.isUnit.mul heW
  simpa only [dW, moduleOverFrameGlobalCoefficientGerm_restrict] using hdW


/-- The fixed actual SGA section is a generator in every chosen frame
at each point of its nonvanishing locus. -/
theorem sga_nonvanishing_section_unit_in_any_frame
    {X : Scheme.{u}} (L : X.LineBundle) (n : ℕ) (s : L.sections n)
    (x : X) (hx : x ∈ L.nonvanishingLocus s) (U : X.Opens) (hxU : x ∈ U)
    (e : (L.toModules (n : ℤ)).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsUnit (moduleOverFrameGlobalCoefficientGerm (L.toModules (n : ℤ)) U e x hxU
      (sgaNaturalSectionToModule L n s)) := by
  obtain ⟨k, hk⟩ := (L.mem_nonvanishingLocus s).mp hx
  have hxk : x ∈ L.U k := (X.basicOpen_le (s.val k)) hk
  apply moduleSection_frame_unit_of_frame_unit (L.toModules (n : ℤ))
    (sgaNaturalSectionToModule L n s) x (L.U k) U hxk hxU (sgaLineBundleOverFrameIso L n k) e
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [sgaNaturalSectionToModule_frame_coefficient]
  exact (X.mem_basicOpen (s.val k) x hxk).mp hk

end MixedFujita
