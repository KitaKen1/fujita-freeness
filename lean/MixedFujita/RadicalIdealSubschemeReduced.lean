/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.QuasicoherentImageIdealSheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! 根基的実イデアル層から実閉部分スキームの被約性。 See reports/check-246-lc-radical-reduced-fixed-subscheme-lifting.json for the verified scope. The actual lc kernel image ideal is radical and its nonempty lower-dimensional subscheme W is reduced. One fixed I and W works for all nef-big adjoints. Usual KV gives actual restriction section lifting; any nonzero restricted section removes an original basepoint on W. Usual KV itself, restricted-section nonvanishing and stable-base-locus placement remain unproved; no normal lc-center adjunction, klt BPF or full F1/F2 is claimed. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
/-- Affine radical ideals give a reduced ACTUAL ideal-sheaf subscheme. -/
theorem idealSheaf_subscheme_isReduced_of_affine_radical
    {X : Scheme.{u}} (I : X.IdealSheafData) (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) :
    IsReduced I.subscheme := by
  let : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
    fun U => (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hI U)
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).mpr
  intro U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  infer_instance

end MixedFujita
