/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafAffineModulePresentation
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-! 実準連接全射の全アフィン開集合上の切断全射。 See reports/check-260-ideal-exterior-affine-generation.json for the verified scope. Actual quasicoherent epimorphisms are surjective on every affine open; the SAME finite global generators span there and have a unit coefficient at any specified affine frame. Empty actual ideal support gives an isomorphic inclusion; the nonflat actual comap comparison makes natural ideal inclusion and Cartier-twisted inclusion epimorphic after mapping off support. ALL high original ample powers construct one finite actual ambient Cartier family naturally zero on the actual closed center whose canonical finite-free map pulls back epimorphically on its canonical open complement. Identifying this with the canonical map of the same naturally pulled global sections, pointwise original Cartier basepointfreeness, exterior LC/Bertini, ambient nonLC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000


/-- An ACTUAL epimorphism of quasi-coherent modules is surjective on sections
over EVERY actual affine open. Open restriction has exact component formulas,
so no new private chart/global-sections equivalence is needed. -/
theorem quasicoherent_epi_app_surjective_on_affine
    {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] (U : X.affineOpens) :
    Function.Surjective (Scheme.Modules.Hom.app φ U.1) := by
  let e := U.2.fromSpec
  let : (M.restrict e).IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback e).app M).symm
  let : (N.restrict e).IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback e).app N).symm
  let : Epi ((Scheme.Modules.restrictFunctor e).map φ) :=
    (Scheme.Modules.restrictFunctor e).map_epi φ
  have h := moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
    ((Scheme.Modules.restrictFunctor e).map φ)
  change Function.Surjective (Scheme.Modules.Hom.app φ (e ''ᵁ ⊤)) at h
  have hU : e ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  exact hU ▸ h

end MixedFujita
