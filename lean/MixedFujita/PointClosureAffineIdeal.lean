/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PointClosureSubscheme
public import MixedFujita.SmoothSchemeCoordinates

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
theorem pointClosureIdeal_affine_of_mem {X : Scheme.{u}} (x : X)
    (hx : IsClosed {x}) (U : X.affineOpens) (hxU : x ∈ U.1) :
    (pointClosureIdeal x).ideal U = (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  rw [pointClosureIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  have he : U.2.fromSpec ⁻¹' (closure ({x} : Set X)) =
      {U.2.primeIdealOf ⟨x, hxU⟩} := by
    rw [hx.closure_eq]
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact U.2.fromSpec.isOpenEmbedding.injective
        (h.trans (U.2.fromSpec_primeIdealOf ⟨x, hxU⟩).symm)
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure ({x} : Set X)) = _
  rw [he, PrimeSpectrum.vanishingIdeal_singleton]

theorem pointClosureIdeal_affine_of_notMem {X : Scheme.{u}} (x : X)
    (hx : IsClosed {x}) (U : X.affineOpens) (hxU : x ∉ U.1) :
    (pointClosureIdeal x).ideal U = ⊤ := by
  rw [pointClosureIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  have he : U.2.fromSpec ⁻¹' (closure ({x} : Set X)) = ∅ := by
    rw [hx.closure_eq]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h : U.2.fromSpec p ∈ U.1 := by
      rw [← SetLike.mem_coe, ← U.2.range_fromSpec]
      exact Set.mem_range_self p
    exact hxU ((Set.mem_singleton_iff.mp hp) ▸ h)
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure ({x} : Set X)) = _
  rw [he]
  simp [PrimeSpectrum.vanishingIdeal]

attribute [local instance] cartierBaseOpenAlgebra cartierBaseLocalAlgebra

theorem pointClosureIdeal_affine_eq_evaluation_kernel {K : Type u} [Field K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] (x : X)
    (hx : IsClosed {x}) (U : X.affineOpens) (hxU : x ∈ U.1)
    (β : X.presheaf.stalk x →ₐ[K] K) :
    (pointClosureIdeal x).ideal U =
      RingHom.ker (rationalAffineGermPoint x hxU β).toRingHom := by
  rw [pointClosureIdeal_affine_of_mem x hx U hxU, rationalAffineGermPoint_ker x hxU β U.2]

end MixedFujita
