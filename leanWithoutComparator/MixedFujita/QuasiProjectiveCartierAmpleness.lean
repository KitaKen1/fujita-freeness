/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Projective.LineBundle
public import MixedFujita.CartierSGAAmplenessDictionary
public import MixedFujita.AmpleCartierPullbackRepresentatives

/-! proper SGA準射影性から元ample Cartierの内部構成。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Proper quasi-projectivity in the actual SGA sense supplies an ORIGINAL
projective ample Cartier divisor, without an embedding comparison witness. -/
theorem proper_isQuasiProjective_exists_ample_cartier
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsQuasiProjective (X ↘ Spec (CommRingCat.of K))] :
    ∃ A : CartierDivisor X, CartierIsAmpleProj K A := by
  let f := X ↘ Spec (CommRingCat.of K)
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := f)
  let W := (f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens)).toScheme
  let j : W ⟶ X := (f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens)).ι
  let : IsIso j := by change IsIso X.topIso.hom; infer_instance
  let : IsIntegral W := by dsimp [W]; infer_instance
  let : W.Over (Spec (CommRingCat.of K)) := ⟨j ≫ f⟩
  let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (W ↘ Spec (CommRingCat.of K)) := by
    change IsProper (j ≫ f)
    infer_instance
  let LW := L.pullback j
  have hLW : LW.IsAmple := hL.2 ⊤ (isAffineOpen_top _)
  let AW := sgaLineBundleCartierDivisor LW
  have hAW : CartierIsAmpleProj K AW :=
    (cartierIsAmpleProj_iff_sga_of_iso K LW AW (sgaLineBundleCartierIso LW)).mpr hLW
  let r := inv j
  let : r.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change r ≫ (j ≫ f) = f
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor AW r
  exact ⟨A, cartierIsAmpleProj_of_finite_pullback_over K r AW A hAW a⟩

end MixedFujita
