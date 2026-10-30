/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSGAAmplenessDictionary
public import MixedFujita.SGATwistPullbackIso
public import SGA.Foundations.Projective.LineBundle

/-! 任意実代表元へのample引き戻し保存と整閉源のample因子の内部構成。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Affine pullback of an ample Cartier bundle is ample in the ORIGINAL
projective sense for every actual Cartier representative on a proper source.
No dominance, normality or supplied source embedding is assumed. -/
theorem cartierIsAmpleProj_of_affine_pullback_representation
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : X ⟶ Y) [IsAffineHom p] (A : CartierDivisor Y) (D : CartierDivisor X)
    (hA : CartierIsAmpleProj K A)
    (a : (Scheme.Modules.pullback p).obj A.sheaf ≅ D.sheaf) :
    CartierIsAmpleProj K D := by
  let L := (cartierSGALineBundle A).pullback p
  let b : L.toModules 1 ≅ D.sheaf :=
    (sgaLineBundlePullbackPowerIso (cartierSGALineBundle A) p 1).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (cartierSGAModuleIso A).symm ≪≫ a
  exact (cartierIsAmpleProj_iff_sga_of_iso K L D b).mpr
    (((cartierIsAmpleProj_iff_sga K A).mp hA).pullback p)


/-- In particular finite pullback preserves ORIGINAL ampleness for any
actual representative, without dominance or a hyperplane-form presentation. -/
theorem cartierIsAmpleProj_of_finite_pullback_representation
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : X ⟶ Y) [IsFinite p] (A : CartierDivisor Y) (D : CartierDivisor X)
    (hA : CartierIsAmpleProj K A)
    (a : (Scheme.Modules.pullback p).obj A.sheaf ≅ D.sheaf) :
    CartierIsAmpleProj K D :=
  cartierIsAmpleProj_of_affine_pullback_representation K p A D hA a


/-- A finite map over the field derives source properness internally, so
an actual Cartier representative of an ample pullback is originally ample
without separate source properness, projectivity or normality premises. -/
theorem cartierIsAmpleProj_of_finite_pullback_over
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : X ⟶ Y) [IsFinite p] [p.IsOver (Spec (CommRingCat.of K))]
    (A : CartierDivisor Y) (D : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (a : (Scheme.Modules.pullback p).obj A.sheaf ≅ D.sheaf) :
    CartierIsAmpleProj K D := by
  let : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p) (S := Spec (CommRingCat.of K))]
    infer_instance
  exact cartierIsAmpleProj_of_finite_pullback_representation K p A D hA a


/-- Every integral finite source over an ample proper scheme internally
acquires a genuine ample Cartier representative of the actual pullback. -/
theorem finite_integral_source_exists_ample_cartier_representative
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : X ⟶ Y) [IsFinite p] [p.IsOver (Spec (CommRingCat.of K))]
    (A : CartierDivisor Y) (hA : CartierIsAmpleProj K A) :
    ∃ D : CartierDivisor X, CartierIsAmpleProj K D ∧
      Nonempty ((Scheme.Modules.pullback p).obj A.sheaf ≅ D.sheaf) := by
  obtain ⟨D, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor A p
  exact ⟨D, cartierIsAmpleProj_of_finite_pullback_over K p A D hA a, ⟨a⟩⟩


/-- Any actual integral closed subscheme of an ample proper scheme
has an internally constructed ORIGINAL ample Cartier divisor. -/
theorem integral_closed_source_exists_original_ample_cartier
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (hY : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A) :
    ∃ D : CartierDivisor X, CartierIsAmpleProj K D := by
  obtain ⟨A, hA⟩ := hY
  obtain ⟨D, hD, _⟩ := finite_integral_source_exists_ample_cartier_representative K i A hA
  exact ⟨D, hD⟩

end MixedFujita
