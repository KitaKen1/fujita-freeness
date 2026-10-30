/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectivePointedFirstOrder
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
Base-ring constants on projective charts. On polynomial projective space, the chart
inclusion followed by the structure morphism is Spec of the chart coefficient map,
by Mathlib's factorization through the degree-zero part. Hence the structure-morphism
constants restricted to the chart D+(X_k) are the chart coefficients. For a morphism
e over the base ring, the base constants of the source restricted to each pulled-back
chart are the images of the constant polynomials under the actual affine polynomial
presentation. Pulled-back homogeneous equations are therefore linear over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ} (R : Type u) [CommRing R]

theorem polynomialProjective_awayι_toBase (k : Fin n) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)
        (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one ≫ polynomialProjectiveToBase n R =
      Spec.map (CommRingCat.ofHom (projectiveChartCoefficient R k)) := by
  rw [polynomialProjectiveToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem polynomialProjective_awayι_appTop_base (k : Fin n) (r : R) :
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)
        (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one).appTop
        ((polynomialProjectiveToBase n R).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
      (Scheme.ΓSpecIso _).inv (projectiveChartCoefficient R k r) := by
  have h := congrArg Scheme.Hom.appTop (polynomialProjective_awayι_toBase R k)
  rw [Scheme.Hom.comp_appTop] at h
  have h' := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  rw [CommRingCat.comp_apply] at h'
  rw [h']
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (projectiveChartCoefficient R k))) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
  exact hn.symm

/-- The structure-morphism constants restricted to the chart D+(X_k) are the chart
coefficients. -/
theorem polynomialProjective_base_constant_chart (k : Fin n) (r : R) :
    (polynomialProjectiveScheme n R).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
          (MvPolynomial.X k) ≤ ⊤)).op
        ((polynomialProjectiveToBase n R).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
      Proj.awayToSection _ (MvPolynomial.X k) (projectiveChartCoefficient R k r) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) R
  set U := Proj.basicOpen 𝒜 (MvPolynomial.X k)
  set i := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k)
    Nat.zero_lt_one
  set z := (polynomialProjectiveToBase n R).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  have h1 := polynomialProjective_awayι_appTop_base R k r
  rw [← Proj.basicOpenIsoSpec_inv_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h1
  have h2 := congrArg i.hom.appTop h1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop,
    CommRingCat.id_apply] at h2
  have h3 := ConcreteCategory.congr_hom
    (Proj.basicOpenToSpec_app_top 𝒜 (MvPolynomial.X k)) ((Scheme.ΓSpecIso _).inv
      (projectiveChartCoefficient R k r))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h3
  have h4 : U.ι.appTop z = U.topIso.inv
      (Proj.awayToSection 𝒜 (MvPolynomial.X k) (projectiveChartCoefficient R k r)) := by
    rw [h2]
    exact h3
  have h5 := congrArg U.topIso.hom h4
  rw [Iso.inv_hom_id_apply] at h5
  have hmor : U.ι.appTop ≫ U.topIso.hom = (Proj 𝒜).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have h6 := ConcreteCategory.congr_hom hmor z
  rw [CommRingCat.comp_apply] at h6
  exact h6.symm.trans h5

theorem projectiveChartAffineToLocalization_C (k : Fin n) (r : R) :
    projectiveChartAffineToLocalization R k (MvPolynomial.C r) = projectiveChartCoefficient R k r := by
  simp [projectiveChartAffineToLocalization]

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K)

/-- For e over the base field, constant polynomials pull back to the base constants. -/
theorem projectivePullbackAffinePolynomialMap_C
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (k : Fin n) (c : K) :
    projectivePullbackAffinePolynomialMap e k (MvPolynomial.C c) =
      Y.presheaf.map (homOfLE (le_top : projectivePullbackCoordinateOpen e k ≤ ⊤)).op
        (Scheme.Modules.baseRingToGlobalSections K Y c) := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply, ← he, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  change e.app _ (Proj.awayToSection _ (MvPolynomial.X k)
    (projectiveChartAffineToLocalization K k (MvPolynomial.C c))) = _
  rw [projectiveChartAffineToLocalization_C, ← polynomialProjective_base_constant_chart K k c]
  have hnat := ConcreteCategory.congr_hom (e.naturality (homOfLE (le_top :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k) ≤ ⊤)).op)
    ((polynomialProjectiveToBase n K).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
  exact hnat.trans rfl

end MixedFujita
