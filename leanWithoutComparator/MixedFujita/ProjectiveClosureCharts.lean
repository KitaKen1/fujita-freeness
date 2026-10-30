/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveArbitraryBaseChange
public import MixedFujita.ProjectiveBaseConstants
public import MixedFujita.ProjectivePullbackEquations
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
The closure of a projective scheme over a smaller coefficient ring and its charts (step 10, R4-3).

For a morphism `e : Y → ℙ_S` and a ring map `c : R → S`, the closure of `Y` in `ℙ_R` is the
scheme-theoretic image of `Y → ℙ_S → ℙ_R` (`projectiveClosure c e`). In the application `Y = T_K`
is a closed subscheme of projective space over a field `K` and `R = A` is a finitely generated
subring of `K`; the closure is the model `T_A`.

* `projectiveChartRingMap e k`: the functions on the `k`-th coordinate chart of a scheme over `ℙ_R`
  as polynomials in the ratios `X_j / X_k`; surjective for a closed immersion, and constants are
  the base constants (`projectiveChartRingMap_C`).
* `awayToSection_comp_coefficientMap_appLE`: the coefficient map `ℙ_S → ℙ_R` sends the ratio
  sections over `D₊(X_k)` to the ratio sections; it is affine
  (`polynomialProjectiveCoefficientMap_isAffineHom`).
* `closureChartMap c e k`: the comparison of the functions on the `k`-th chart of the closure with
  those of the `k`-th chart of `Y`; it is injective (`closureChartMap_injective`, from Mathlib's
  `Hom.toImage_app_injective`) and sends the ratios to the ratios
  (`closureChartMap_projectiveChartRingMap`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ}

section Chart

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (e : Y ⟶ polynomialProjectiveScheme n R)

/-- The functions on the `k`-th coordinate chart of a scheme over projective space over a ring,
as images of polynomials in the ratios `X_j / X_k`. -/
noncomputable def projectiveChartRingMap (k : Fin n) :
    MvPolynomial {j : Fin n // j ≠ k} R →+* Γ(Y, projectivePullbackCoordinateOpen e k) :=
  (e.app _).hom.comp ((Proj.awayToSection
    (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).hom.comp
      (projectiveChartAffineToLocalization R k))

theorem projectiveChartRingMap_surjective [IsClosedImmersion e] (k : Fin n) :
    Function.Surjective (projectiveChartRingMap e k) := by
  have hU := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
  let a := Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
  have ha : Function.Surjective (Proj.awayToSection
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) := by
    simpa only [a, Proj.basicOpenIsoAway_hom] using
      (ConcreteCategory.bijective_of_isIso a.hom).2
  exact (e.app_surjective _ hU).comp (ha.comp (projectiveChartRingEquiv R k).symm.surjective)

/-- Constant polynomials go to the base constants of the chart. -/
theorem projectiveChartRingMap_C (q : Y ⟶ Spec (CommRingCat.of R))
    (he : e ≫ polynomialProjectiveToBase n R = q) (k : Fin n) (r : R) :
    projectiveChartRingMap e k (MvPolynomial.C r) =
      q.appLE ⊤ (projectivePullbackCoordinateOpen e k) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  subst he
  change e.app _ (Proj.awayToSection _ (MvPolynomial.X k)
    (projectiveChartAffineToLocalization R k (MvPolynomial.C r))) = _
  rw [projectiveChartAffineToLocalization_C, ← polynomialProjective_base_constant_chart R k r,
    ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  rfl

end Chart

section Coefficient

variable {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S)

theorem awayToSection_comp_coefficientMap_appLE_aux (k : Fin n) (b : MvPolynomial (Fin n) S)
    (hb : b = MvPolynomial.map c (MvPolynomial.X k)) (hb₁ : b.IsHomogeneous 1)
    (m : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) S) b)
    (hm : ∀ d a (ha : a.IsHomogeneous d),
      m (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d a
        (by simpa using ha)) =
      HomogeneousLocalization.Away.mk _ hb₁ d (MvPolynomial.map c a)
        (by simpa using ha.map c))
    (h : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) b ≤
      polynomialProjectiveCoefficientMap c ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ≫
        (polynomialProjectiveCoefficientMap c).appLE _ _ h =
      CommRingCat.ofHom m ≫
        Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) S) b := by
  subst b
  have hmap : m = HomogeneousLocalization.Away.map (polynomialScalarGradedMap c)
      (MvPolynomial.X k) := by
    apply RingHom.ext
    intro x
    obtain ⟨d, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.isHomogeneous_X R k) x
    rw [hm d a (by simpa using ha)]
    exact (HomogeneousLocalization.Away.map_mk (polynomialScalarGradedMap c)
      (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) d a ha).symm
  subst hmap
  exact Proj.awayToSection_comp_appLE (polynomialScalarGradedMap c)
    (polynomialScalarGradedMap_irrelevant c) (MvPolynomial.isHomogeneous_X R k)

/-- The coefficient map `ℙ_S → ℙ_R` sends the ratio sections over `D₊(X_k)` to the ratio
sections. -/
theorem awayToSection_comp_coefficientMap_appLE (k : Fin n)
    (h : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k) ≤
      polynomialProjectiveCoefficientMap c ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ≫
        (polynomialProjectiveCoefficientMap c).appLE _ _ h =
      CommRingCat.ofHom (projectiveChartScalarMap c k) ≫
        Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k) :=
  awayToSection_comp_coefficientMap_appLE_aux c k (MvPolynomial.X k)
    (MvPolynomial.map_X c k).symm (MvPolynomial.isHomogeneous_X S k)
    (projectiveChartScalarMap c k) (projectiveChartScalarMap_mk c k) h

/-- The coefficient map is affine (a base change of `Spec S → Spec R`). -/
theorem polynomialProjectiveCoefficientMap_isAffineHom :
    IsAffineHom (polynomialProjectiveCoefficientMap (n := n) c) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (polynomialProjectiveCoefficientMap_isPullback c).flip inferInstance

theorem projectiveChartScalarMap_affineToLocalization (k : Fin n)
    (p : MvPolynomial {j : Fin n // j ≠ k} R) :
    projectiveChartScalarMap c k (projectiveChartAffineToLocalization R k p) =
      projectiveChartAffineToLocalization S k (MvPolynomial.map c p) := by
  simp only [projectiveChartScalarMap, RingHom.comp_apply, projectiveChartAffine_roundtrip]

end Coefficient

section Closure

variable {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n S)

/-- The closure of `Y` in projective space over `R`: the scheme-theoretic image of
`Y → ℙ_S → ℙ_R`. -/
noncomputable abbrev projectiveClosure : Scheme.{u} :=
  (e ≫ polynomialProjectiveCoefficientMap c).image

/-- The closed immersion of the closure into projective space over `R`. -/
noncomputable abbrev projectiveClosureι : projectiveClosure c e ⟶ polynomialProjectiveScheme n R :=
  (e ≫ polynomialProjectiveCoefficientMap c).imageι

/-- The map from `Y` to its closure. -/
noncomputable abbrev projectiveClosureMap : Y ⟶ projectiveClosure c e :=
  (e ≫ polynomialProjectiveCoefficientMap c).toImage

theorem projectiveClosureMap_comp_ι :
    projectiveClosureMap c e ≫ projectiveClosureι c e = e ≫ polynomialProjectiveCoefficientMap c :=
  Scheme.Hom.toImage_imageι _

theorem projectiveClosureMap_preimage_chart (k : Fin n) :
    projectiveClosureMap c e ⁻¹ᵁ projectivePullbackCoordinateOpen (projectiveClosureι c e) k =
      projectivePullbackCoordinateOpen e k := by
  rw [projectivePullbackCoordinateOpen, projectivePullbackCoordinateOpen,
    ← Scheme.Hom.comp_preimage, projectiveClosureMap_comp_ι, Scheme.Hom.comp_preimage,
    polynomialProjectiveCoefficientMap_preimage_coordinate]

/-- The comparison of the functions on the `k`-th chart of the closure with those of the `k`-th
chart of `Y`. -/
noncomputable def closureChartMap (k : Fin n) :
    Γ(projectiveClosure c e, projectivePullbackCoordinateOpen (projectiveClosureι c e) k) →+*
      Γ(Y, projectivePullbackCoordinateOpen e k) :=
  ((projectiveClosureMap c e).appLE _ _ (projectiveClosureMap_preimage_chart c e k).ge).hom

theorem closureChartMap_injective [QuasiCompact (e ≫ polynomialProjectiveCoefficientMap c)]
    (k : Fin n) : Function.Injective (closureChartMap c e k) := by
  have h1 := Scheme.Hom.toImage_app_injective (e ≫ polynomialProjectiveCoefficientMap c)
    (polynomialProjectiveCoordinateAffineOpen R k)
  have hiso : IsIso (Y.presheaf.map
      (homOfLE (projectiveClosureMap_preimage_chart c e k).ge).op) := by
    rw [show homOfLE (projectiveClosureMap_preimage_chart c e k).ge =
      eqToHom (projectiveClosureMap_preimage_chart c e k).symm from Subsingleton.elim _ _]
    infer_instance
  have h2 := (ConcreteCategory.bijective_of_isIso (Y.presheaf.map
      (homOfLE (projectiveClosureMap_preimage_chart c e k).ge).op)).1
  exact h2.comp h1

/-- The comparison map sends the ratios to the ratios. -/
theorem closureChartMap_projectiveChartRingMap (k : Fin n)
    (p : MvPolynomial {j : Fin n // j ≠ k} R) :
    closureChartMap c e k (projectiveChartRingMap (projectiveClosureι c e) k p) =
      projectiveChartRingMap e k (MvPolynomial.map c p) := by
  have hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k) ≤
      polynomialProjectiveCoefficientMap c ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) :=
    (polynomialProjectiveCoefficientMap_preimage_coordinate c k).ge
  have key : (projectiveClosureι c e).app _ ≫
      (projectiveClosureMap c e).appLE _ _ (projectiveClosureMap_preimage_chart c e k).ge =
      (polynomialProjectiveCoefficientMap c).appLE _ _ hle ≫ e.app _ := by
    rw [← Scheme.Hom.comp_appLE]
    have hgen : ∀ (g : Y ⟶ polynomialProjectiveScheme n R)
        (hg : g = e ≫ polynomialProjectiveCoefficientMap c)
        (h : projectivePullbackCoordinateOpen e k ≤ g ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)),
        g.appLE _ _ h = (e ≫ polynomialProjectiveCoefficientMap c).appLE _ _ (hg ▸ h) := by
      rintro g rfl h
      rfl
    rw [hgen _ (projectiveClosureMap_comp_ι c e), Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]
    rfl
  change ((projectiveClosureι c e).app _ ≫
      (projectiveClosureMap c e).appLE _ _ (projectiveClosureMap_preimage_chart c e k).ge)
        (Proj.awayToSection _ (MvPolynomial.X k) (projectiveChartAffineToLocalization R k p)) =
    e.app _ (Proj.awayToSection _ (MvPolynomial.X k)
      (projectiveChartAffineToLocalization S k (MvPolynomial.map c p)))
  have h2 : (polynomialProjectiveCoefficientMap c).appLE _ _ hle
      (Proj.awayToSection _ (MvPolynomial.X k) (projectiveChartAffineToLocalization R k p)) =
      Proj.awayToSection _ (MvPolynomial.X k)
        (projectiveChartScalarMap c k (projectiveChartAffineToLocalization R k p)) := by
    have := ConcreteCategory.congr_hom (awayToSection_comp_coefficientMap_appLE c k hle)
      (projectiveChartAffineToLocalization R k p)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.ofHom_apply] at this
    exact this
  rw [key, CommRingCat.comp_apply, h2, projectiveChartScalarMap_affineToLocalization]
  rfl

end Closure

end MixedFujita
