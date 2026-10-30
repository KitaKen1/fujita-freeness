/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InvertibleOpenRestriction
public import MixedFujita.ProjectiveCartierIdealIso
public import MixedFujita.ProjectiveNonzeroHypersurface

/-!
A representation of an existing IdealSheafData by an invertible module sheaf
included in the structure sheaf. Injectivity and exact images on the affine
basis identify the represented ideal, including multiplicities.

RelativeCartierPresentation adds flatness of that ideal's actual closed
subscheme over the base. These are local project interfaces for the standard
invertible-ideal definition, not upstream CartierDivisor predicates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

structure InvertibleIdealPresentation {X : Scheme.{u}} (I : X.IdealSheafData) where
  moduleSheaf : X.Modules
  invertible : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X moduleSheaf
  inclusion : moduleSheaf ⟶ SheafOfModules.unit X.ringCatSheaf
  injective : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app inclusion U)
  image_eq : ∀ U : X.affineOpens,
    Set.range (Scheme.Modules.Hom.app inclusion U.1) = (I.ideal U : Set Γ(X, U.1))

structure RelativeCartierPresentation {X S : Scheme.{u}} (p : X ⟶ S)
    (I : X.IdealSheafData) extends InvertibleIdealPresentation I where
  flat : Flat (I.subschemeι ≫ p)

theorem invertibleIdealPresentation_inclusion_mono
    {X : Scheme.{u}} {I : X.IdealSheafData} (P : InvertibleIdealPresentation I) :
    Mono P.inclusion := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  exact fun U => P.injective U.unop

theorem invertibleIdealPresentation_mem_image_iff
    {X : Scheme.{u}} {I : X.IdealSheafData} (P : InvertibleIdealPresentation I)
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ Set.range (Scheme.Modules.Hom.app P.inclusion U.1) ↔ a ∈ I.ideal U := by
  rw [P.image_eq]
  rfl

noncomputable def projectiveHypersurfaceInvertibleIdealPresentation
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    InvertibleIdealPresentation (projectiveHypersurfaceIdealSheaf f d hf) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let D := projectiveHomogeneousCartier R k₀ d f hf h0
  have hD : D.IsEffective := projectiveHomogeneousCartier_isEffective R k₀ d f hf h0
  exact
    { moduleSheaf := (-D).sheaf
      invertible := (-D).isInvertible_sheaf
      inclusion := negativeCartierToUnit _ D hD
      injective := negativeCartierToUnit_app_injective _ D hD
      image_eq := projectiveHomogeneousCartier_inclusion_range R k₀ d f hf h0 }

noncomputable def projectiveHypersurfaceOpenInvertibleIdealPresentation
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    {Y : Scheme.{u}} (j : Y ⟶ polynomialProjectiveScheme n R) [IsOpenImmersion j] :
    InvertibleIdealPresentation ((projectiveHypersurfaceIdealSheaf f d hf).comap j) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let D := projectiveHomogeneousCartier R k₀ d f hf h0
  have hD : D.IsEffective := projectiveHomogeneousCartier_isEffective R k₀ d f hf h0
  exact
    { moduleSheaf := (-D).sheaf.restrict j
      invertible := negativeCartier_restrict_isInvertible _ D j
      inclusion := negativeCartierToOpenUnit _ D hD j
      injective := negativeCartierToOpenUnit_app_injective _ D hD j
      image_eq := projectiveHomogeneousCartier_openInclusion_range R k₀ d f hf h0 j }

end MixedFujita
