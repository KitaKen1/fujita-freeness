/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineQuotientSubschemes
public import MixedFujita.ProjectiveIdealSheafGluing
public import MixedFujita.ProjectiveBaseChange
public import MixedFujita.ProjectiveChartFlatHypersurfaces
public import MixedFujita.ProjectiveDehomogenizationCoefficients

/-!
The actual global projective hypersurface ideal sheaf and its affine
coordinate restrictions as quotient-ring Spec hypersurfaces. The chart
isomorphisms preserve both the ambient immersion and coefficient projection.
Relative effective Cartier and lct constructions remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type u} [CommRing R]

noncomputable def projectiveHypersurfaceIdealSheaf
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    (polynomialProjectiveScheme n R).IdealSheafData :=
  homogeneousProjectiveIdealSheaf ({()} : Finset Unit) (fun _ => f) d (fun _ _ => hf)

noncomputable def projectiveHypersurfaceProjection
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    (projectiveHypersurfaceIdealSheaf f d hf).subscheme ⟶ Spec (CommRingCat.of R) :=
  (projectiveHypersurfaceIdealSheaf f d hf).subschemeι ≫ polynomialProjectiveToBase n R

noncomputable def projectiveAffineChartAmbientMap (R : Type u) [CommRing R] (k : Fin n) :
    Spec (CommRingCat.of (MvPolynomial {j : Fin n // j ≠ k} R)) ⟶
      polynomialProjectiveScheme n R :=
  (polynomialProjectiveAffineChartIso R k).inv ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι

theorem projectiveAffineChartAmbientMap_toBase (R : Type u) [CommRing R] (k : Fin n) :
    projectiveAffineChartAmbientMap R k ≫ polynomialProjectiveToBase n R =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j : Fin n // j ≠ k} R)) := by
  simp only [projectiveAffineChartAmbientMap, Category.assoc,
    polynomialProjectiveAffineChart_toBase, Iso.inv_hom_id_assoc]

theorem projectiveHypersurfaceIdealSheaf_affine_restrict
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (k : Fin n) :
    (projectiveHypersurfaceIdealSheaf f d hf).comap (projectiveAffineChartAmbientMap R k) =
      specIdealSheaf (Ideal.span ({projectiveDehomogenize R k f} :
        Set (MvPolynomial {j : Fin n // j ≠ k} R))) := by
  rw [projectiveHypersurfaceIdealSheaf, projectiveAffineChartAmbientMap,
    Scheme.IdealSheafData.comap_comp, homogeneousProjectiveIdealSheaf_restrict,
    projectiveChartIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  simp only [polynomialProjectiveAffineChartIso, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  change (specIdealSheaf (homogeneousChartLocalizationIdeal ({()} : Finset Unit)
    (fun _ => f) d (fun _ _ => hf) k)).comap
      (Spec.map (CommRingCat.ofHom (projectiveChartRingEquiv R k).toRingHom)) = _
  rw [specIdealSheaf_comap, homogeneousChartLocalizationIdeal_affine]
  have : Nonempty ({()} : Finset Unit) := ⟨⟨(), by simp⟩⟩
  simp [projectiveChartIdeal, Ideal.map_span]

noncomputable def projectiveHypersurfaceAffineChartIso
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (k : Fin n) :
    Spec (CommRingCat.of (MvPolynomial {j : Fin n // j ≠ k} R ⧸
      Ideal.span ({projectiveDehomogenize R k f} :
        Set (MvPolynomial {j : Fin n // j ≠ k} R)))) ≅
      pullback (projectiveAffineChartAmbientMap R k)
        (projectiveHypersurfaceIdealSheaf f d hf).subschemeι :=
  specQuotientIdealSheafIso _ ≪≫
    idealSheafPullbackIso _ _ _ (projectiveHypersurfaceIdealSheaf_affine_restrict f d hf k)

theorem projectiveHypersurfaceAffineChartIso_hom_fst
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (k : Fin n) :
    (projectiveHypersurfaceAffineChartIso f d hf k).hom ≫ pullback.fst _ _ =
      polynomialHypersurfaceInclusion (projectiveDehomogenize R k f) := by
  simp only [projectiveHypersurfaceAffineChartIso, Iso.trans_hom, Category.assoc,
    idealSheafPullbackIso_hom_fst, specQuotientIdealSheafIso_hom_ι,
    polynomialHypersurfaceInclusion]

theorem projectiveHypersurfaceAffineChartIso_hom_toBase
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (k : Fin n) :
    (projectiveHypersurfaceAffineChartIso f d hf k).hom ≫ pullback.snd _ _ ≫
      projectiveHypersurfaceProjection f d hf =
        polynomialHypersurfaceProjection (projectiveDehomogenize R k f) := by
  simp only [projectiveHypersurfaceProjection, ← Category.assoc]
  rw [Category.assoc _ (pullback.snd _ _) _, ← pullback.condition,
    ← Category.assoc, projectiveHypersurfaceAffineChartIso_hom_fst,
    Category.assoc, projectiveAffineChartAmbientMap_toBase,
    polynomialHypersurfaceInclusion_projection]

@[reducible]
noncomputable def polynomialProjectiveAffineOpenCover (R : Type u) [CommRing R] :
    (polynomialProjectiveScheme n R).OpenCover :=
  (polynomialProjectiveCoordinateOpenCover R).copy (Fin n)
    (fun k => Spec (CommRingCat.of (MvPolynomial {j : Fin n // j ≠ k} R)))
    (projectiveAffineChartAmbientMap R) (Equiv.refl _)
    (fun k => (polynomialProjectiveAffineChartIso R k).symm) (fun _ => rfl)

theorem projectiveHypersurfaceProjection_flat_of_chart_units
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (hu : ∀ k : Fin n, ∃ q : {j : Fin n // j ≠ k} →₀ ℕ,
      IsUnit ((projectiveDehomogenize R k f).coeff q)) :
    Flat (projectiveHypersurfaceProjection f d hf) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    ((polynomialProjectiveAffineOpenCover R).pullback₂
      (projectiveHypersurfaceIdealSheaf f d hf).subschemeι)
  intro k
  change Fin n at k
  change Flat (pullback.snd (projectiveAffineChartAmbientMap R k)
    (projectiveHypersurfaceIdealSheaf f d hf).subschemeι ≫
      projectiveHypersurfaceProjection f d hf)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (projectiveHypersurfaceAffineChartIso f d hf k).hom,
    projectiveHypersurfaceAffineChartIso_hom_toBase]
  obtain ⟨q, hq⟩ := hu k
  exact polynomialHypersurfaceProjection_flat _ q hq

theorem projectiveHypersurfaceProjection_locallyOfFinitePresentation
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    LocallyOfFinitePresentation (projectiveHypersurfaceProjection f d hf) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    ((polynomialProjectiveAffineOpenCover R).pullback₂
      (projectiveHypersurfaceIdealSheaf f d hf).subschemeι)
  intro k
  change Fin n at k
  change LocallyOfFinitePresentation
    (pullback.snd (projectiveAffineChartAmbientMap R k)
      (projectiveHypersurfaceIdealSheaf f d hf).subschemeι ≫
        projectiveHypersurfaceProjection f d hf)
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)
    (projectiveHypersurfaceAffineChartIso f d hf k).hom,
    projectiveHypersurfaceAffineChartIso_hom_toBase]
  exact polynomialHypersurfaceProjection_locallyOfFinitePresentation _

theorem projectiveHypersurfaceProjection_isProper
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    IsProper (projectiveHypersurfaceProjection f d hf) := by
  let _ := polynomialProjectiveToBase_isProper n R
  unfold projectiveHypersurfaceProjection
  infer_instance

theorem projectiveHypersurfaceProjection_pullback_flat_of_chart_units
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (hu : ∀ k : Fin n, ∃ q : {j : Fin n // j ≠ k} →₀ ℕ,
      IsUnit ((projectiveDehomogenize R k f).coeff q))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) :
    Flat (pullback.snd (projectiveHypersurfaceProjection f d hf) g) := by
  let _ := projectiveHypersurfaceProjection_flat_of_chart_units f d hf hu
  infer_instance

theorem projectiveHypersurfaceProjection_pullback_locallyOfFinitePresentation
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) :
    LocallyOfFinitePresentation (pullback.snd (projectiveHypersurfaceProjection f d hf) g) := by
  let _ := projectiveHypersurfaceProjection_locallyOfFinitePresentation f d hf
  infer_instance

theorem projectiveHypersurfaceProjection_flat_of_unit_coefficient
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    Flat (projectiveHypersurfaceProjection f d hf) :=
  projectiveHypersurfaceProjection_flat_of_chart_units f d hf
    (fun k => projectiveDehomogenize_has_unit_coefficient k f d hf q hq)

theorem projectiveHypersurfaceProjection_mapped_flat_of_unit_coefficient
    {S : Type u} [CommRing S] (c : R →+* S)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    Flat (projectiveHypersurfaceProjection (MvPolynomial.map c f) d (hf.map c)) := by
  apply projectiveHypersurfaceProjection_flat_of_unit_coefficient _ d (hf.map c) q
  rw [MvPolynomial.coeff_map]
  exact hq.map c

theorem projectiveHypersurfaceProjection_pullback_flat_of_unit_coefficient
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : IsUnit (f.coeff q))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) :
    Flat (pullback.snd (projectiveHypersurfaceProjection f d hf) g) := by
  let _ := projectiveHypersurfaceProjection_flat_of_unit_coefficient f d hf q hq
  infer_instance

theorem projectiveHomogeneous_localized_global_hypersurface_cover
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (p : PrimeSpectrum R) (hp : p ∈ polynomialNonzeroLocus f) :
    ∃ q ∈ f.support, f.coeff q ∉ p.asIdeal ∧
      let S := Localization.Away (f.coeff q)
      let F := MvPolynomial.map (algebraMap R S) f
      let hF := hf.map (algebraMap R S)
      Flat (projectiveHypersurfaceProjection F d hF) ∧
        LocallyOfFinitePresentation (projectiveHypersurfaceProjection F d hF) ∧
          IsProper (projectiveHypersurfaceProjection F d hF) := by
  obtain ⟨q, hq, hpq⟩ := polynomialNonzeroLocus_local_coefficient f p hp
  refine ⟨q, hq, hpq, ?_, projectiveHypersurfaceProjection_locallyOfFinitePresentation _ d _,
    projectiveHypersurfaceProjection_isProper _ d _⟩
  apply projectiveHypersurfaceProjection_flat_of_unit_coefficient _ d _ q
  rw [MvPolynomial.coeff_map]
  exact IsLocalization.Away.algebraMap_isUnit (f.coeff q)

end MixedFujita
