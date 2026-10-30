/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveEquationCartier
public import MixedFujita.EffectiveRegularCartier
public import MixedFujita.ProjectiveHypersurfaceChartIdeals

/-!
The actual homogeneous Cartier divisor is effective and has an actual
invertible sheaf. On each coordinate chart, the regular sections of its
negative sheaf are precisely the multiples of f/X_i^d.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} (R : Type*) [CommRing R] [IsDomain R]

theorem projectiveHomogeneousCartier_isEffective (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    (projectiveHomogeneousCartier R k₀ d f hf h0).IsEffective := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let : ∀ k : Fin n, Nonempty (Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :=
      fun k => polynomialProjective_coordinate_open_nonempty R k
  apply cartier_isEffective_of_regularEquations (polynomialProjectiveScheme n R)
    (projectiveHomogeneousCartier R k₀ d f hf h0)
    (fun k => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))
    (polynomialProjective_coordinate_opens_cover n R)
    (fun k => projectiveHomogeneousEquation R k d f hf)
    (fun k => projectiveHomogeneousEquation_ne_zero R k d f hf h0)
  exact fun k => projectiveHomogeneousCartier_restrict R k₀ k d f hf h0

theorem projectiveHomogeneousCartier_isInvertible_sheaf (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (polynomialProjectiveScheme n R)
      (projectiveHomogeneousCartier R k₀ d f hf h0).sheaf := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  exact (projectiveHomogeneousCartier R k₀ d f hf h0).isInvertible_sheaf

theorem projectiveHomogeneousCartier_negativeSection_mem_iff (k₀ k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (s : Γ(polynomialProjectiveScheme n R,
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    Scheme.Modules.Hom.app (toRationalFunctions (polynomialProjectiveScheme n R)) _ s ∈
      (-(projectiveHomogeneousCartier R k₀ d f hf h0)).sections _ ↔
        s ∈ Ideal.span ({projectiveHomogeneousEquation R k d f hf} :
          Set Γ(polynomialProjectiveScheme n R,
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let := polynomialProjective_coordinate_open_nonempty R k
  exact negativeCartier_regularSection_mem_iff _ _ _ _
    (projectiveHomogeneousEquation_ne_zero R k d f hf h0)
    (projectiveHomogeneousCartier_restrict R k₀ k d f hf h0).symm s

theorem projectiveHomogeneousCartier_isInvertible_negative_sheaf (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (polynomialProjectiveScheme n R)
      (-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  exact (-(projectiveHomogeneousCartier R k₀ d f hf h0)).isInvertible_sheaf

theorem projectiveHomogeneousCartier_negativeSection_mem_hypersurface_ideal_iff
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (W : (polynomialProjectiveScheme n R).affineOpens)
    (s : Γ(polynomialProjectiveScheme n R, W.1)) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    Scheme.Modules.Hom.app (toRationalFunctions (polynomialProjectiveScheme n R)) W.1 s ∈
      (-(projectiveHomogeneousCartier R k₀ d f hf h0)).sections W.1 ↔
        s ∈ (projectiveHypersurfaceIdealSheaf f d hf).ideal W := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let : ∀ k : Fin n, Nonempty (polynomialProjectiveCoordinateAffineOpen R k).1 :=
    fun k => polynomialProjective_coordinate_open_nonempty R k
  exact negativeCartier_regularSection_mem_idealSheaf_iff
    (polynomialProjectiveScheme n R) (projectiveHomogeneousCartier R k₀ d f hf h0)
    (projectiveHypersurfaceIdealSheaf f d hf)
    (polynomialProjectiveCoordinateAffineOpen R)
    (polynomialProjective_coordinate_opens_cover n R)
    (fun k => projectiveHomogeneousEquation R k d f hf)
    (fun k => projectiveHomogeneousEquation_ne_zero R k d f hf h0)
    (fun k => (projectiveHomogeneousCartier_restrict R k₀ k d f hf h0).symm)
    (fun k => projectiveHypersurfaceIdealSheaf_coordinate_ideal R k d f hf) W s

theorem projectiveHomogeneousCartier_negativeSections_eq_hypersurface_ideal_image
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (W : (polynomialProjectiveScheme n R).affineOpens) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sections W.1 :
        Set Γ(rationalFunctions (polynomialProjectiveScheme n R), W.1)) =
      (Scheme.Modules.Hom.app (toRationalFunctions (polynomialProjectiveScheme n R)) W.1) ''
        ((projectiveHypersurfaceIdealSheaf f d hf).ideal W :
          Set Γ(polynomialProjectiveScheme n R, W.1)) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  ext s
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := negativeCartier_section_exists_regular_of_isEffective _
      (projectiveHomogeneousCartier R k₀ d f hf h0)
      (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0) W.1 s hs
    refine ⟨a, ?_, ha⟩
    exact (projectiveHomogeneousCartier_negativeSection_mem_hypersurface_ideal_iff
      R k₀ d f hf h0 W a).mp (ha.symm ▸ hs)
  · rintro ⟨a, ha, rfl⟩
    exact (projectiveHomogeneousCartier_negativeSection_mem_hypersurface_ideal_iff
      R k₀ d f hf h0 W a).mpr ha

end MixedFujita
