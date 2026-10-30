/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveIntegral
public import MixedFujita.ProjectiveChartOverlaps
public import MixedFujita.RegularEquationCartier

/-!
The equations f/X_i^d of a nonzero homogeneous polynomial over an
integral domain glue to an actual Cartier divisor on polynomial projective
space. The transition units are (X_j/X_i)^d, transported through the
actual structure-sheaf section maps on coordinate intersections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} (R : Type*) [CommRing R]

noncomputable def projectiveHomogeneousEquation (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    Γ(polynomialProjectiveScheme n R,
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :=
  Proj.awayToSection _ (MvPolynomial.X k)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
      (by simpa using hf))

noncomputable def projectiveOverlapSectionMap (k j : Fin n) :
    CommRingCat.of (projectiveChartOverlapRing R k j) ⟶
      Γ(polynomialProjectiveScheme n R,
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)) :=
  Proj.awayToSection _ (MvPolynomial.X k * MvPolynomial.X j) ≫
    (polynomialProjectiveScheme n R).presheaf.map
      (eqToHom (Proj.basicOpen_mul _ _ _).symm).op

theorem projectiveOverlapSectionMap_left (k j : Fin n) :
    CommRingCat.ofHom (projectiveChartOverlapFromLeft R k j) ≫
      projectiveOverlapSectionMap R k j =
      Proj.awayToSection _ (MvPolynomial.X k) ≫
        (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_left).op := by
  rw [projectiveOverlapSectionMap, ← Category.assoc, projectiveChartOverlapFromLeft]
  rw [Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (f := MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R j) rfl]
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem projectiveOverlapSectionMap_right (k j : Fin n) :
    CommRingCat.ofHom (projectiveChartOverlapFromRight R k j) ≫
      projectiveOverlapSectionMap R k j =
      Proj.awayToSection _ (MvPolynomial.X j) ≫
        (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_right).op := by
  rw [projectiveOverlapSectionMap, ← Category.assoc, projectiveChartOverlapFromRight]
  rw [Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (f := MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R k) (mul_comm _ _)]
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem projectiveHomogeneousEquation_overlap (k j : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    ∃ w : Γ(polynomialProjectiveScheme n R,
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j))ˣ,
      (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_left).op
          (projectiveHomogeneousEquation R k d f hf) =
        (w : Γ(polynomialProjectiveScheme n R,
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j))) *
          (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_right).op
          (projectiveHomogeneousEquation R j d f hf) := by
  let w := (projectiveChartOverlapUnit_isUnit R k j).unit ^ d
  refine ⟨Units.map (projectiveOverlapSectionMap R k j).hom w, ?_⟩
  have h := congrArg (projectiveOverlapSectionMap R k j)
    (projectiveChartOverlap_fraction R k j d f hf)
  rw [(projectiveOverlapSectionMap R k j).hom.map_mul,
    (projectiveOverlapSectionMap R k j).hom.map_pow] at h
  have hleft := ConcreteCategory.congr_hom (projectiveOverlapSectionMap_left R k j)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
      (by simpa using hf))
  have hright := ConcreteCategory.congr_hom (projectiveOverlapSectionMap_right R k j)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R j) d f
      (by simpa using hf))
  dsimp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hleft hright
  rw [hleft, hright] at h
  simpa [w, projectiveHomogeneousEquation] using h

theorem projectiveHomogeneousEquation_ne_zero (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    projectiveHomogeneousEquation R k d f hf ≠ 0 := by
  intro h
  apply h0
  apply (homogeneousChartFraction_eq_zero_iff k d f hf).mp
  let e := Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  simpa only [e, Proj.basicOpenIsoAway_hom, projectiveHomogeneousEquation, map_zero] using h

theorem polynomialProjective_coordinate_open_nonempty [IsDomain R] (k : Fin n) :
    Nonempty (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) := by
  refine ⟨⟨polynomialProjectiveZeroPoint R k, ?_⟩⟩
  rw [Proj.mem_basicOpen]
  intro h
  have h' : MvPolynomial.X k ∈ (⊥ : Ideal (MvPolynomial (Fin n) R)) := h
  exact MvPolynomial.X_ne_zero k (Ideal.mem_bot.mp h')

theorem projectiveHomogeneousEquation_germ_regular [IsDomain R] (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (x : polynomialProjectiveScheme n R)
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) :
    letI := polynomialProjectiveScheme_isIntegral R k
    letI := polynomialProjective_coordinate_open_nonempty R k
    (regularEquationRationalUnit (polynomialProjectiveScheme n R) _
        (projectiveHomogeneousEquation R k d f hf)
        (projectiveHomogeneousEquation_ne_zero R k d f hf h0) :
          (polynomialProjectiveScheme n R).functionField) ∈
      (algebraMap ((polynomialProjectiveScheme n R).presheaf.stalk x)
        (polynomialProjectiveScheme n R).functionField).range ∧
    (polynomialProjectiveScheme n R).presheaf.germ _ x hx
      (projectiveHomogeneousEquation R k d f hf) ∈
        nonZeroDivisors ((polynomialProjectiveScheme n R).presheaf.stalk x) := by
  let := polynomialProjectiveScheme_isIntegral R k
  let := polynomialProjective_coordinate_open_nonempty R k
  exact ⟨regularEquationRationalUnit_mem_stalk_range _ _ _
    (projectiveHomogeneousEquation_ne_zero R k d f hf h0) x hx,
    regularEquation_germ_mem_nonZeroDivisors _ _ _
      (projectiveHomogeneousEquation_ne_zero R k d f hf h0) x hx⟩

theorem projectiveHomogeneousCartier_existsUnique [IsDomain R] (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    letI : ∀ k : Fin n, Nonempty (Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :=
        fun k => polynomialProjective_coordinate_open_nonempty R k
    ∃! D : CartierDivisor (polynomialProjectiveScheme n R), ∀ k : Fin n,
      (cartierDivisorSheaf (polynomialProjectiveScheme n R)).1.map
        (homOfLE (show Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
          (MvPolynomial.X k) ≤ ⊤ from le_top)).op D =
        rationalUnitClass (polynomialProjectiveScheme n R)
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))
          (Additive.ofMul (regularEquationRationalUnit (polynomialProjectiveScheme n R) _
            (projectiveHomogeneousEquation R k d f hf)
            (projectiveHomogeneousEquation_ne_zero R k d f hf h0))) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let : ∀ k : Fin n, Nonempty (Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :=
      fun k => polynomialProjective_coordinate_open_nonempty R k
  apply cartierDivisor_existsUnique_of_regularEquations (polynomialProjectiveScheme n R)
    (fun k => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))
    (polynomialProjective_coordinate_opens_cover n R)
    (fun k => projectiveHomogeneousEquation R k d f hf)
    (fun k => projectiveHomogeneousEquation_ne_zero R k d f hf h0)
  exact fun k j => projectiveHomogeneousEquation_overlap R k j d f hf

noncomputable def projectiveHomogeneousCartier [IsDomain R] (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    CartierDivisor (polynomialProjectiveScheme n R) :=
  (projectiveHomogeneousCartier_existsUnique R k₀ d f hf h0).exists.choose

theorem projectiveHomogeneousCartier_restrict [IsDomain R] (k₀ k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    letI := polynomialProjective_coordinate_open_nonempty R k
    (cartierDivisorSheaf (polynomialProjectiveScheme n R)).1.map
        (homOfLE (show Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
          (MvPolynomial.X k) ≤ ⊤ from le_top)).op
          (projectiveHomogeneousCartier R k₀ d f hf h0) =
      rationalUnitClass (polynomialProjectiveScheme n R)
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))
        (Additive.ofMul (regularEquationRationalUnit (polynomialProjectiveScheme n R) _
          (projectiveHomogeneousEquation R k d f hf)
          (projectiveHomogeneousEquation_ne_zero R k d f hf h0))) :=
  (projectiveHomogeneousCartier_existsUnique R k₀ d f hf h0).exists.choose_spec k

end MixedFujita
