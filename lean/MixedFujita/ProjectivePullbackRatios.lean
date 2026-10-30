/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePullbackCartier

/-!
Equal-degree actual projective equations have the same explicit unit
transition. Their ratio in an integral source's actual function field
therefore does not depend on the nonempty coordinate chart.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {n : ℕ} {R : Type u} [CommRing R]

noncomputable def projectiveHomogeneousOverlapUnit (k j : Fin n) (d : ℕ) :
    Γ(polynomialProjectiveScheme n R,
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j))ˣ :=
  Units.map (projectiveOverlapSectionMap R k j).hom.toMonoidHom
    ((projectiveChartOverlapUnit_isUnit R k j).unit ^ d)

theorem projectiveHomogeneousEquation_overlap_explicit (k j : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_left).op
        (projectiveHomogeneousEquation R k d f hf) =
      (projectiveHomogeneousOverlapUnit (R := R) k j d : Γ(polynomialProjectiveScheme n R,
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j))) *
        (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_right).op
          (projectiveHomogeneousEquation R j d f hf) := by
  have h := congrArg (projectiveOverlapSectionMap R k j)
    (projectiveChartOverlap_fraction R k j d f hf)
  rw [(projectiveOverlapSectionMap R k j).hom.map_mul,
    (projectiveOverlapSectionMap R k j).hom.map_pow] at h
  have hl := ConcreteCategory.congr_hom (projectiveOverlapSectionMap_left R k j)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
      (by simpa using hf))
  have hr := ConcreteCategory.congr_hom (projectiveOverlapSectionMap_right R k j)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R j) d f
      (by simpa using hf))
  dsimp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hl hr
  rw [hl, hr] at h
  simpa [projectiveHomogeneousOverlapUnit, projectiveHomogeneousEquation] using h

variable {Y : Scheme.{u}} (e : Y ⟶ polynomialProjectiveScheme n R)

noncomputable def projectivePullbackHomogeneousOverlapUnit (k j : Fin n) (d : ℕ) :
    Γ(Y, projectivePullbackCoordinateOpen e k ⊓ projectivePullbackCoordinateOpen e j)ˣ :=
  Units.map (e.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (MvPolynomial.X k) ⊓ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X j))).hom.toMonoidHom
    (projectiveHomogeneousOverlapUnit (R := R) k j d)

theorem projectivePullbackHomogeneousEquation_overlap_explicit (k j : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    Y.presheaf.map (homOfLE inf_le_left).op
        (projectivePullbackHomogeneousEquation e k d f hf) =
      (projectivePullbackHomogeneousOverlapUnit e k j d :
        Γ(Y, projectivePullbackCoordinateOpen e k ⊓ projectivePullbackCoordinateOpen e j)) *
        Y.presheaf.map (homOfLE inf_le_right).op
          (projectivePullbackHomogeneousEquation e j d f hf) := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)
  have h := congrArg (e.app U) (projectiveHomogeneousEquation_overlap_explicit k j d f hf)
  rw [(e.app U).hom.map_mul] at h
  have hk := ConcreteCategory.congr_hom
    (e.naturality (homOfLE (show U ≤ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) from inf_le_left)).op)
      (projectiveHomogeneousEquation R k d f hf)
  have hj := ConcreteCategory.congr_hom
    (e.naturality (homOfLE (show U ≤ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j) from inf_le_right)).op)
      (projectiveHomogeneousEquation R j d f hf)
  dsimp only [CommRingCat.hom_comp, RingHom.comp_apply] at hk hj
  exact hk.symm.trans (h.trans (congrArg (fun a => e.app U
    (projectiveHomogeneousOverlapUnit (R := R) k j d) * a) hj))

variable [IsIntegral Y]

noncomputable def projectivePullbackHomogeneousRationalUnit
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hgeneric : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) : Y.functionFieldˣ :=
  regularEquationRationalUnit Y (projectivePullbackCoordinateOpen e k.val)
    (projectivePullbackHomogeneousEquation e k.val d f hf)
    (projectivePullbackHomogeneousEquation_ne_zero e k.val d f hf hd hgeneric)

theorem projectivePullbackHomogeneousRationalUnit_overlap
    (k j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hgeneric : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    letI := integral_opens_inter_nonempty Y (projectivePullbackCoordinateOpen e k.val)
      (projectivePullbackCoordinateOpen e j.val)
    projectivePullbackHomogeneousRationalUnit e k d f hf hd hgeneric =
      Units.map (Y.germToFunctionField
        (projectivePullbackCoordinateOpen e k.val ⊓ projectivePullbackCoordinateOpen e j.val)).hom
          (projectivePullbackHomogeneousOverlapUnit e k.val j.val d) *
        projectivePullbackHomogeneousRationalUnit e j d f hf hd hgeneric :=
  regularEquationRationalUnit_eq_of_overlap Y _ _ _ _ _
    (projectivePullbackHomogeneousEquation_overlap_explicit e k.val j.val d f hf)

noncomputable def projectivePullbackHomogeneousRatio
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d)
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous d) (hd : 0 < d)
    (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal) : Y.functionFieldˣ :=
  projectivePullbackHomogeneousRationalUnit e k d f hf hd hfgen *
    (projectivePullbackHomogeneousRationalUnit e k d g hg hd hggen)⁻¹

theorem projectivePullbackHomogeneousRatio_chart_independent
    (k j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d)
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous d) (hd : 0 < d)
    (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    projectivePullbackHomogeneousRatio e k d f hf g hg hd hfgen hggen =
      projectivePullbackHomogeneousRatio e j d f hf g hg hd hfgen hggen := by
  let := integral_opens_inter_nonempty Y (projectivePullbackCoordinateOpen e k.val)
    (projectivePullbackCoordinateOpen e j.val)
  unfold projectivePullbackHomogeneousRatio
  rw [projectivePullbackHomogeneousRationalUnit_overlap e k j d f hf hd hfgen,
    projectivePullbackHomogeneousRationalUnit_overlap e k j d g hg hd hggen]
  simpa only [div_eq_mul_inv] using
    (mul_div_mul_left_eq_div
      (projectivePullbackHomogeneousRationalUnit e j d f hf hd hfgen)
      (projectivePullbackHomogeneousRationalUnit e j d g hg hd hggen)
      (Units.map (Y.germToFunctionField
        (projectivePullbackCoordinateOpen e k.val ⊓ projectivePullbackCoordinateOpen e j.val)).hom
          (projectivePullbackHomogeneousOverlapUnit e k.val j.val d)))

end MixedFujita
