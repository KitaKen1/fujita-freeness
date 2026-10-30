/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosureEtaleCoordinates

/-!
The projective embedding of a fibre (step 10, R4-3).

Let `ι : X → ℙ_A` be a morphism and `L` an `A`-algebra. The map `X ×_A L → ℙ_L`
(`fibreProjectiveMap`, the lift into the pullback square
`polynomialProjectiveCoefficientMap_isPullback`) is a base change of `ι` along the coefficient map
`ℙ_L → ℙ_A` (`fibreProjectiveMap_isPullback`, by pasting the two pullback squares over
`Spec L → Spec A`), hence a closed immersion when `ι` is one
(`fibreProjectiveMap_isClosedImmersion`). Its standard charts are the preimages of those of `X`
(`fibreProjectiveMap_preimage_coordinate`), and it pulls the homogeneous equations `f/X_k^d` back to
the pullbacks of those of `X` (`fibreProjectiveMap_homogeneousEquation`, through
`coefficientMap_appLE_homogeneousEquation`). A coordinate `X_k` with a nonempty chart is not in the
ideal of the generic point (`X_notMem_genericPoint_of_nonempty`).

For the closure `T_A` and the residue field `κ`, this is the embedding `e_κ : T_κ → ℙ_κ` whose
hyperplane divisor enters the ample relation on `T_κ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ}

/-- **The coefficient map pulls the homogeneous equations back to the homogeneous equations.** -/
theorem coefficientMap_appLE_homogeneousEquation {R S : Type u} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    (polynomialProjectiveCoefficientMap c).appLE _ _
        (polynomialProjectiveCoefficientMap_preimage_coordinate c k).ge
        (projectiveHomogeneousEquation R k d f hf) =
      projectiveHomogeneousEquation S k d (MvPolynomial.map c f) (hf.map c) := by
  have h := ConcreteCategory.congr_hom (awayToSection_comp_coefficientMap_appLE c k
    (polynomialProjectiveCoefficientMap_preimage_coordinate c k).ge)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f (by simpa using hf))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  rw [projectiveChartScalarMap_mk c k d f hf] at h
  exact h

/-- A coordinate whose chart is nonempty is not in the ideal of the generic point. -/
theorem X_notMem_genericPoint_of_nonempty {R : Type u} [CommRing R] {Y : Scheme.{u}}
    [IsIntegral Y] (e : Y ⟶ polynomialProjectiveScheme n R) (k : Fin n)
    [Nonempty (projectivePullbackCoordinateOpen e k)] :
    MvPolynomial.X k ∉ (e (genericPoint Y)).asHomogeneousIdeal := by
  have hmem : genericPoint Y ∈ projectivePullbackCoordinateOpen e k :=
    ((genericPoint_spec Y).mem_open_set_iff (projectivePullbackCoordinateOpen e k).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (projectivePullbackCoordinateOpen e k)))
  exact (Proj.mem_basicOpen _ _ _).1 hmem

section Fibre

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {X : Scheme.{u}}
  (ι : X ⟶ polynomialProjectiveScheme n A)

/-- **The base change of `ι` to projective space over `L`.** -/
noncomputable def fibreProjectiveMap :
    pullback (ι ≫ polynomialProjectiveToBase n A) (Spec.map (CommRingCat.ofHom (algebraMap A L))) ⟶
      polynomialProjectiveScheme n L :=
  (polynomialProjectiveCoefficientMap_isPullback (n := n) (algebraMap A L)).lift
    (pullback.fst _ _ ≫ ι) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])

theorem fibreProjectiveMap_coefficientMap :
    fibreProjectiveMap (L := L) ι ≫ polynomialProjectiveCoefficientMap (algebraMap A L) =
      pullback.fst _ _ ≫ ι :=
  IsPullback.lift_fst _ _ _ _

theorem fibreProjectiveMap_toBase :
    fibreProjectiveMap (L := L) ι ≫ polynomialProjectiveToBase n L = pullback.snd _ _ :=
  IsPullback.lift_snd _ _ _ _

/-- **The fibre map is a base change of `ι`.** -/
theorem fibreProjectiveMap_isPullback :
    IsPullback (pullback.fst (ι ≫ polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A L)))) (fibreProjectiveMap ι) ι
      (polynomialProjectiveCoefficientMap (algebraMap A L)) := by
  have H := polynomialProjectiveCoefficientMap_isPullback (n := n) (algebraMap A L)
  have Hout := IsPullback.of_hasPullback (ι ≫ polynomialProjectiveToBase n A)
    (Spec.map (CommRingCat.ofHom (algebraMap A L)))
  rw [← fibreProjectiveMap_toBase ι] at Hout
  exact (IsPullback.of_right Hout.flip (fibreProjectiveMap_coefficientMap ι) H.flip).flip

/-- The fibre map of a closed immersion is a closed immersion. -/
theorem fibreProjectiveMap_isClosedImmersion [IsClosedImmersion ι] :
    IsClosedImmersion (fibreProjectiveMap (L := L) ι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    (fibreProjectiveMap_isPullback ι) inferInstance

/-- The standard charts of the fibre are the preimages of those of `X`. -/
theorem fibreProjectiveMap_preimage_coordinate (k : Fin n) :
    projectivePullbackCoordinateOpen (fibreProjectiveMap (L := L) ι) k =
      pullback.fst (ι ≫ polynomialProjectiveToBase n A)
        (Spec.map (CommRingCat.ofHom (algebraMap A L))) ⁻¹ᵁ projectivePullbackCoordinateOpen ι k := by
  rw [projectivePullbackCoordinateOpen, projectivePullbackCoordinateOpen,
    ← polynomialProjectiveCoefficientMap_preimage_coordinate (algebraMap A L) k,
    ← Scheme.Hom.comp_preimage, fibreProjectiveMap_coefficientMap, Scheme.Hom.comp_preimage]

/-- **The fibre map pulls the homogeneous equations back to the pullbacks of those of `X`.** -/
theorem fibreProjectiveMap_homogeneousEquation (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) A)
    (hf : f.IsHomogeneous d) :
    projectivePullbackHomogeneousEquation (fibreProjectiveMap (L := L) ι) k d
        (MvPolynomial.map (algebraMap A L) f) (hf.map _) =
      (pullback.fst (ι ≫ polynomialProjectiveToBase n A)
        (Spec.map (CommRingCat.ofHom (algebraMap A L)))).appLE _ _
        (fibreProjectiveMap_preimage_coordinate ι k).le
        (projectivePullbackHomogeneousEquation ι k d f hf) := by
  rw [projectivePullbackHomogeneousEquation, projectivePullbackHomogeneousEquation,
    ← coefficientMap_appLE_homogeneousEquation (algebraMap A L) k d f hf]
  change (fibreProjectiveMap ι).app _ _ =
    (pullback.fst (ι ≫ polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A L)))).appLE
        (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) A) (MvPolynomial.X k)) _
        (fibreProjectiveMap_preimage_coordinate ι k).le
        (ι.app _ (projectiveHomogeneousEquation A k d f hf))
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (fibreProjectiveMap_coefficientMap ι)]
  rfl

end Fibre

end MixedFujita
