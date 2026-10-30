/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing
public import MixedFujita.ProjectiveCartierSheafPullback
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.ProjectiveHyperplaneSections
public import MixedFujita.ModuleFramesSGAModuleIso

/-! Identify the actual polynomial-projective coordinate equations with SGA fraction sections. Genuine Cartier equation frames have exactly the SGA transition units, giving an isomorphism of the actual ambient hyperplane Cartier sheaf with the SGA degree-one module. All ambient coordinate charts are nonempty over a domain; no statement about dominance of an embedded source is used. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem polynomialProjective_fracSection_eq_equation
    {R : Type u} [CommRing R] {n : ℕ} (i : Fin n)
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1) :
    Proj.fracSection (MvPolynomial.homogeneousSubmodule (Fin n) R)
      hg (MvPolynomial.isHomogeneous_X R i)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X i)) le_rfl =
      projectiveHomogeneousEquation R i 1 g hg := by
  apply Proj.section_ext (MvPolynomial.homogeneousSubmodule (Fin n) R)
  intro x
  rw [Proj.val_fracSection_apply]
  simp only [projectiveHomogeneousEquation]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [HomogeneousLocalization.Away.val_mk]
  simp only [Localization.mk_eq_mk']
  rw [IsLocalization.map_mk']
  simp only [pow_one, RingHom.id_apply]

theorem polynomialProjective_equations_sga_compat
    {R : Type u} [CommRing R] {n : ℕ}
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
    (i j : (projectiveSpace.twistingBundle (Fin n) R).ι) :
    (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_left).op
        (projectiveHomogeneousEquation R i.down 1 g hg) =
      ((projectiveSpace.twistingBundle (Fin n) R).g i j :
        Γ(polynomialProjectiveScheme n R,
          (projectiveSpace.twistingBundle (Fin n) R).U i ⊓
            (projectiveSpace.twistingBundle (Fin n) R).U j)) *
        (polynomialProjectiveScheme n R).presheaf.map (homOfLE inf_le_right).op
          (projectiveHomogeneousEquation R j.down 1 g hg) := by
  rw [← polynomialProjective_fracSection_eq_equation i.down g hg,
    ← polynomialProjective_fracSection_eq_equation j.down g hg]
  simp only [Proj.map_fracSection]
  simpa only [projectiveSpace.twistingBundle, Proj.twistingSheaf, Proj.twistingUnit,
    pow_one] using Proj.twistingSheaf.homogeneousSection_compat
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) R)
    (fun k : ULift.{u} (Fin n) => MvPolynomial.X k.down)
    (fun k => MvPolynomial.isHomogeneous_X R k.down) hg i j

theorem moduleFramesSGALineBundle_eq_of_transitions
    {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules)
    (e : ∀ i, M.over (L.U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (L.U i)))
    (hg : ∀ i j, moduleFrameTransitionUnit M L.U e i j
      (L.U i ⊓ L.U j) inf_le_left inf_le_right = L.g i j) :
    moduleFramesSGALineBundle M L.U e L.iSup_eq_top = L := by
  have hg' : (fun i j => moduleFrameTransitionUnit M L.U e i j
      (L.U i ⊓ L.U j) inf_le_left inf_le_right) = L.g := funext fun i => funext (hg i)
  cases L
  simp only [moduleFramesSGALineBundle] at hg' ⊢
  congr

noncomputable def moduleFramesCompatibleSGAIso
    {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules)
    (e : ∀ i, M.over (L.U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (L.U i)))
    (hg : ∀ i j, moduleFrameTransitionUnit M L.U e i j
      (L.U i ⊓ L.U j) inf_le_left inf_le_right = L.g i j) :
    M ≅ L.toModules 1 :=
  moduleFramesSGAModuleIso M L.U e L.iSup_eq_top ≪≫
    eqToIso (congrArg (fun A : X.LineBundle => A.toModules 1)
      (moduleFramesSGALineBundle_eq_of_transitions L M e hg))

theorem cartierEquationFrameTransitionUnit_eq
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    {ι : Type u} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (a : ι → X.functionFieldˣ)
    (ha : ∀ i, rationalUnitClass X (U i) (Additive.ofMul (a i)) = D |_ U i)
    (i j : ι) (w : Γ(X, U i ⊓ U j)ˣ)
    (hw : letI := integral_opens_inter_nonempty X (U i) (U j)
      a i = Units.map (X.germToFunctionField (U i ⊓ U j)).hom w * a j) :
    moduleFrameTransitionUnit D.sheaf U
      (fun k => cartierOpenFrameIso D (U k) (a k) (ha k)) i j
      (U i ⊓ U j) inf_le_left inf_le_right = w := by
  letI := integral_opens_inter_nonempty X (U i) (U j)
  let frames := fun k => cartierOpenFrameIso D (U k) (a k) (ha k)
  let t := (moduleOverFrameCoefficient D.sheaf (U j) (frames j)
    (U i ⊓ U j) inf_le_right).symm 1
  have ht : moduleOverFrameCoefficient D.sheaf (U j) (frames j)
      (U i ⊓ U j) inf_le_right t = 1 := LinearEquiv.apply_symm_apply _ _
  have htr := moduleFrameTransitionUnit_mul D.sheaf U frames i j
    (U i ⊓ U j) inf_le_left inf_le_right t
  rw [ht, mul_one] at htr
  apply Units.ext
  change (moduleFrameTransitionUnit D.sheaf U frames i j
    (U i ⊓ U j) inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) = _
  rw [htr]
  apply X.germToFunctionField_injective (U i ⊓ U j)
  change X.germToFunctionField (U i ⊓ U j)
    (cartierOpenCoefficient D (U i) (a i) (ha i) _ inf_le_left t) = _
  rw [cartierOpenCoefficient_image]
  have hc := cartierOpenCoefficient_image D (U j) (a j) (ha j)
    (U i ⊓ U j) inf_le_right t
  change X.germToFunctionField (U i ⊓ U j)
    (moduleOverFrameCoefficient D.sheaf (U j) (frames j) _ inf_le_right t) = _ at hc
  rw [ht, map_one] at hc
  have hval : (a i : X.functionField) =
      X.germToFunctionField (U i ⊓ U j) w * (a j : X.functionField) :=
    congrArg Units.val hw
  rw [hval, mul_assoc, ← hc, mul_one]

noncomputable def polynomialHyperplaneSGAModuleIso
    {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}
    [IsIntegral (polynomialProjectiveScheme n R)]
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
    (hP : g ∉ (genericPoint (polynomialProjectiveScheme n R)).asHomogeneousIdeal) :
    (projectiveHyperplaneCartier (𝟙 (polynomialProjectiveScheme n R)) g hg hP).sheaf ≅
      (projectiveSpace.twistingBundle (Fin n) R).toModules 1 := by
  let P := polynomialProjectiveScheme n R
  let L := projectiveSpace.twistingBundle (Fin n) R
  let D := projectiveHyperplaneCartier (𝟙 P) g hg hP
  letI (k : Fin n) : Nonempty
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) :=
    polynomialProjective_coordinate_open_nonempty R k
  letI (k : Fin n) : Nonempty (projectivePullbackCoordinateOpen (𝟙 P) k) := by
    simpa [projectivePullbackCoordinateOpen] using
      (polynomialProjective_coordinate_open_nonempty R k)
  letI (i : L.ι) : Nonempty (L.U i) := polynomialProjective_coordinate_open_nonempty R i.down
  let a (i : L.ι) : P.functionFieldˣ :=
    projectiveHyperplaneUnit (𝟙 P) g hg hP ⟨i.down, inferInstance⟩
  have ha (i : L.ι) : rationalUnitClass P (L.U i) (Additive.ofMul (a i)) = D |_ L.U i :=
    (projectivePullbackHomogeneousCartier_restrict (𝟙 P) 1 g hg one_pos hP
      ⟨i.down, inferInstance⟩).symm
  let frames := fun i => cartierOpenFrameIso D (L.U i) (a i) (ha i)
  refine moduleFramesCompatibleSGAIso L D.sheaf frames ?_
  intro i j
  apply cartierEquationFrameTransitionUnit_eq D L.U a ha i j (L.g i j)
  exact regularEquationRationalUnit_eq_of_overlap P
    (projectiveHomogeneousEquation R i.down 1 g hg)
    (projectivePullbackHomogeneousEquation_ne_zero (𝟙 P) i.down 1 g hg one_pos hP)
    (projectiveHomogeneousEquation R j.down 1 g hg)
    (projectivePullbackHomogeneousEquation_ne_zero (𝟙 P) j.down 1 g hg one_pos hP)
    (L.g i j) (polynomialProjective_equations_sga_compat g hg i j)

end MixedFujita
