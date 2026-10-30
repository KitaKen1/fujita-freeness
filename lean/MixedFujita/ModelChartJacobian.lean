/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartMonomial

/-!
The chart Jacobian of a model of Spec A on a chart of the model (step 9, strict transform charts).

For a dominant morphism ρ : T → Spec A over K, a chart c of T and étale coordinates x of A, let
μ : A → Γ(T, c.U) be the map of sections (`modelChartAlgHom`). The chart Jacobian of ρ in the
global chart of Spec A given by x and the chart c is the image in the function field of the
relative Jacobian det J(μ) of the ring map in the coordinates x and those of c
(`chartRelativeJacobianDet_appLE`): it only depends on the images of the coordinates, and the germ
map of c.U to the function field is formally étale. This identifies det J(μ) of the strict
transform charts (check-334) with a local equation of the relative canonical divisor K_{T/X} on
the chart, to which the local products of check-337 apply.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Jacobian

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  functionFieldBaseAlgebra specAlgebraOver

variable {A : Type u} [CommRing A] [IsDomain A] [Algebra K A] {T : Scheme.{u}} [IsIntegral T]
  [T.Over (Spec (CommRingCat.of K))]

/-- The map of sections A → Γ(T, U) of a morphism to Spec A over K. -/
noncomputable def modelChartAlgHom (ρ : T ⟶ Spec (CommRingCat.of A))
    [ρ.IsOver (Spec (CommRingCat.of K))] (U : T.Opens) : A →ₐ[K] Γ(T, U) :=
  (appLEAlgHom (K := K) ρ ⊤ U le_top).comp (specTopAlgEquiv (K := K) A).toAlgHom

omit [IsDomain A] [IsIntegral T] in
theorem modelChartAlgHom_apply (ρ : T ⟶ Spec (CommRingCat.of A))
    [ρ.IsOver (Spec (CommRingCat.of K))] (U : T.Opens) (a : A) :
    modelChartAlgHom (K := K) ρ U a =
      ρ.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) :=
  rfl

/-- The chart Jacobian of a model of Spec A on a chart c is the image of the relative Jacobian of
the map of sections A → Γ(T, c.U). -/
theorem chartRelativeJacobianDet_appLE (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] (x : MvPolynomial (Fin n) K →ₐ[K] A)
    (hx : x.toRingHom.FormallyEtale) (c : EtaleChart K T n) :
    chartRelativeJacobianDet ρ (specAlgebraEtaleChart x hx) c =
      T.germToFunctionField c.U
        (etaleRelativeJacobian (modelChartAlgHom (K := K) ρ c.U) x c.coords c.formallyEtale).det := by
  have : Nonempty c.U := c.nonempty
  let ι : Γ(T, c.U) →ₐ[K] T.functionField := sectionGermAlgHom (X := T) c.U
  have hc : etaleChartFunctionFieldCoords c = ι.comp c.coords := rfl
  have hιy : (ι.comp c.coords).toRingHom.FormallyEtale :=
    hc ▸ etaleChartFunctionFieldCoords_formallyEtale c
  have hcoords : ∀ p, dominantFunctionFieldAlgHom (K := K) ρ
      (etaleChartFunctionFieldCoords (specAlgebraEtaleChart x hx) p) =
        ι (modelChartAlgHom (K := K) ρ c.U (x p)) := by
    intro p
    change (dominantFunctionFieldMap ρ).hom
        ((Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (x p))) = _
    rw [dominantFunctionFieldMap_germ ρ ⊤ c.U le_top]
    rfl
  have hmat : etaleRelativeJacobian (dominantFunctionFieldAlgHom (K := K) ρ)
      (etaleChartFunctionFieldCoords (specAlgebraEtaleChart x hx))
      (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c) =
      etaleRelativeJacobian (ι.comp (modelChartAlgHom (K := K) ρ c.U)) x (ι.comp c.coords)
        hιy := by
    ext i j
    change etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) j
        (dominantFunctionFieldAlgHom (K := K) ρ
          (etaleChartFunctionFieldCoords (specAlgebraEtaleChart x hx) (MvPolynomial.X i))) =
      etaleCoordinateDerivation (ι.comp c.coords) hιy j
        (ι (modelChartAlgHom (K := K) ρ c.U (x (MvPolynomial.X i))))
    rw [hcoords, etaleCoordinateDerivation_congr hc]
  unfold chartRelativeJacobianDet
  rw [hmat, etaleRelativeJacobian_det_comp_coords (modelChartAlgHom (K := K) ρ c.U) ι x c.coords
    c.formallyEtale hιy]
  rfl

end Jacobian

end MixedFujita
