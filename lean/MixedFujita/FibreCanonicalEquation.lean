/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreEtaleCharts
public import MixedFujita.RingEtaleJacobian
public import MixedFujita.TwistedDeRhamCech
public import MixedFujita.RegularEquationCartier
public import MixedFujita.CartierCechBaseChange

/-!
The canonical equations of the fibre charts are images of one Jacobian over the base (step 10,
R4-3).

Let `X` be a scheme over a ring `A` and `Y = X ×_A L` its fibre over a field `L`. For two affine
opens `V, V₀` of `X` with étale coordinates `y, y₀` over `A` and an affine open `W ≤ V ⊓ V₀`, the
restricted coordinates are étale on `W` (`restrictCoordinates_formallyEtale`), with a Jacobian
`J_W = det(dy, dy₀)` over `A` (`ringJacobianOn`, check 527). The canonical equation of the fibre
chart over `V` relative to that over `V₀` (check 522) is the germ of the pullback of `J_W`
(`fibreEtaleChart_canonicalEquation`): both bases of differentials of the function field come from
the coordinates `1 ⊗ y_j`, `1 ⊗ y₀_j` of `L ⊗_A Γ(X, W) ≅ Γ(Y, g⁻¹W)` (check 497) through a
formally étale map, so their determinant is the image of the determinant over `L ⊗_A Γ(X, W)`,
which is the image of `J_W` (check 527).

For the closure `T_A` this identifies the transition functions of the canonical divisors of the
fibres `T_K` and `T_κ` with the images of the Jacobians over `A`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] structureSectionsAlgebra Algebra.TensorProduct.rightAlgebra

section Restrict

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] {n : ℕ}

/-- Coordinates restricted to a smaller open, over the base. -/
noncomputable def restrictCoordinates {V W : X.Opens} (h : W ≤ V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) : MvPolynomial (Fin n) A →ₐ[A] Γ(X, W) :=
  (structureRestrictAlgHom A X h).comp y

/-- Étale coordinates restrict to étale coordinates on a smaller affine open. -/
theorem restrictCoordinates_formallyEtale {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (hy : y.toRingHom.FormallyEtale) : (restrictCoordinates h y).toRingHom.FormallyEtale :=
  RingHom.FormallyEtale.comp hy (restrict_formallyEtale_of_isAffineOpen hV hW h)

/-- **The Jacobian over the base** of two systems of étale coordinates on a common affine open. -/
noncomputable def ringJacobianOn {V V₀ W : X.Opens} (hV : IsAffineOpen V) (hV₀ : IsAffineOpen V₀)
    (hW : IsAffineOpen W) (hWV : W ≤ V) (hWV₀ : W ≤ V₀) (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (y₀ : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V₀)) (hy : y.toRingHom.FormallyEtale)
    (hy₀ : y₀.toRingHom.FormallyEtale) : Γ(X, W) :=
  (ringEtaleCoordinateBasis (restrictCoordinates hWV y)
      (restrictCoordinates_formallyEtale hV hW hWV y hy)).det
    (ringEtaleCoordinateBasis (restrictCoordinates hWV₀ y₀)
      (restrictCoordinates_formallyEtale hV₀ hW hWV₀ y₀ hy₀))

end Restrict

section Canonical

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of L))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A L))))
  [IsAffineHom g] [IsIntegral Y] {n : ℕ}

/-- The germ of the base change of `L ⊗_A Γ(X, W) ≅ Γ(Y, g⁻¹W)`, as an `L`-algebra map to the
function field. -/
noncomputable def fibreGermAlgHom {W : X.Opens} (hW : IsAffineOpen W) [Nonempty (g ⁻¹ᵁ W)] :
    L ⊗[A] Γ(X, W) →ₐ[L] Y.functionField :=
  (sectionGermAlgHom (K := L) (g ⁻¹ᵁ W)).comp (sectionsBaseChangeEquiv H hW).toAlgHom

theorem fibreGermAlgHom_formallyEtale {W : X.Opens} (hW : IsAffineOpen W) [Nonempty (g ⁻¹ᵁ W)] :
    (fibreGermAlgHom H hW).toRingHom.FormallyEtale :=
  RingHom.FormallyEtale.comp (formallyEtale_of_ringEquiv (sectionsBaseChangeEquiv H hW).toRingEquiv)
    (sectionGermAlgHom_formallyEtale (g ⁻¹ᵁ W) (hW.preimage g))

/-- The coordinates of a fibre chart in the function field come from a smaller affine open. -/
theorem etaleChartFunctionFieldCoords_fibreEtaleChart {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) [Nonempty (g ⁻¹ᵁ W)]
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) :
    etaleChartFunctionFieldCoords (fibreEtaleChart H hV y hy hne) =
      (fibreGermAlgHom H hW).comp (tensorCoordinatesOf L (restrictCoordinates h y)) := by
  apply MvPolynomial.algHom_ext
  intro j
  change sectionGermAlgHom (K := L) (g ⁻¹ᵁ V) ((fibreEtaleChart H hV y hy hne).coords
      (MvPolynomial.X j)) =
    sectionGermAlgHom (K := L) (g ⁻¹ᵁ W)
      (sectionsBaseChangeEquiv H hW (tensorCoordinatesOf L (restrictCoordinates h y)
        (MvPolynomial.X j)))
  rw [fibreEtaleChart_coords_X, tensorCoordinatesOf_X, sectionsBaseChangeEquiv_tmul, map_one,
    one_mul]
  change Y.germToFunctionField (g ⁻¹ᵁ V) (g.appLE V (g ⁻¹ᵁ V) le_rfl (y (MvPolynomial.X j))) =
    Y.germToFunctionField (g ⁻¹ᵁ W) (g.appLE W (g ⁻¹ᵁ W) le_rfl
      (X.presheaf.map (homOfLE h).op (y (MvPolynomial.X j))))
  rw [appLE_of_restrict_apply, ← appLE_restrict_apply (h := (Opens.map g.base).monotone h),
    germToFunctionField_restrict]

/-- **The canonical equation of a fibre chart relative to another is the germ of the pullback of
the Jacobian over the base.** -/
theorem fibreEtaleChart_canonicalEquation {V V₀ W : X.Opens} (hV : IsAffineOpen V)
    (hV₀ : IsAffineOpen V₀) (hW : IsAffineOpen W) (hWV : W ≤ V) (hWV₀ : W ≤ V₀)
    [Nonempty (g ⁻¹ᵁ W)] (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (y₀ : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V₀)) (hy : y.toRingHom.FormallyEtale)
    (hy₀ : y₀.toRingHom.FormallyEtale) (hne : Nonempty (g ⁻¹ᵁ V))
    (hne₀ : Nonempty (g ⁻¹ᵁ V₀)) :
    (etaleChartCanonicalEquation (fibreEtaleChart H hV₀ y₀ hy₀ hne₀)
        (fibreEtaleChart H hV y hy hne) : Y.functionField) =
      Y.germToFunctionField (g ⁻¹ᵁ W)
        (g.appLE W (g ⁻¹ᵁ W) le_rfl (ringJacobianOn hV hV₀ hW hWV hWV₀ y y₀ hy hy₀)) := by
  have hφ := fibreGermAlgHom_formallyEtale H hW
  have hb : ∀ {V' : X.Opens} (hV' : IsAffineOpen V') (h : W ≤ V')
      (z : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V')) (hz : z.toRingHom.FormallyEtale)
      (hne' : Nonempty (g ⁻¹ᵁ V')),
      etaleChartBasis (fibreEtaleChart H hV' z hz hne') =
        etaleCoordinateBasis ((fibreGermAlgHom H hW).comp
          (tensorCoordinatesOf L (restrictCoordinates h z)))
          (formallyEtale_comp _ hφ _ (tensorCoordinatesOf_formallyEtale L _
            (restrictCoordinates_formallyEtale hV' hW h z hz))) := by
    intro V' hV' h z hz hne'
    apply Module.Basis.eq_of_apply_eq
    intro j
    rw [etaleChartBasis, etaleCoordinateBasis_apply, etaleCoordinateBasis_apply,
      etaleChartFunctionFieldCoords_fibreEtaleChart H hV' hW h z hz hne']
  rw [etaleChartCanonicalEquation_val, hb hV hWV y hy hne, hb hV₀ hWV₀ y₀ hy₀ hne₀,
    etaleCoordinateBasis_det_comp _ hφ _ _
      (tensorCoordinatesOf_formallyEtale L _ (restrictCoordinates_formallyEtale hV hW hWV y hy))
      (tensorCoordinatesOf_formallyEtale L _ (restrictCoordinates_formallyEtale hV₀ hW hWV₀ y₀ hy₀)),
    etaleCoordinateBasis_tensorCoordinatesOf_det]
  change sectionGermAlgHom (K := L) (g ⁻¹ᵁ W)
      (sectionsBaseChangeEquiv H hW ((1 : L) ⊗ₜ[A] ringJacobianOn hV hV₀ hW hWV hWV₀ y y₀ hy hy₀)) = _
  rw [sectionsBaseChangeEquiv_tmul, map_one, one_mul]
  rfl

end Canonical

end MixedFujita
