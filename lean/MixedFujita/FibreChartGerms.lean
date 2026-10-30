/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartwiseAmpleRelation
public import MixedFujita.FibreCanonicalEquation

/-!
Germs of pulled-back functions on the fibre charts (step 10, R4-3).

For `g : Y → X` with `Y` integral, `pullbackGerm g V : Γ(X, V) → K(Y)` is the germ of the pullback
of a function, a ring map compatible with restriction (`pullbackGerm_restrict`) and with pulling
back to smaller opens (`germToFunctionField_appLE_eq_pullbackGerm`). On the fibre charts of
check 522 the coordinate units are the germs of the coordinates
(`etaleChartCoordinateRationalUnit_fibreEtaleChart`), the coordinate monomials of check 490 are
the germs of the monomials in the coordinates (`logTwistMonomial_fibreEtaleChart`), and the
canonical equations are the germs of the Jacobians over the base (check 528).

Hence a relation among functions on opens `W_i ⊆ X` gives the relation of check 539 among the
local equations on the fibre (`fibre_chartRelation_of_relation`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Germ

variable {X Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)

/-- The germ of the pullback of a function, in the function field of `Y`. -/
noncomputable def pullbackGerm (V : X.Opens) [Nonempty (g ⁻¹ᵁ V)] : Γ(X, V) →+* Y.functionField :=
  (Y.germToFunctionField (g ⁻¹ᵁ V)).hom.comp (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom

theorem pullbackGerm_apply (V : X.Opens) [Nonempty (g ⁻¹ᵁ V)] (a : Γ(X, V)) :
    pullbackGerm g V a = Y.germToFunctionField (g ⁻¹ᵁ V) (g.appLE V (g ⁻¹ᵁ V) le_rfl a) :=
  rfl

/-- The germ of a pullback to a smaller open. -/
theorem germToFunctionField_appLE_eq_pullbackGerm {V : X.Opens} {W : Y.Opens}
    [Nonempty (g ⁻¹ᵁ V)] [Nonempty W] (h : W ≤ g ⁻¹ᵁ V) (a : Γ(X, V)) :
    Y.germToFunctionField W (g.appLE V W h a) = pullbackGerm g V a := by
  rw [pullbackGerm_apply, ← appLE_restrict_apply (g := g) le_rfl h, germToFunctionField_restrict]

/-- **The germ of a pullback is compatible with restriction.** -/
theorem pullbackGerm_restrict {V W : X.Opens} (h : W ≤ V) [Nonempty (g ⁻¹ᵁ V)]
    [Nonempty (g ⁻¹ᵁ W)] (a : Γ(X, V)) :
    pullbackGerm g W (X.presheaf.map (homOfLE h).op a) = pullbackGerm g V a := by
  rw [pullbackGerm_apply, appLE_of_restrict_apply, germToFunctionField_appLE_eq_pullbackGerm]

end Germ

section Fibre

attribute [local instance] structureSectionsAlgebra

variable {A κ : Type u} [CommRing A] [Field κ] [Algebra A κ] {X Y : Scheme.{u}} [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) [IsAffineHom g] {n : ℕ}

/-- **The coordinate units of a fibre chart are the germs of the coordinates.** -/
theorem etaleChartCoordinateRationalUnit_fibreEtaleChart {V : X.Opens} (hV : IsAffineOpen V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) (j : Fin n) :
    (etaleChartCoordinateRationalUnit (fibreEtaleChart H hV y hy hne) j : Y.functionField) =
      pullbackGerm g V (y (MvPolynomial.X j)) := by
  rw [etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val, fibreEtaleChart_coords_X]
  rfl

/-- **The coordinate monomials of a fibre chart are the germs of the monomials.** -/
theorem logTwistMonomial_fibreEtaleChart {V : X.Opens} (hV : IsAffineOpen V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) (S : Finset (Fin n)) (r : Fin n → ℕ) :
    (logTwistMonomial (fibreEtaleChart H hV y hy hne) S r : Y.functionField) =
      pullbackGerm g V (∏ j ∈ S, y (MvPolynomial.X j) ^ r j) := by
  rw [logTwistMonomial, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Units.val_pow_eq_pow_val, map_pow, etaleChartCoordinateRationalUnit_fibreEtaleChart]

/-- **A relation among functions on the base gives the chart relation of check 539 on the
fibre.** -/
theorem fibre_chartRelation_of_relation {N : ℕ} {V : Fin (N + 1) → X.Opens}
    (hV : ∀ i, IsAffineOpen (V i)) (y : ∀ i, MvPolynomial (Fin n) A →ₐ[A] Γ(X, V i))
    (hy : ∀ i, (y i).toRingHom.FormallyEtale) (hne : ∀ i, Nonempty (g ⁻¹ᵁ V i))
    {W : Fin (N + 1) → X.Opens} (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V i)
    (hWV₀ : ∀ i, W i ≤ V 0) [hneW : ∀ i, Nonempty (g ⁻¹ᵁ W i)]
    (u : ∀ i, Γ(X, V i ⊓ V 0)) {R : Fin (N + 1) → X.Opens} (hVR : ∀ i, V i ≤ R i)
    (rr : ∀ i, Γ(X, R i)) (w : ∀ i, Γ(X, V i)ˣ) (S : Fin (N + 1) → Finset (Fin n))
    (ex : Fin (N + 1) → Fin n → ℕ) (m m' : ℕ)
    (hrel : ∀ i,
      (X.presheaf.map (homOfLE (le_inf (hWV i) (hWV₀ i))).op (u i)) ^ (m * m') *
          (X.presheaf.map (homOfLE (hWV₀ i)).op
            (∏ j ∈ S 0, y 0 (MvPolynomial.X j) ^ ex 0 j)) ^ m' *
          X.presheaf.map (homOfLE (hWV₀ i)).op (w 0 : Γ(X, V 0)) =
        X.presheaf.map (homOfLE (hWV i)).op (w i : Γ(X, V i)) *
          X.presheaf.map (homOfLE ((hWV i).trans (hVR i))).op (rr i) *
          ringJacobianOn (hV i) (hV 0) (hW i) (hWV i) (hWV₀ i) (y i) (y 0) (hy i) (hy 0) ^
            (m * m') *
          (X.presheaf.map (homOfLE (hWV i)).op
            (∏ j ∈ S i, y i (MvPolynomial.X j) ^ ex i j)) ^ m') (i : Fin (N + 1)) :
    haveI : Nonempty (g ⁻¹ᵁ (V i ⊓ V 0)) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ W i)).1,
      (Opens.map g.base).monotone (le_inf (hWV i) (hWV₀ i)) (Classical.arbitrary (g ⁻¹ᵁ W i)).2⟩⟩
    haveI : Nonempty (g ⁻¹ᵁ R i) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ V i)).1,
      (Opens.map g.base).monotone (hVR i) (Classical.arbitrary (g ⁻¹ᵁ V i)).2⟩⟩
    pullbackGerm g (V i ⊓ V 0) (u i) ^ (m * m') *
        (logTwistMonomial (fibreEtaleChart H (hV 0) (y 0) (hy 0) (hne 0)) (S 0) (ex 0) :
          Y.functionField) ^ m' *
        pullbackGerm g (V 0) (w 0 : Γ(X, V 0)) =
      pullbackGerm g (V i) (w i : Γ(X, V i)) * pullbackGerm g (R i) (rr i) *
        (etaleChartCanonicalEquation (fibreEtaleChart H (hV 0) (y 0) (hy 0) (hne 0))
          (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)) : Y.functionField) ^ (m * m') *
        (logTwistMonomial (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)) (S i) (ex i) :
          Y.functionField) ^ m' := by
  have : Nonempty (g ⁻¹ᵁ (V i ⊓ V 0)) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ W i)).1,
    (Opens.map g.base).monotone (le_inf (hWV i) (hWV₀ i)) (Classical.arbitrary (g ⁻¹ᵁ W i)).2⟩⟩
  have : Nonempty (g ⁻¹ᵁ R i) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ V i)).1,
    (Opens.map g.base).monotone (hVR i) (Classical.arbitrary (g ⁻¹ᵁ V i)).2⟩⟩
  have : Nonempty (g ⁻¹ᵁ V 0) := hne 0
  have : Nonempty (g ⁻¹ᵁ V i) := hne i
  have h := congrArg (pullbackGerm g (W i)) (hrel i)
  simp only [map_mul, map_pow, pullbackGerm_restrict] at h
  rw [logTwistMonomial_fibreEtaleChart, logTwistMonomial_fibreEtaleChart,
    fibreEtaleChart_canonicalEquation H (hV i) (hV 0) (hW i) (hWV i) (hWV₀ i) (y i) (y 0) (hy i)
      (hy 0) (hne i) (hne 0)]
  rw [germToFunctionField_appLE_eq_pullbackGerm]
  exact h

end Fibre

end MixedFujita
