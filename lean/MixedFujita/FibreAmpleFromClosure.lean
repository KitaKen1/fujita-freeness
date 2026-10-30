/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantChartRelation
public import MixedFujita.FibreProjectiveEmbedding

/-!
Ampleness on the fibre from a relation on the closure (step 10, R4-3).

Let `X → ℙ_A` be a closed immersion and `Y = X ×_A κ` a fibre over a field, smooth and integral,
embedded in `ℙ_κ` compatibly with the charts and the chart equations (check 537). Let `V_i` be
affine opens of `X` inside the charts of `X_{k(i)}` with étale coordinates `ψ_i`, whose fibre charts
are simple normal crossing charts covering `Y`. If on `W_i ⊆ V_i ∩ V_0` the functions
`u_i` (transition functions of `Q`), the coordinate monomials `M_i`, units `w_i`, the chart equations
`r_i = X_{k(0)}/X_{k(i)}` and the Jacobians `J_i` satisfy
`u_i^{m m'} M_0^{m'} w_0 = w_i r_i J_i^{m m'} M_i^{m'}`, and `Q_Y` has the local equations given by the
germs of the `u_i`, then `m (Q_Y − K_Y) − Σ a_k E_k` is ample on `Y`
(`fibre_cartierIsAmpleProj_of_closureRelation`: check 540 gives the relation of check 539 among the
local equations, and the chart equations of `Y` are the pullbacks of those of `X`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable structureSectionsAlgebra

universe u

variable {A κ : Type u} [CommRing A] [Field κ] [Algebra A κ] {X Y : Scheme.{u}} [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) [IsAffineHom g]
  [IsLocallyNoetherian Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of κ))]
  [∀ z : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (z : Y))]
  (hnorm : ∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z))
  {d r : ℕ} (ξ : Fin r → Y) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor Y)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint Y),
    cartierCoefficient (E k) (z : Y) = if (z : Y) = ξ k then 1 else 0)

include hnorm hinj hξ hEc in
/-- **The adjoint divisor on the fibre is ample, from a relation of functions on the closure.** -/
theorem fibre_cartierIsAmpleProj_of_closureRelation {P : ℕ}
    (ι : X ⟶ polynomialProjectiveScheme P A) (eY : Y ⟶ polynomialProjectiveScheme P κ)
    [IsClosedImmersion eY]
    (heY : eY ≫ polynomialProjectiveToBase P κ = Y ↘ Spec (CommRingCat.of κ))
    (heYk : ∀ k, projectivePullbackCoordinateOpen eY k = g ⁻¹ᵁ projectivePullbackCoordinateOpen ι k)
    (k₀ : Fin P)
    (heYeq : ∀ k, projectivePullbackHomogeneousEquation eY k 1 (MvPolynomial.X k₀)
        (MvPolynomial.isHomogeneous_X κ k₀) =
      g.appLE _ _ (heYk k).le (projectivePullbackHomogeneousEquation ι k 1 (MvPolynomial.X k₀)
        (MvPolynomial.isHomogeneous_X A k₀)))
    {N : ℕ} {V : Fin (N + 1) → X.Opens} (hV : ∀ i, IsAffineOpen (V i))
    (kk : Fin (N + 1) → Fin P) (hk₀ : kk 0 = k₀)
    (hVk : ∀ i, V i ≤ projectivePullbackCoordinateOpen ι (kk i))
    (y : ∀ i, MvPolynomial (Fin d) A →ₐ[A] Γ(X, V i)) (hy : ∀ i, (y i).toRingHom.FormallyEtale)
    (hne : ∀ i, Nonempty (g ⁻¹ᵁ V i)) (σ : Fin (N + 1) → Fin r → Option (Fin d))
    (hc : ∀ i, IsSNCChart (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)) ξ (σ i))
    (hcov : ⨆ i, (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)).U = ⊤)
    (hcover : iSup (fun c : EtaleChart κ Y d => c.U) = ⊤)
    {W : Fin (N + 1) → X.Opens} (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V i)
    (hWV₀ : ∀ i, W i ≤ V 0) [∀ i, Nonempty (g ⁻¹ᵁ W i)]
    (u : ∀ i, Γ(X, V i ⊓ V 0)) (w : ∀ i, Γ(X, V i)ˣ) (Q : CartierDivisor Y)
    (gQ : Fin (N + 1) → Y.functionFieldˣ)
    (hgQ : ∀ i, ∀ z ∈ (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)).U, Q.IsLocalEquationAt z (gQ i))
    (hgQu : ∀ i, haveI : Nonempty (g ⁻¹ᵁ (V i ⊓ V 0)) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ W i)).1,
        (Opens.map g.base).monotone (le_inf (hWV i) (hWV₀ i)) (Classical.arbitrary (g ⁻¹ᵁ W i)).2⟩⟩
      (gQ i : Y.functionField) = pullbackGerm g (V i ⊓ V 0) (u i))
    (m m' : ℕ) (hm' : 1 ≤ m') (a : Fin r → ℕ)
    (hrel : ∀ i,
      (X.presheaf.map (homOfLE (le_inf (hWV i) (hWV₀ i))).op (u i)) ^ (m * m') *
          (X.presheaf.map (homOfLE (hWV₀ i)).op
            (∏ j ∈ logSetOf (σ 0), y 0 (MvPolynomial.X j) ^ logTwistExponent (σ 0) a j)) ^ m' *
          X.presheaf.map (homOfLE (hWV₀ i)).op (w 0 : Γ(X, V 0)) =
        X.presheaf.map (homOfLE (hWV i)).op (w i : Γ(X, V i)) *
          X.presheaf.map (homOfLE ((hWV i).trans (hVk i))).op
            (projectivePullbackHomogeneousEquation ι (kk i) 1 (MvPolynomial.X k₀)
              (MvPolynomial.isHomogeneous_X A k₀)) *
          ringJacobianOn (hV i) (hV 0) (hW i) (hWV i) (hWV₀ i) (y i) (y 0) (hy i) (hy 0) ^
            (m * m') *
          (X.presheaf.map (homOfLE (hWV i)).op
            (∏ j ∈ logSetOf (σ i), y i (MvPolynomial.X j) ^ logTwistExponent (σ i) a j)) ^ m') :
    CartierIsAmpleProj κ (m • (Q - canonicalDivisor d
      (fibreEtaleChart H (hV 0) (y 0) (hy 0) (hne 0)) hcover) - ∑ k, a k • E k) := by
  classical
  subst hk₀
  -- the fibre charts lie in the charts of the embedding
  have hUk : ∀ i, (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)).U ≤
      projectivePullbackCoordinateOpen eY (kk i) := by
    intro i
    rw [heYk]
    exact (Opens.map g.base).monotone (hVk i)
  -- the fibre units
  let w' : ∀ i, Γ(Y, (fibreEtaleChart H (hV i) (y i) (hy i) (hne i)).U)ˣ := fun i =>
    Units.map (g.appLE (V i) (g ⁻¹ᵁ V i) le_rfl).hom.toMonoidHom (w i)
  refine cartierIsAmpleProj_adjoint_of_chartRelation hnorm ξ hinj hξ E hEc eY heY _ σ hc hcov
    hcover kk hUk Q gQ hgQ m m' hm' a w' (fun i => ?_)
  -- the relation of check 540
  have h := fibre_chartRelation_of_relation H hV y hy hne hW hWV hWV₀ u hVk
    (fun i => projectivePullbackHomogeneousEquation ι (kk i) 1 (MvPolynomial.X (kk 0))
      (MvPolynomial.isHomogeneous_X A (kk 0))) w (fun i => logSetOf (σ i))
    (fun i => logTwistExponent (σ i) a) m m' hrel i
  have : Nonempty (g ⁻¹ᵁ V i) := hne i
  have : Nonempty (g ⁻¹ᵁ V 0) := hne 0
  have : Nonempty (projectivePullbackCoordinateOpen eY (kk i)) :=
    ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ V i)).1, hUk i (Classical.arbitrary (g ⁻¹ᵁ V i)).2⟩⟩
  have : Nonempty (g ⁻¹ᵁ projectivePullbackCoordinateOpen ι (kk i)) :=
    ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ V i)).1,
      (Opens.map g.base).monotone (hVk i) (Classical.arbitrary (g ⁻¹ᵁ V i)).2⟩⟩
  have hwi : ∀ j, Y.germToFunctionField (fibreEtaleChart H (hV j) (y j) (hy j) (hne j)).U
      (w' j : Γ(Y, _)) = pullbackGerm g (V j) (w j : Γ(X, V j)) := fun j => rfl
  have hr : Y.germToFunctionField (projectivePullbackCoordinateOpen eY (kk i))
      (projectivePullbackHomogeneousEquation eY (kk i) 1 (MvPolynomial.X (kk 0))
        (MvPolynomial.isHomogeneous_X κ (kk 0))) =
      pullbackGerm g (projectivePullbackCoordinateOpen ι (kk i))
        (projectivePullbackHomogeneousEquation ι (kk i) 1 (MvPolynomial.X (kk 0))
          (MvPolynomial.isHomogeneous_X A (kk 0))) := by
    rw [heYeq (kk i), germToFunctionField_appLE_eq_pullbackGerm]
  rw [hgQu i, hwi, hwi, hr]
  exact h

end MixedFujita
