/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreAmpleFromClosure

/-!
The chart relation on the closure from that on `T` (step 10, R4-3).

Let `T ⊆ ℙ_K` be a closed subscheme with closure `T_A` over a subring `A ⊆ K` with `T = T_A ×_A K`,
affine opens `V_i ⊆ T_A` inside the charts of `X_{k(i)}` with étale coordinates `ψ_i`, and charts
`c_i` of `T` whose coordinates have the germs of the `ψ_i` (check 536). If the chart relation of
check 541 holds on `T` for local equations `g_i` and units `w^K_i`, and the germs of functions `u_i`
and units `w_i` on `T_A` are the `g_i` and `w^K_i`, then the relation of check 545 holds among
functions on `W_i ⊆ V_i ∩ V_0` (`closure_relation_of_chartRelation`): the germs of the coordinate
monomials, chart equations and Jacobians on `T_A` are those of the charts of `T`
(checks 528, 540, 543), and the map `T → T_A` is dominant (check 544).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable structureSectionsAlgebra

universe u

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  {P : ℕ} (e : T ⟶ polynomialProjectiveScheme P K) [IsClosedImmersion e]

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- The map to the closure is affine. -/
theorem projectiveClosureMap_isAffineHom {A : Type u} [CommRing A] (c : A →+* K) :
    IsAffineHom (projectiveClosureMap c e) := by
  have := polynomialProjectiveCoefficientMap_isAffineHom (n := P) c
  have h : IsAffineHom (projectiveClosureMap c e ≫ projectiveClosureι c e) := by
    rw [projectiveClosureMap_comp_ι]
    infer_instance
  exact IsAffineHom.comp_iff.1 h

/-- **The chart relation on the closure, from the chart relation on `T`.** -/
theorem closure_relation_of_chartRelation (A : Subalgebra ℤ K)
    (HA : letI := projectiveClosureOver e (algebraMap A K)
      IsPullback (projectiveClosureMap (algebraMap A K) e) (T ↘ Spec (CommRingCat.of K))
        (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    {N d r : ℕ} {V : Fin (N + 1) → (projectiveClosure (algebraMap A K) e).Opens}
    (hV : ∀ i, IsAffineOpen (V i)) (kk : Fin (N + 1) → Fin P)
    (hVk : ∀ i, V i ≤ projectivePullbackCoordinateOpen (projectiveClosureι (algebraMap A K) e) (kk i))
    (ψ : ∀ i, letI := projectiveClosureOver e (algebraMap A K)
      MvPolynomial (Fin d) A →ₐ[A] Γ(projectiveClosure (algebraMap A K) e, V i))
    (hψ : ∀ i, letI := projectiveClosureOver e (algebraMap A K)
      (ψ i).toRingHom.FormallyEtale)
    [hne : ∀ i, Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ V i)]
    {W : Fin (N + 1) → (projectiveClosure (algebraMap A K) e).Opens} (hW : ∀ i, IsAffineOpen (W i))
    (hWV : ∀ i, W i ≤ V i) (hWV₀ : ∀ i, W i ≤ V 0)
    [∀ i, Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ W i)]
    (c : Fin (N + 1) → EtaleChart K T d)
    (hψc : ∀ i j, pullbackGerm (projectiveClosureMap (algebraMap A K) e) (V i) (ψ i (MvPolynomial.X j)) =
      T.germToFunctionField (c i).U ((c i).coords (MvPolynomial.X j)))
    (hUk : ∀ i, (c i).U ≤ projectivePullbackCoordinateOpen e (kk i))
    (u : ∀ i, Γ(projectiveClosure (algebraMap A K) e, V i ⊓ V 0)) (gQ : Fin (N + 1) → T.functionFieldˣ)
    (hgQu : ∀ i, haveI : Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (V i ⊓ V 0)) :=
        ⟨⟨(Classical.arbitrary (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ W i)).1,
          (Opens.map (projectiveClosureMap (algebraMap A K) e).base).monotone
            (le_inf (hWV i) (hWV₀ i))
            (Classical.arbitrary (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ W i)).2⟩⟩
      (gQ i : T.functionField) = pullbackGerm (projectiveClosureMap (algebraMap A K) e) (V i ⊓ V 0) (u i))
    (w : ∀ i, Γ(projectiveClosure (algebraMap A K) e, V i)ˣ) (wK : ∀ i, Γ(T, (c i).U)ˣ)
    (hwK : ∀ i, pullbackGerm (projectiveClosureMap (algebraMap A K) e) (V i) (w i : Γ(projectiveClosure (algebraMap A K) e, V i)) =
      T.germToFunctionField (c i).U (wK i : Γ(T, (c i).U)))
    (σ : Fin (N + 1) → Fin r → Option (Fin d)) (m m' : ℕ) (a : Fin r → ℕ)
    (hrelT : ∀ i, haveI : Nonempty (projectivePullbackCoordinateOpen e (kk i)) :=
        ⟨⟨(Classical.arbitrary (c i).U).1, hUk i (Classical.arbitrary (c i).U).2⟩⟩
      (gQ i : T.functionField) ^ (m * m') *
          (logTwistMonomial (c 0) (logSetOf (σ 0)) (logTwistExponent (σ 0) a) :
            T.functionField) ^ m' *
          T.germToFunctionField (c 0).U (wK 0 : Γ(T, (c 0).U)) =
        T.germToFunctionField (c i).U (wK i : Γ(T, (c i).U)) *
          T.germToFunctionField (projectivePullbackCoordinateOpen e (kk i))
            (projectivePullbackHomogeneousEquation e (kk i) 1 (MvPolynomial.X (kk 0))
              (MvPolynomial.isHomogeneous_X K (kk 0))) *
          (etaleChartCanonicalEquation (c 0) (c i) : T.functionField) ^ (m * m') *
          (logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a) :
            T.functionField) ^ m')
    (i : Fin (N + 1)) :
    letI := projectiveClosureOver e (algebraMap A K)
    ((projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE (le_inf (hWV i) (hWV₀ i))).op
        (u i)) ^ (m * m') *
        ((projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE (hWV₀ i)).op
          (∏ j ∈ logSetOf (σ 0), ψ 0 (MvPolynomial.X j) ^ logTwistExponent (σ 0) a j)) ^ m' *
        (projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE (hWV₀ i)).op
          (w 0 : Γ(projectiveClosure (algebraMap A K) e, V 0)) =
      (projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE (hWV i)).op (w i : Γ(projectiveClosure (algebraMap A K) e, V i)) *
        (projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE ((hWV i).trans (hVk i))).op
          (projectivePullbackHomogeneousEquation (projectiveClosureι (algebraMap A K) e) (kk i) 1
            (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X A (kk 0))) *
        ringJacobianOn (hV i) (hV 0) (hW i) (hWV i) (hWV₀ i) (ψ i) (ψ 0) (hψ i) (hψ 0) ^ (m * m') *
        ((projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE (hWV i)).op
          (∏ j ∈ logSetOf (σ i), ψ i (MvPolynomial.X j) ^ logTwistExponent (σ i) a j)) ^ m' := by
  classical
  let _ := projectiveClosureOver e (algebraMap A K)
  let φ := projectiveClosureMap (algebraMap A K) e
  have := projectiveClosure_isIntegral_of_isClosedImmersion e (algebraMap A K)
  have := projectiveClosureMap_isDominant e (algebraMap A K)
  have := projectiveClosureMap_isAffineHom e (algebraMap A K)
  have hneW' : ∀ j, Nonempty (W j) := fun j =>
    ⟨⟨φ (Classical.arbitrary (φ ⁻¹ᵁ W j)).1, (Classical.arbitrary (φ ⁻¹ᵁ W j)).2⟩⟩
  have hne0 : ∀ j, Nonempty (φ ⁻¹ᵁ (V j ⊓ V 0)) := fun j =>
    ⟨⟨(Classical.arbitrary (φ ⁻¹ᵁ W j)).1, (Opens.map φ.base).monotone (le_inf (hWV j) (hWV₀ j))
      (Classical.arbitrary (φ ⁻¹ᵁ W j)).2⟩⟩
  have hneR : ∀ j, Nonempty (φ ⁻¹ᵁ projectivePullbackCoordinateOpen
      (projectiveClosureι (algebraMap A K) e) (kk j)) := fun j =>
    ⟨⟨(Classical.arbitrary (φ ⁻¹ᵁ V j)).1, (Opens.map φ.base).monotone (hVk j)
      (Classical.arbitrary (φ ⁻¹ᵁ V j)).2⟩⟩
  refine relation_of_pullbackGerm_relation φ hWV hWV₀ hVk u
    (fun j => ∏ l ∈ logSetOf (σ j), ψ j (MvPolynomial.X l) ^ logTwistExponent (σ j) a l) (fun j => (w j : Γ(projectiveClosure (algebraMap A K) e, V j)))
    (fun j => projectivePullbackHomogeneousEquation (projectiveClosureι (algebraMap A K) e) (kk j) 1
      (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X A (kk 0)))
    (fun j => ringJacobianOn (hV j) (hV 0) (hW j) (hWV j) (hWV₀ j) (ψ j) (ψ 0) (hψ j) (hψ 0))
    m m' (fun j => ?_) i
  -- the germs of the monomials
  have hM : ∀ l, pullbackGerm φ (V l)
      (∏ j ∈ logSetOf (σ l), ψ l (MvPolynomial.X j) ^ logTwistExponent (σ l) a j) =
      (logTwistMonomial (c l) (logSetOf (σ l)) (logTwistExponent (σ l) a) : T.functionField) := by
    intro l
    rw [map_prod, logTwistMonomial, Units.coe_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val, hψc, etaleChartCoordinateRationalUnit,
      regularEquationRationalUnit_val]
  -- the germ of the chart equation
  have hr : pullbackGerm φ (projectivePullbackCoordinateOpen (projectiveClosureι (algebraMap A K) e)
      (kk j)) (projectivePullbackHomogeneousEquation (projectiveClosureι (algebraMap A K) e) (kk j) 1
        (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X A (kk 0))) =
      haveI : Nonempty (projectivePullbackCoordinateOpen e (kk j)) :=
        ⟨⟨(Classical.arbitrary (c j).U).1, hUk j (Classical.arbitrary (c j).U).2⟩⟩
      T.germToFunctionField (projectivePullbackCoordinateOpen e (kk j))
        (projectivePullbackHomogeneousEquation e (kk j) 1 (MvPolynomial.X (kk 0))
          (MvPolynomial.isHomogeneous_X K (kk 0))) := by
    have : Nonempty (projectivePullbackCoordinateOpen e (kk j)) :=
      ⟨⟨(Classical.arbitrary (c j).U).1, hUk j (Classical.arbitrary (c j).U).2⟩⟩
    have h := projectiveClosureMap_homogeneousEquation (algebraMap A K) e (kk j) 1
      (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X A (kk 0))
    simp only [MvPolynomial.map_X] at h
    rw [← germToFunctionField_appLE_eq_pullbackGerm φ
      (projectiveClosureMap_preimage_chart (algebraMap A K) e (kk j)).ge, h]
  -- the germ of the Jacobian
  have hJ : pullbackGerm φ (W j)
      (ringJacobianOn (hV j) (hV 0) (hW j) (hWV j) (hWV₀ j) (ψ j) (ψ 0) (hψ j) (hψ 0)) =
      (etaleChartCanonicalEquation (c 0) (c j) : T.functionField) := by
    have hcan := fibreEtaleChart_canonicalEquation HA (hV j) (hV 0) (hW j) (hWV j) (hWV₀ j) (ψ j)
      (ψ 0) (hψ j) (hψ 0) (hne j) (hne 0)
    rw [germToFunctionField_appLE_eq_pullbackGerm] at hcan
    rw [← hcan]
    congr 1
    exact etaleChartCanonicalEquation_congr
      (etaleChartFunctionFieldCoords_eq_of_germ fun l => by
        rw [fibreEtaleChart_coords_X]
        exact hψc 0 l)
      (etaleChartFunctionFieldCoords_eq_of_germ fun l => by
        rw [fibreEtaleChart_coords_X]
        exact hψc j l)
  rw [← hgQu, hM, hM, hwK, hwK, hr, hJ]
  exact hrelT j

end MixedFujita
