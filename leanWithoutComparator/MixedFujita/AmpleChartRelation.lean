/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartwiseAmpleRelation
public import MixedFujita.CartierAtlasCocycle

/-!
The chartwise relation from an ample relation (step 10, R4-3).

This is the converse of check 539. On `Y` with the charts `c_i ⊆ D₊(X_{k(i)})`, if
`m' • (m (Q − K_Y) − Σ a_k E_k) = H_{X_{k₀}} + div f` with `k₀ = k(0)`, where `Q` has local
equations `g_i` on `c_i` with `g_0 = 1` and `K_Y` has reference chart `c_0`, then there are units
`w_i` on `c_i` with
`g_i^{m m'} · M_0^{m'} · w_0 = w_i · (X_{k₀}/X_{k(i)}) · J_i^{m m'} · M_i^{m'}`
(`exists_chartRelation_of_eq_hyperplane_add_principal`): the local equations
`λ_i^{m'} = ((g_i J_i⁻¹)^m M_i⁻¹)^{m'}` and `(X_{k₀}/X_{k(i)}) f` of the two sides differ by units
(check 534), and on `c_0` the relation gives `f = M_0^{−m'} w_0⁻¹`.

On `T_K` the units `w_i` are then spread to the closure `T_A` (check 535), where the relation becomes
an identity of functions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

universe u

variable {κ : Type u} [Field κ] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of κ))]
  [IsLocallyNoetherian Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of κ))]
  [∀ z : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (z : Y))]
  (hnorm : ∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z))
  {d r : ℕ} (ξ : Fin r → Y) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor Y)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint Y),
    cartierCoefficient (E k) (z : Y) = if (z : Y) = ξ k then 1 else 0)

include hnorm hinj hξ hEc in
/-- **An ample relation `m' • (m (Q − K_Y) − Σ a_k E_k) = H + div f` gives the chartwise
relation of check 539.** -/
theorem exists_chartRelation_of_eq_hyperplane_add_principal {P : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme P κ) {N : ℕ} (c : Fin (N + 1) → EtaleChart κ Y d)
    (σ : Fin (N + 1) → Fin r → Option (Fin d)) (hc : ∀ i, IsSNCChart (c i) ξ (σ i))
    (hcover : iSup (fun c : EtaleChart κ Y d => c.U) = ⊤) (kk : Fin (N + 1) → Fin P)
    (hUk : ∀ i, (c i).U ≤ projectivePullbackCoordinateOpen e (kk i)) (Q : CartierDivisor Y)
    (gQ : Fin (N + 1) → Y.functionFieldˣ) (hgQ : ∀ i, ∀ y ∈ (c i).U, Q.IsLocalEquationAt y (gQ i))
    (hgQ0 : gQ 0 = 1) (m m' : ℕ) (a : Fin r → ℕ) (f : Y.functionFieldˣ)
    (hggen : MvPolynomial.X (kk 0) ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (heq : m' • (m • (Q - canonicalDivisor d (c 0) hcover) - ∑ k, a k • E k) =
      projectiveHyperplaneCartier e (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X κ (kk 0))
        hggen + principalCartierDivisor Y f) :
    ∃ w : ∀ i, Γ(Y, (c i).U)ˣ, ∀ i, haveI : Nonempty (projectivePullbackCoordinateOpen e (kk i)) :=
        ⟨⟨(Classical.arbitrary (c i).U).1, hUk i (Classical.arbitrary (c i).U).2⟩⟩
      (gQ i : Y.functionField) ^ (m * m') *
          (logTwistMonomial (c 0) (logSetOf (σ 0)) (logTwistExponent (σ 0) a) :
            Y.functionField) ^ m' *
          Y.germToFunctionField (c 0).U (w 0 : Γ(Y, (c 0).U)) =
        Y.germToFunctionField (c i).U (w i : Γ(Y, (c i).U)) *
          Y.germToFunctionField (projectivePullbackCoordinateOpen e (kk i))
            (projectivePullbackHomogeneousEquation e (kk i) 1 (MvPolynomial.X (kk 0))
              (MvPolynomial.isHomogeneous_X κ (kk 0))) *
          (etaleChartCanonicalEquation (c 0) (c i) : Y.functionField) ^ (m * m') *
          (logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a) :
            Y.functionField) ^ m' := by
  classical
  let M : Fin (N + 1) → Y.functionFieldˣ := fun i =>
    logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a)
  let lam : Fin (N + 1) → Y.functionFieldˣ := fun i =>
    (gQ i * (etaleChartCanonicalEquation (c 0) (c i))⁻¹) ^ m * (M i)⁻¹
  -- the two local equations of the common divisor on each chart
  have hne : ∀ i, Nonempty (projectivePullbackCoordinateOpen e (kk i)) := fun i =>
    ⟨⟨(Classical.arbitrary (c i).U).1, hUk i (Classical.arbitrary (c i).U).2⟩⟩
  let hyp : Fin (N + 1) → Y.functionFieldˣ := fun i =>
    projectiveHyperplaneUnit e (MvPolynomial.X (kk 0)) (MvPolynomial.isHomogeneous_X κ (kk 0)) hggen
      ⟨kk i, hne i⟩
  have hlam : ∀ i, ∀ y ∈ (c i).U, (m' • (m • (Q - canonicalDivisor d (c 0) hcover) -
      ∑ k, a k • E k)).IsLocalEquationAt y (lam i ^ m') := by
    intro i y hy
    refine isLocalEquationAt_nsmul_pow ?_ m'
    simp only [sub_eq_add_neg]
    exact (isLocalEquationAt_nsmul_pow ((hgQ i y hy).mul
      (canonicalDivisor_isLocalEquationAt (c 0) hcover (c i) hy).inv) m).mul
      (isLocalEquationAt_logTwistMonomial (c i) (σ i) a hnorm ξ hinj hξ E hEc (hc i) y hy).inv
  have hrhs : ∀ i, ∀ y ∈ (c i).U, (m' • (m • (Q - canonicalDivisor d (c 0) hcover) -
      ∑ k, a k • E k)).IsLocalEquationAt y (hyp i * f) := by
    intro i y hy
    rw [heq]
    exact (projectiveHyperplane_isLocalEquationAt e (MvPolynomial.X (kk 0))
      (MvPolynomial.isHomogeneous_X κ (kk 0)) hggen ⟨kk i, hne i⟩ y (hUk i hy)).mul
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor y f)
  choose w hw using fun i => exists_unit_germ_eq_of_isLocalEquationAt (hlam i) (hrhs i)
  refine ⟨w, fun i => ?_⟩
  -- the values of the hyperplane equations and of the reference chart
  have hyp_val : ∀ j, (hyp j : Y.functionField) =
      Y.germToFunctionField (projectivePullbackCoordinateOpen e (kk j))
        (projectivePullbackHomogeneousEquation e (kk j) 1 (MvPolynomial.X (kk 0))
          (MvPolynomial.isHomogeneous_X κ (kk 0))) := fun j => rfl
  have hyp0 : (hyp 0 : Y.functionField) = 1 := by
    rw [hyp_val, projectivePullbackHomogeneousEquation_X_self, map_one]
  have hJ0 : (etaleChartCanonicalEquation (c 0) (c 0) : Y.functionField) = 1 := by
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
  have h0 := hw 0
  have hi := hw i
  simp only [lam, M, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hgQ0,
    Units.val_one] at h0 hi
  rw [hJ0, hyp0] at h0
  rw [hyp_val] at hi
  have hf : (f : Y.functionField) ≠ 0 := Units.ne_zero _
  have hJ : (etaleChartCanonicalEquation (c 0) (c i) : Y.functionField) ≠ 0 := Units.ne_zero _
  have hMi : (logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a) :
    Y.functionField) ≠ 0 := Units.ne_zero _
  have hM0 : (logTwistMonomial (c 0) (logSetOf (σ 0)) (logTwistExponent (σ 0) a) :
    Y.functionField) ≠ 0 := Units.ne_zero _
  have hgi : (gQ i : Y.functionField) ≠ 0 := Units.ne_zero _
  have hHy : Y.germToFunctionField (projectivePullbackCoordinateOpen e (kk i))
      (projectivePullbackHomogeneousEquation e (kk i) 1 (MvPolynomial.X (kk 0))
        (MvPolynomial.isHomogeneous_X κ (kk 0))) ≠ 0 := by
    rw [← hyp_val]
    exact Units.ne_zero _
  simp only [inv_one, one_mul, one_pow, mul_one, mul_pow, inv_pow, ← pow_mul] at h0 hi
  field_simp at h0 hi
  linear_combination (-((logTwistMonomial (c 0) (logSetOf (σ 0)) (logTwistExponent (σ 0) a) :
      Y.functionField) ^ m' * Y.germToFunctionField (c 0).U (w 0 : Γ(Y, (c 0).U)))) * hi +
    (Y.germToFunctionField (c i).U (w i : Γ(Y, (c i).U)) *
      Y.germToFunctionField (projectivePullbackCoordinateOpen e (kk i))
        (projectivePullbackHomogeneousEquation e (kk i) 1 (MvPolynomial.X (kk 0))
          (MvPolynomial.isHomogeneous_X κ (kk 0))) *
      (etaleChartCanonicalEquation (c 0) (c i) : Y.functionField) ^ (m * m') *
      (logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a) :
        Y.functionField) ^ m') * h0

end MixedFujita
