/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleFromLocalEquations
public import MixedFujita.LogChartFrobeniusCartier

/-!
The adjoint divisor is ample from a chartwise relation (step 10, R4-3).

Let `Y` be a smooth integral variety over a field with a closed immersion `e : Y → ℙ_κ`, a simple
normal crossing family `ξ` with component divisors `E_k`, and simple normal crossing charts `c_i`
covering `Y` with `c_i.U ⊆ D₊(X_{k(i)})`. Let `Q` have local equations `g_i` on `c_i.U` and let
`K_Y` be the canonical divisor with reference chart `c_0`, with local equations `J_i` (the chart
equations). With the coordinate monomials `M_i = Π y_{i,j}^{e_{ij}}` of `Σ a_k E_k` (check 490),
if for units `w_i` on `c_i.U`
`g_i^{m m'} · M_0^{m'} · w_0 = w_i · (X_{k(0)}/X_{k(i)}) · J_i^{m m'} · M_i^{m'}`,
then `m (Q − K_Y) − Σ a_k E_k` is ample (`cartierIsAmpleProj_adjoint_of_chartRelation`): its local
equations `λ_i = (g_i J_i⁻¹)^m M_i⁻¹` satisfy `λ_i^{m'} = w_i (X_{k(0)}/X_{k(i)}) f` with
`f = M_0^{−m'} w_0⁻¹`, and check 538 applies.

On the fibre `T_κ` all factors are images of functions on the closure `T_A`, and the relation is
the image of one on `T_A` spread from `T`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra Classical.propDecidable

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
/-- **The adjoint divisor `m (Q − K_Y) − Σ a_k E_k` is ample from a chartwise relation.** -/
theorem cartierIsAmpleProj_adjoint_of_chartRelation {P : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme P κ) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase P κ = Y ↘ Spec (CommRingCat.of κ)) {N : ℕ}
    (c : Fin (N + 1) → EtaleChart κ Y d) (σ : Fin (N + 1) → Fin r → Option (Fin d))
    (hc : ∀ i, IsSNCChart (c i) ξ (σ i)) (hcov : ⨆ i, (c i).U = ⊤)
    (hcover : iSup (fun c : EtaleChart κ Y d => c.U) = ⊤) (kk : Fin (N + 1) → Fin P)
    (hUk : ∀ i, (c i).U ≤ projectivePullbackCoordinateOpen e (kk i)) (Q : CartierDivisor Y)
    (gQ : Fin (N + 1) → Y.functionFieldˣ) (hgQ : ∀ i, ∀ y ∈ (c i).U, Q.IsLocalEquationAt y (gQ i))
    (m m' : ℕ) (hm' : 1 ≤ m') (a : Fin r → ℕ) (w : ∀ i, Γ(Y, (c i).U)ˣ)
    (hrel : ∀ i, haveI : Nonempty (projectivePullbackCoordinateOpen e (kk i)) :=
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
            Y.functionField) ^ m') :
    CartierIsAmpleProj κ (m • (Q - canonicalDivisor d (c 0) hcover) - ∑ k, a k • E k) := by
  classical
  have : Nonempty (projectivePullbackCoordinateOpen e (kk 0)) :=
    ⟨⟨(Classical.arbitrary (c 0).U).1, hUk 0 (Classical.arbitrary (c 0).U).2⟩⟩
  let M : Fin (N + 1) → Y.functionFieldˣ := fun i =>
    logTwistMonomial (c i) (logSetOf (σ i)) (logTwistExponent (σ i) a)
  let lam : Fin (N + 1) → Y.functionFieldˣ := fun i =>
    (gQ i * (etaleChartCanonicalEquation (c 0) (c i))⁻¹) ^ m * (M i)⁻¹
  let f : Y.functionFieldˣ := ((M 0) ^ m')⁻¹ * (regularUnitToFunctionField Y (c 0).U (w 0))⁻¹
  refine cartierIsAmpleProj_of_localEquations e he (kk 0) _ m' hm' f (fun i => (c i).U) hcov kk
    hUk lam (fun i y hy => ?_) w (fun i => ?_)
  · -- the local equations of the adjoint divisor
    simp only [sub_eq_add_neg]
    exact (isLocalEquationAt_nsmul_pow ((hgQ i y hy).mul
      (canonicalDivisor_isLocalEquationAt (c 0) hcover (c i) hy).inv) m).mul
      (isLocalEquationAt_logTwistMonomial (c i) (σ i) a hnorm ξ hinj hξ E hEc (hc i) y hy).inv
  · -- the relation, in the function field
    have h := hrel i
    have hW0 : ((regularUnitToFunctionField Y (c 0).U (w 0) : Y.functionFieldˣ) :
        Y.functionField) = Y.germToFunctionField (c 0).U (w 0 : Γ(Y, (c 0).U)) :=
      by rw [regularUnitToFunctionField_apply, Units.coe_map]; rfl
    rw [← hW0] at h
    have hgoal : ((lam i ^ m' : Y.functionFieldˣ) : Y.functionField) =
        (((gQ i : Y.functionField) * (etaleChartCanonicalEquation (c 0) (c i) :
          Y.functionField)⁻¹) ^ m * (M i : Y.functionField)⁻¹) ^ m' := by
      simp only [lam, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    have hf : (f : Y.functionField) = ((M 0 : Y.functionField) ^ m')⁻¹ *
        ((regularUnitToFunctionField Y (c 0).U (w 0) : Y.functionFieldˣ) : Y.functionField)⁻¹ := by
      simp only [f, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hgoal, hf]
    have hJ : (etaleChartCanonicalEquation (c 0) (c i) : Y.functionField) ≠ 0 := Units.ne_zero _
    have hMi : (M i : Y.functionField) ≠ 0 := Units.ne_zero _
    have hM0 : (M 0 : Y.functionField) ≠ 0 := Units.ne_zero _
    have hW0ne : ((regularUnitToFunctionField Y (c 0).U (w 0) : Y.functionFieldˣ) :
      Y.functionField) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [div_pow, ← pow_mul]
    field_simp
    linear_combination h

end MixedFujita
