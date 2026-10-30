/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianCriterionCharts
public import MixedFujita.VeryGeneralPoint
public import OAI.AlgebraicGeometry.Seshadri.Bertini.CriticalLocus
public import OAI.AlgebraicGeometry.Seshadri.Bertini.LinearFamilies

/-!
Bertini on étale charts (step 8), from the affine Bertini theorem of openai/math
(`OAI.MaximalSeshadri.Bertini.affine_bertini_smooth`, vendored under the Apache License 2.0).
The ring of an étale chart of a scheme locally of finite type over a field K is smooth over K,
and the differentials of the coordinates form a basis of its Kähler differentials. In
characteristic zero, for finitely many sections v_i on the chart, a general member
t_0 + Σ t_i v_i of the linear system spanned by the constants and the v_i cuts out a smooth
K-algebra: there is a nonzero polynomial p in the parameters such that p(t) ≠ 0 suffices. Over an
uncountable field, countably many charts with finite families of sections admit common very
general parameters, so one member is smooth on all of them at once. The same holds for a
base-point-free linear system Σ t_i v_i without the constants (the v_i generate the unit ideal),
from `OAI.MaximalSeshadri.LinearBertini.affine_bertini`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The ring of an étale chart is smooth over K. -/
theorem etaleChart_smooth (c : EtaleChart K X n) : Algebra.Smooth K Γ(X, c.U) := by
  let _ := c.coords.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) Γ(X, c.U) :=
    IsScalarTower.of_algebraMap_eq fun k => (c.coords.commutes k).symm
  have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U) := etaleChart_coords_etale c
  exact Algebra.Smooth.comp K (MvPolynomial (Fin n) K) Γ(X, c.U)

/-- Bertini on an étale chart: a general member t_0 + Σ t_i v_i of the linear system spanned by
the constants and finitely many sections v_i cuts out a smooth K-algebra. -/
theorem etaleChart_bertini_smooth [CharZero K] (c : EtaleChart K X n) {ι : Type*} [Fintype ι]
    (v : ι → Γ(X, c.U)) :
    ∃ p : MvPolynomial (Option ι) K, p ≠ 0 ∧ ∀ t : Option ι → K, MvPolynomial.aeval t p ≠ 0 →
      Algebra.Smooth K (Γ(X, c.U) ⧸ Ideal.span
        ({OAI.MaximalSeshadri.Bertini.specializedSection v t} : Set Γ(X, c.U))) := by
  have := etaleChart_smooth c
  exact OAI.MaximalSeshadri.Bertini.affine_bertini_smooth
    (etaleCoordinateBasis c.coords c.formallyEtale) v

/-- Very general members: for countably many étale charts with finite families of sections indexed
by the same type, one choice of parameters gives a smooth member on every chart. -/
theorem etaleCharts_veryGeneral_bertini_smooth [CharZero K] [Uncountable K] {κ : Type*}
    [Countable κ] {ι : Type*} [Fintype ι] (c : κ → EtaleChart K X n)
    (v : ∀ k, ι → Γ(X, (c k).U)) :
    ∃ t : Option ι → K, ∀ k, Algebra.Smooth K (Γ(X, (c k).U) ⧸ Ideal.span
      ({OAI.MaximalSeshadri.Bertini.specializedSection (v k) t} : Set Γ(X, (c k).U))) := by
  choose p hp hsmooth using fun k => etaleChart_bertini_smooth (c k) (v k)
  let e := Fintype.equivFin (Option ι)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_countable (fun k => MvPolynomial.rename e (p k))
    (fun k h => hp k ((MvPolynomial.rename_injective _ e.injective) (h.trans (map_zero _).symm)))
  refine ⟨x ∘ e, fun k => hsmooth k _ ?_⟩
  have h := hx k
  rw [MvPolynomial.eval_rename] at h
  exact h

/-- Bertini for a base-point-free linear system on an étale chart: if the sections v_i generate the
unit ideal, a general member Σ t_i v_i cuts out a smooth K-algebra. -/
theorem etaleChart_bertini_smooth_of_span_eq_top [CharZero K] (c : EtaleChart K X n) {ι : Type*}
    [Fintype ι] (v : ι → Γ(X, c.U)) (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      Algebra.Smooth K (Γ(X, c.U) ⧸ Ideal.span
        ({OAI.MaximalSeshadri.LinearBertini.specializedSection v t} : Set Γ(X, c.U))) := by
  have := etaleChart_smooth c
  exact OAI.MaximalSeshadri.LinearBertini.affine_bertini v hunit

/-- Very general members of base-point-free linear systems on countably many étale charts: one
choice of parameters gives a smooth member on every chart. -/
theorem etaleCharts_veryGeneral_bertini_smooth_of_span_eq_top [CharZero K] [Uncountable K]
    {κ : Type*} [Countable κ] {ι : Type*} [Fintype ι] (c : κ → EtaleChart K X n)
    (v : ∀ k, ι → Γ(X, (c k).U)) (hunit : ∀ k, Ideal.span (Set.range (v k)) = ⊤) :
    ∃ t : ι → K, ∀ k, Algebra.Smooth K (Γ(X, (c k).U) ⧸ Ideal.span
      ({OAI.MaximalSeshadri.LinearBertini.specializedSection (v k) t} : Set Γ(X, (c k).U))) := by
  choose p hp hsmooth using fun k => etaleChart_bertini_smooth_of_span_eq_top (c k) (v k) (hunit k)
  let e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_countable (fun k => MvPolynomial.rename e (p k))
    (fun k h => hp k ((MvPolynomial.rename_injective _ e.injective) (h.trans (map_zero _).symm)))
  refine ⟨x ∘ e, fun k => hsmooth k _ ?_⟩
  have h := hx k
  rw [MvPolynomial.eval_rename] at h
  exact h

end MixedFujita
