/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartBertini

/-!
Bertini on the coordinate strata of étale charts (step 8). Killing the variables X_i, i ∈ S, of a
polynomial ring gives the polynomial ring in the remaining variables (`MvPolynomial.killCompl`),
so the quotient K[X]/(X_i : i ∈ S) is smooth over K. For an étale chart y : K[X] → B the stratum
B/(y_i : i ∈ S) is the base change of B along K[X] → K[X]/(X_i : i ∈ S), hence étale over a smooth
K-algebra and smooth over K. In characteristic zero a general member Σ t_i v_i of a
base-point-free linear system on the chart is therefore smooth on every coordinate stratum at once
(`OAI.MaximalSeshadri.LinearBertini.affine_bertini` on each stratum); over an uncountable field one
very general member does this on countably many charts. On a chart in which the components of a
simple normal crossing divisor are coordinate hyperplanes, a general member is smooth and meets the
divisor transversally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

section Polynomial

variable {K σ : Type*} [Field K]

/-- Killing the variables in S: the quotient of K[X_σ] by (X_i : i ∈ S) is the polynomial ring in
the remaining variables. -/
noncomputable def polynomialKillEquiv (S : Set σ) :
    (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X (R := K) '' S)) ≃ₐ[K]
      MvPolynomial {j // j ∉ S} K := by
  classical
  let κ : MvPolynomial σ K →ₐ[K] MvPolynomial {j // j ∉ S} K :=
    MvPolynomial.killCompl (R := K) (Subtype.val_injective (p := fun j => j ∉ S))
  have hX : ∀ i, i ∈ S → κ (MvPolynomial.X i) = 0 := by
    intro i hi
    simp only [κ, MvPolynomial.killCompl, MvPolynomial.aeval_X]
    refine dite_eq_right ?_
    rintro ⟨j, rfl⟩
    exact j.2 hi
  have hκ : ∀ a ∈ Ideal.span (MvPolynomial.X (R := K) '' S), κ a = 0 := by
    intro a ha
    have hle : Ideal.span (MvPolynomial.X (R := K) '' S) ≤ RingHom.ker κ.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hX i hi
    exact hle ha
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ κ hκ)
    ((Ideal.Quotient.mkₐ K _).comp (MvPolynomial.rename Subtype.val)) ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro j
    change κ (MvPolynomial.rename Subtype.val (MvPolynomial.X j)) = MvPolynomial.X j
    exact MvPolynomial.killCompl_rename_app _ _
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk _ (MvPolynomial.rename Subtype.val (κ (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ (MvPolynomial.X i)
    by_cases hi : i ∈ S
    · rw [hX i hi, map_zero, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, hi, rfl⟩
    · have hκi : κ (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by
        simp only [κ, MvPolynomial.killCompl, MvPolynomial.aeval_X]
        rw [dite_eq_left ⟨⟨i, hi⟩, rfl⟩]
        congr 1
        apply (Equiv.ofInjective _ (Subtype.val_injective (p := fun j => j ∉ S))).injective
        rw [Equiv.apply_symm_apply]
        rfl
      rw [hκi, MvPolynomial.rename_X]

variable [Finite σ]

/-- The quotient of a polynomial ring in finitely many variables by some of the variables is smooth
over K. -/
theorem smooth_polynomial_quotient_variables (S : Set σ) :
    Algebra.Smooth K (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X (R := K) '' S)) :=
  have : Algebra.Smooth K (MvPolynomial {j // j ∉ S} K) := ⟨inferInstance, inferInstance⟩
  Algebra.Smooth.of_equiv (polynomialKillEquiv S).symm

end Polynomial

section Chart

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- The coordinate stratum {y_i = 0 : i ∈ S} of an étale chart, as an ideal of the chart ring. -/
noncomputable def etaleChartStratumIdeal (c : EtaleChart K X n) (S : Set (Fin n)) :
    Ideal Γ(X, c.U) :=
  (Ideal.span (MvPolynomial.X (R := K) '' S)).map c.coords

theorem etaleChartStratumIdeal_eq_span (c : EtaleChart K X n) (S : Set (Fin n)) :
    etaleChartStratumIdeal c S = Ideal.span ((fun i => c.coords (MvPolynomial.X i)) '' S) := by
  rw [etaleChartStratumIdeal, Ideal.map_span, Set.image_image]

/-- The images of a base-point-free family generate the unit ideal on every stratum. -/
theorem span_range_stratum_eq_top (c : EtaleChart K X n) (S : Set (Fin n)) {ι : Type*}
    (v : ι → Γ(X, c.U)) (hunit : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range fun i => Ideal.Quotient.mk (etaleChartStratumIdeal c S) (v i)) = ⊤ := by
  rw [Set.range_comp' (Ideal.Quotient.mk (etaleChartStratumIdeal c S)) v, ← Ideal.map_span, hunit,
    Ideal.map_top]

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The coordinate strata of an étale chart are smooth over K. -/
theorem etaleChart_stratum_smooth (c : EtaleChart K X n) (S : Set (Fin n)) :
    Algebra.Smooth K (Γ(X, c.U) ⧸ etaleChartStratumIdeal c S) := by
  let P := MvPolynomial (Fin n) K
  let B := Γ(X, c.U)
  let _ : Algebra P B := c.coords.toRingHom.toAlgebra
  have : IsScalarTower K P B := IsScalarTower.of_algebraMap_eq fun k => (c.coords.commutes k).symm
  have : Algebra.Etale P B := etaleChart_coords_etale c
  let J : Ideal P := Ideal.span (MvPolynomial.X (R := K) '' S)
  have : Algebra.Smooth K (P ⧸ J) := smooth_polynomial_quotient_variables S
  have : Algebra.Smooth K ((P ⧸ J) ⊗[P] B) := Algebra.Smooth.comp K (P ⧸ J) ((P ⧸ J) ⊗[P] B)
  let e : (B ⧸ J.map (algebraMap P B)) ≃ₐ[K] (P ⧸ J) ⊗[P] B :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).restrictScalars K).trans
      ((Algebra.TensorProduct.comm P B (P ⧸ J)).restrictScalars K)
  have hI : etaleChartStratumIdeal c S = J.map (algebraMap P B) := rfl
  rw [hI]
  refine Algebra.Smooth.of_equiv (A := (P ⧸ J) ⊗[P] B) ?_
  exact e.symm

/-- Bertini on the coordinate strata: for a base-point-free family of sections on countably many
étale charts, over an uncountable field of characteristic zero one very general member Σ t_i v_i
is smooth on every coordinate stratum of every chart. -/
theorem etaleCharts_veryGeneral_bertini_strata [CharZero K] [Uncountable K] {κ : Type*}
    [Countable κ] {ι : Type*} [Fintype ι] (c : κ → EtaleChart K X n)
    (v : ∀ k, ι → Γ(X, (c k).U)) (hunit : ∀ k, Ideal.span (Set.range (v k)) = ⊤) :
    ∃ t : ι → K, ∀ (k : κ) (S : Set (Fin n)),
      Algebra.Smooth K ((Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S) ⧸ Ideal.span
        ({(OAI.MaximalSeshadri.LinearBertini.specializedSection
          (fun i => Ideal.Quotient.mk (etaleChartStratumIdeal (c k) S) (v k i)) t)} :
            Set (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S))) := by
  have hpoly : ∀ (k : κ) (S : Set (Fin n)), ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K ((Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S) ⧸ Ideal.span
          ({(OAI.MaximalSeshadri.LinearBertini.specializedSection
            (fun i => Ideal.Quotient.mk (etaleChartStratumIdeal (c k) S) (v k i)) t)} :
              Set (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S))) := by
    intro k S
    have := etaleChart_stratum_smooth (c k) S
    exact OAI.MaximalSeshadri.LinearBertini.affine_bertini _
      (span_range_stratum_eq_top (c k) S (v k) (hunit k))
  choose p hp hsmooth using hpoly
  let e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_countable (ι := κ × Set (Fin n))
    (fun kS => MvPolynomial.rename e (p kS.1 kS.2))
    (fun kS h => hp kS.1 kS.2
      ((MvPolynomial.rename_injective _ e.injective) (h.trans (map_zero _).symm)))
  refine ⟨x ∘ e, fun k S => hsmooth k S _ ?_⟩
  have h := hx (k, S)
  rw [MvPolynomial.eval_rename] at h
  exact h

end Chart

end MixedFujita
