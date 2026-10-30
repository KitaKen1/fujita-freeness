/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorLinearCombination
public import MixedFujita.FixedCoefficientSpecialization
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
Return the explicit corrected polynomial coefficients to the same linear
combination in the source module of a given Taylor map. A nonzero parameter
form then gives exact Taylor order, a nonzero source element, its actual
linear-span membership, and the precise diagonal equation. The module is
also instantiated at actual global sections of an O_X-module over K.
The Taylor map, order bounds, closed bad locus and good zero fiber are
explicit inputs. Exceptional-divisor restriction and KV lifting are not
constructed here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {K ι V : Type u} [Field K] [AddCommGroup V] [Module K V]

noncomputable def correctedTaylorCombination
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → V) (a : ι → K) (t : K) : V :=
  ∑ l ∈ I, correctedCoefficientVector w p a t l • s l

theorem correctedTaylorCombination_leadingForm
    (d : ℕ) (T : V →ₗ[K] MvPowerSeries (Fin n) K)
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → V) (a : ι → K) (t : K) :
    homogeneousTaylorForm d (T (correctedTaylorCombination I w p s a t)) =
      ∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) *
        taylorLeadingLinearMap d T (s l) :=
  taylorLeadingLinearMap_linearCombination d T I s _

theorem fixedCoefficientTaylorCombination_exact_order
    (d : ℕ) (T : V →ₗ[K] MvPowerSeries (Fin n) K)
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → V) (a : ι → K) {t : K} (ht : t ≠ 0)
    (hs : ∀ l ∈ I, (d : ℕ∞) ≤ (T (s l)).order)
    (hw : ∀ l ∈ I, ∀ q ∈ (taylorLeadingLinearMap d T (s l)).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (hF : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) ≠ 0) :
    (T (correctedTaylorCombination I w p s a t)).order = (d : ℕ∞) ∧
      correctedTaylorCombination I w p s a t ≠ 0 ∧
      correctedTaylorCombination I w p s a t ∈
        Submodule.span K (Set.range (fun l : I => s l)) ∧
      MvPolynomial.map (Polynomial.evalRingHom t)
        (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) =
        polynomialDiagonalHom w t
          (homogeneousTaylorForm d (T (correctedTaylorCombination I w p s a t))) := by
  have h0 := (fixedCoefficientParameterForm_nonzero_original_combination
    I w p (fun l => taylorLeadingLinearMap d T (s l)) a ht hw hF).1
  obtain ⟨ho, hn⟩ := taylor_linearCombination_exact_order d T I s
    (correctedCoefficientVector w p a t) hs h0
  refine ⟨ho, hn, taylor_linearCombination_mem_span I s _, ?_⟩
  rw [correctedTaylorCombination_leadingForm]
  exact fixedCoefficientParameterForm_nonzero_parameter_diagonal
    I w p (fun l => taylorLeadingLinearMap d T (s l)) a ht hw

theorem fixedCoefficientTaylor_good_combination [Infinite K]
    (d : ℕ) (T : V →ₗ[K] MvPowerSeries (Fin n) K)
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → V) (a : ι → K)
    (hs : ∀ l ∈ I, (d : ℕ∞) ≤ (T (s l)).order)
    (hw : ∀ l ∈ I, ∀ q ∈ (taylorLeadingLinearMap d T (s l)).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (hzero : MvPolynomial.map (Polynomial.evalRingHom 0)
      (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) ≠ 0)
    {Z : Set (((polynomialProjectiveToBase n (Polynomial K)) ⁻¹ᵁ
      (polynomialNonzeroLocus
        (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) :
        (Spec (CommRingCat.of (Polynomial K))).Opens)).toScheme)}
    (hZ : IsClosed Z)
    (hgoodzero : ∀ x, projectiveNonzeroAmbientProjection
      (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) x =
      (⟨polynomialParameterPoint (0 : K),
        (polynomialParameterPoint_mem_nonzeroLocus 0 _).mpr hzero⟩ :
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
          (polynomialNonzeroLocus
            (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a))) →
        x ∉ Z) :
    ∃ t : K, t ≠ 0 ∧ ∃ hF : MvPolynomial.map (Polynomial.evalRingHom t)
        (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) ≠ 0,
      (T (correctedTaylorCombination I w p s a t)).order = (d : ℕ∞) ∧
      correctedTaylorCombination I w p s a t ≠ 0 ∧
      correctedTaylorCombination I w p s a t ∈
        Submodule.span K (Set.range (fun l : I => s l)) ∧
      MvPolynomial.map (Polynomial.evalRingHom t)
        (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) =
        polynomialDiagonalHom w t
          (homogeneousTaylorForm d (T (correctedTaylorCombination I w p s a t))) ∧
      ∀ x, projectiveNonzeroAmbientProjection
        (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) x =
        (⟨polynomialParameterPoint t,
          (polynomialParameterPoint_mem_nonzeroLocus t _).mpr hF⟩ :
          Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
            (polynomialNonzeroLocus
              (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a))) →
          x ∉ Z := by
  obtain ⟨t, ht, hF, hgood⟩ := projectiveNonzeroForm_good_nonzero_parameter
    (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a)
    hzero hZ hgoodzero
  obtain ⟨ho, hn, hm, he⟩ := fixedCoefficientTaylorCombination_exact_order
    d T I w p s a ht hs hw hF
  exact ⟨t, ht, hF, ho, hn, hm, he, hgood⟩

omit [AddCommGroup V] [Module K V] in
theorem fixedCoefficientGlobalSection_exact_order
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] (M : X.Modules)
    (d : ℕ) (T : Γ(M, ⊤) →ₗ[K] MvPowerSeries (Fin n) K)
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → Γ(M, ⊤)) (a : ι → K) {t : K} (ht : t ≠ 0)
    (hs : ∀ l ∈ I, (d : ℕ∞) ≤ (T (s l)).order)
    (hw : ∀ l ∈ I, ∀ q ∈ (taylorLeadingLinearMap d T (s l)).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (hF : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p (fun l => taylorLeadingLinearMap d T (s l)) a) ≠ 0) :
    (T (correctedTaylorCombination I w p s a t)).order = (d : ℕ∞) ∧
      correctedTaylorCombination I w p s a t ≠ 0 ∧
      correctedTaylorCombination I w p s a t ∈
        Submodule.span K (Set.range (fun l : I => s l)) := by
  obtain ⟨ho, hn, hm, _⟩ := fixedCoefficientTaylorCombination_exact_order
    d T I w p s a ht hs hw hF
  exact ⟨ho, hn, hm⟩

omit [AddCommGroup V] [Module K V] in
theorem correctedGlobalSection_restriction
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] (M : X.Modules)
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (s : ι → Γ(M, ⊤)) (a : ι → K) (t : K) (U : X.Opens) :
    M.presheaf.map U.leTop.op (correctedTaylorCombination I w p s a t) =
      ∑ l ∈ I, (X.presheaf.map U.leTop.op
        (Scheme.Modules.baseRingToGlobalSections K X (correctedCoefficientVector w p a t l))) •
          M.presheaf.map U.leTop.op (s l) := by
  simp only [correctedTaylorCombination, map_sum,
    Scheme.Modules.base_smul_globalSections, Scheme.Modules.map_smul]

end MixedFujita
