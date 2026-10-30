/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialNonzeroLocus
public import MixedFujita.HomogeneousIdealFamily

/-!
The universal linear combination of actual homogeneous polynomial forms.
Coefficient specialization is exact, coordinate parameter vectors recover
the individual generators, and the locus of nonzero residue-field forms
is an actual Zariski open. No Bertini, relative Cartier, or lct theorem is
asserted here.
-/

@[expose] public section

namespace MixedFujita

open scoped Classical

variable {R S σ ι : Type*} [CommRing R] [CommRing S]

noncomputable def universalHomogeneousForm (I : Finset ι) (g : ι → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial ι R) :=
  ∑ l ∈ I, MvPolynomial.C (MvPolynomial.X l) * MvPolynomial.map MvPolynomial.C (g l)

theorem universalHomogeneousForm_coeff (I : Finset ι) (g : ι → MvPolynomial σ R)
    (q : σ →₀ ℕ) :
    (universalHomogeneousForm I g).coeff q =
      ∑ l ∈ I, MvPolynomial.X l * MvPolynomial.C ((g l).coeff q) := by
  classical
  simp only [universalHomogeneousForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

theorem universalHomogeneousForm_isHomogeneous (I : Finset ι)
    (g : ι → MvPolynomial σ R) (d : ℕ) (hg : ∀ l ∈ I, (g l).IsHomogeneous d) :
    (universalHomogeneousForm I g).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro l hl
  exact ((hg l hl).map MvPolynomial.C).C_mul _

theorem universalHomogeneousForm_scalar (I : Finset ι) (g : ι → MvPolynomial σ R)
    (c : R →+* S) :
    MvPolynomial.map (MvPolynomial.map c) (universalHomogeneousForm I g) =
      universalHomogeneousForm I (fun l => MvPolynomial.map c (g l)) := by
  classical
  have hc : (MvPolynomial.map (σ := ι) c).comp MvPolynomial.C =
      (MvPolynomial.C : S →+* MvPolynomial ι S).comp c := by
    ext r
    simp
  unfold universalHomogeneousForm
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.map_map, hc]

theorem universalHomogeneousForm_specialize (I : Finset ι)
    (g : ι → MvPolynomial σ R) (a : ι → R) :
    MvPolynomial.map (MvPolynomial.eval₂Hom (RingHom.id R) a)
        (universalHomogeneousForm I g) =
      ∑ l ∈ I, MvPolynomial.C (a l) * g l := by
  classical
  have hc : (MvPolynomial.eval₂Hom (RingHom.id R) a).comp
      (MvPolynomial.C : R →+* MvPolynomial ι R) = RingHom.id R := by
    ext r
    simp
  simp only [universalHomogeneousForm, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.eval₂Hom_X', MvPolynomial.map_map, hc, MvPolynomial.map_id]

theorem universalHomogeneousForm_coordinate (I : Finset ι)
    (g : ι → MvPolynomial σ R) {l : ι} (hl : l ∈ I) :
    MvPolynomial.map (MvPolynomial.eval₂Hom (RingHom.id R)
        (fun i => if i = l then 1 else 0)) (universalHomogeneousForm I g) = g l := by
  classical
  rw [universalHomogeneousForm_specialize]
  simp [hl]

theorem universalHomogeneousForm_eq_zero_iff (I : Finset ι)
    (g : ι → MvPolynomial σ R) :
    universalHomogeneousForm I g = 0 ↔ ∀ l ∈ I, g l = 0 := by
  constructor
  · intro h l hl
    have hc := universalHomogeneousForm_coordinate I g hl
    rw [h, map_zero] at hc
    exact hc.symm
  · intro h
    classical
    unfold universalHomogeneousForm
    exact Finset.sum_eq_zero (fun l hl => by rw [h l hl, map_zero, mul_zero])

theorem universalHomogeneousForm_ne_zero (I : Finset ι)
    (g : ι → MvPolynomial σ R) {l : ι} (hl : l ∈ I) (hg : g l ≠ 0) :
    universalHomogeneousForm I g ≠ 0 := by
  intro h
  exact hg ((universalHomogeneousForm_eq_zero_iff I g).mp h l hl)

theorem universalHomogeneousForm_mem_extendedIdeal (I : Finset ι)
    (g : ι → MvPolynomial σ R) :
    universalHomogeneousForm I g ∈
      Ideal.map (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ι R))
        (Ideal.span (Set.range (fun l : I => g l))) := by
  classical
  apply Ideal.sum_mem
  intro l hl
  apply Ideal.mul_mem_left
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨l, hl⟩, rfl⟩)

theorem universalHomogeneousForm_nonzeroLocus_coordinate {K : Type*} [Field K]
    (I : Finset ι) (g : ι → MvPolynomial σ K) {l : ι} (hl : l ∈ I) (hg : g l ≠ 0) :
    ¬ polynomialCoefficientIdeal (universalHomogeneousForm I g) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id K)
        (fun i => if i = l then 1 else 0)) := by
  rw [← polynomial_map_eq_zero_iff, universalHomogeneousForm_coordinate I g hl]
  exact hg

variable {n : ℕ} {K : Type*} [Field K]

noncomputable def universalParameterHomogeneousForm (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) (MvPolynomial ι (Polynomial K)) :=
  universalHomogeneousForm I (fun l => homogeneousParameterFamily w (p l) (f l))

theorem universalParameterHomogeneousForm_isHomogeneous (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (universalParameterHomogeneousForm I w p f).IsHomogeneous d :=
  universalHomogeneousForm_isHomogeneous I _ d
    (fun l hl => homogeneousParameterFamily_isHomogeneous w (p l) (hf l hl))

theorem universalParameterHomogeneousForm_baseChange (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (t : K) :
    MvPolynomial.map (MvPolynomial.map (Polynomial.evalRingHom t))
        (universalParameterHomogeneousForm I w p f) =
      universalHomogeneousForm I
        (fun l => (weightedPolynomialFamily w (p l) (f l)).eval (MvPolynomial.C t)) := by
  rw [universalParameterHomogeneousForm, universalHomogeneousForm_scalar]
  congr 1
  funext l
  exact homogeneousParameterFamily_baseChange w (p l) (f l) t

theorem universalParameterHomogeneousForm_at_one (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    MvPolynomial.map (MvPolynomial.map (Polynomial.evalRingHom 1))
        (universalParameterHomogeneousForm I w p f) = universalHomogeneousForm I f := by
  rw [universalParameterHomogeneousForm_baseChange]
  simp only [map_one, weightedPolynomialFamily_at_one]

theorem universalParameterHomogeneousForm_at_zero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    MvPolynomial.map (MvPolynomial.map (Polynomial.evalRingHom 0))
        (universalParameterHomogeneousForm I w p f) =
      universalHomogeneousForm I (fun l => MvPolynomial.monomial (p l) ((f l).coeff (p l))) := by
  rw [universalParameterHomogeneousForm, universalHomogeneousForm_scalar]
  unfold universalHomogeneousForm
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only
  rw [homogeneousParameterFamily_at_zero w (p l) (f l) (hp l hl) (hw l hl)]

theorem homogeneousParameterFamily_all_fibers_nonzero (w : Fin n → ℕ)
    (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) (hp : p ∈ f.support)
    (hw : ∀ q ∈ f.support, q ≠ p → polynomialExponentWeight w p < polynomialExponentWeight w q)
    (t : K) : MvPolynomial.map (Polynomial.evalRingHom t)
      (homogeneousParameterFamily w p f) ≠ 0 := by
  by_cases ht : t = 0
  · subst t
    rw [homogeneousParameterFamily_at_zero w p f hp hw]
    exact MvPolynomial.monomial_eq_zero.not.mpr (MvPolynomial.mem_support_iff.mp hp)
  · rw [homogeneousParameterFamily_baseChange]
    apply weightedPolynomialFamily_nonzero_fiber w p f ht
    · intro h
      simp [h] at hp
    · intro q hq
      by_cases he : q = p
      · simp [he]
      · exact (hw q hq he).le

theorem universalParameterHomogeneousForm_fiber_ne_zero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) {l : ι} (hl : l ∈ I)
    (hp : p l ∈ (f l).support)
    (hw : ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) (t : K) :
    MvPolynomial.map (MvPolynomial.map (Polynomial.evalRingHom t))
      (universalParameterHomogeneousForm I w p f) ≠ 0 := by
  rw [universalParameterHomogeneousForm, universalHomogeneousForm_scalar]
  exact universalHomogeneousForm_ne_zero I _ hl
    (homogeneousParameterFamily_all_fibers_nonzero w (p l) (f l) hp hw t)

theorem universalParameterHomogeneousForm_fiber_good_vector (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) {l : ι} (hl : l ∈ I)
    (hp : p l ∈ (f l).support)
    (hw : ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) (t : K) :
    ∃ a : ι → K, MvPolynomial.map (MvPolynomial.eval₂Hom (RingHom.id K) a)
      (MvPolynomial.map (MvPolynomial.map (Polynomial.evalRingHom t))
        (universalParameterHomogeneousForm I w p f)) ≠ 0 := by
  refine ⟨fun i => if i = l then 1 else 0, ?_⟩
  rw [universalParameterHomogeneousForm, universalHomogeneousForm_scalar,
    universalHomogeneousForm_coordinate I _ hl]
  exact homogeneousParameterFamily_all_fibers_nonzero w (p l) (f l) hp hw t

end MixedFujita
