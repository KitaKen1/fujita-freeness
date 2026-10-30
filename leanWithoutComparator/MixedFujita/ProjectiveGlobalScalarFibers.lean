/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveIdealSheafGluing
public import MixedFujita.ProjectivePolynomialMaps

/-!
Chart coefficient maps commute with the actual global Proj scalar maps.
Global ideal-sheaf pullbacks preserve the generated ideals, and the parameter
zero and one closed subschemes are actual categorical pullbacks along the
Proj evaluation maps, including their closed immersions. The ambient Proj
coefficient-base-change square over Spec R is a separate obligation; no
flatness or lct semicontinuity is asserted here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem polynomialScalarAwayMap_commutes {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) (k : Fin n)
    (b : MvPolynomial (Fin n) S) (hb : b = MvPolynomial.map c (MvPolynomial.X k))
    (hb₁ : b.IsHomogeneous 1)
    (m : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) S) b)
    (hm : ∀ d a (ha : a.IsHomogeneous d),
      m (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d a
        (by simpa using ha)) =
      HomogeneousLocalization.Away.mk _ hb₁ d (MvPolynomial.map c a)
        (by simpa using ha.map c)) :
    Proj.awayι _ b hb₁ Nat.zero_lt_one ≫ polynomialScalarProjectiveMap c hc =
      Spec.map (CommRingCat.ofHom m) ≫
        Proj.awayι _ (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one := by
  subst b
  have hmap : m = HomogeneousLocalization.Away.map (polynomialScalarGradedMap c)
      (MvPolynomial.X k) := by
    apply RingHom.ext
    intro x
    obtain ⟨d, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.isHomogeneous_X R k) x
    rw [hm d a (by simpa using ha)]
    exact (HomogeneousLocalization.Away.map_mk (polynomialScalarGradedMap c)
      (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) d a ha).symm
  rw [hmap]
  exact Proj.awayι_comp_map (polynomialScalarGradedMap c)
    (graded_irrelevant_le_map_of_surjective _ (polynomialScalarGradedMap_surjective c hc))
    Nat.zero_lt_one (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k)

theorem projectiveChartScalarSchemeMap_global_commutes {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) (k : Fin n) :
    projectiveChartScalarSchemeMap c k ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
        polynomialScalarProjectiveMap c hc := by
  apply (cancel_epi (polynomialProjectiveCoordinateChartIso n S k).inv).mp
  simp only [projectiveChartScalarSchemeMap, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]
  change Spec.map (CommRingCat.ofHom (projectiveChartScalarMap c k)) ≫
      Proj.awayι _ _ (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one =
    Proj.awayι _ _ (MvPolynomial.isHomogeneous_X S k) Nat.zero_lt_one ≫
      polynomialScalarProjectiveMap c hc
  exact (polynomialScalarAwayMap_commutes c hc k (MvPolynomial.X k)
    (MvPolynomial.map_X c k).symm (MvPolynomial.isHomogeneous_X S k)
    (projectiveChartScalarMap c k) (projectiveChartScalarMap_mk c k)).symm

theorem homogeneousProjectiveIdealSheaf_scalar {R S : Type u} {ι : Type*}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c)
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (homogeneousProjectiveIdealSheaf I f d hf).comap (polynomialScalarProjectiveMap c hc) =
      homogeneousProjectiveIdealSheaf I (fun l => MvPolynomial.map c (f l)) d
        (fun l hl => (hf l hl).map c) := by
  apply homogeneousProjectiveIdealSheaf_unique
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartScalarSchemeMap_global_commutes c hc k,
    Scheme.IdealSheafData.comap_comp, homogeneousProjectiveIdealSheaf_restrict,
    projectiveChartIdealSheaf_scalar, homogeneousChartLocalizationIdeal_scalar]

theorem homogeneousChartLocalizationIdeal_monomial {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (d : ℕ)
    (hp : ∀ l ∈ I, (p l).degree = d) (k : Fin n) :
    homogeneousChartLocalizationIdeal I (fun l => MvPolynomial.monomial (p l) (1 : R)) d
        (fun l hl => MvPolynomial.isHomogeneous_monomial 1 (hp l hl)) k =
      projectiveChartMonomialIdeal (R := R) I p k := by
  apply projectiveChartIdealMap_injective R k
  rw [homogeneousChartLocalizationIdeal_affine, projectiveChartMonomialIdeal_affine,
    projectiveChartIdeal, Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  simp only [projectiveDehomogenize_monomial, map_one, one_mul]

noncomputable def homogeneousProjectiveMonomialIdealSheaf {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (d : ℕ)
    (hp : ∀ l ∈ I, (p l).degree = d) :
    (polynomialProjectiveScheme n R).IdealSheafData :=
  homogeneousProjectiveIdealSheaf I (fun l => MvPolynomial.monomial (p l) (1 : R)) d
    (fun l hl => MvPolynomial.isHomogeneous_monomial 1 (hp l hl))

theorem homogeneousProjectiveMonomialIdealSheaf_restrict {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (d : ℕ)
    (hp : ∀ l ∈ I, (p l).degree = d) (k : Fin n) :
    (homogeneousProjectiveMonomialIdealSheaf (R := R) I p d hp).comap
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι =
      projectiveChartIdealSheaf R k (projectiveChartMonomialIdeal (R := R) I p k) := by
  rw [homogeneousProjectiveMonomialIdealSheaf, homogeneousProjectiveIdealSheaf_restrict,
    homogeneousChartLocalizationIdeal_monomial I p d hp k]

theorem homogeneous_support_degree {K : Type u} [Field K] {ι : Type*}
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (hp : ∀ l ∈ I, p l ∈ (f l).support) :
    ∀ l ∈ I, (p l).degree = d := by
  intro l hl
  have hd := hf l hl (MvPolynomial.mem_support_iff.mp (hp l hl))
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hd

theorem homogeneousParameterProjectiveIdealSheaf_at_zero {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    (homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
        (polynomialParameterProjectiveEval (0 : K)) =
      homogeneousProjectiveMonomialIdealSheaf I p d (homogeneous_support_degree I p f d hf hp) := by
  apply idealSheaf_ext_of_affine_restrictions _ _
    (polynomialProjectiveCoordinateAffineOpen K)
    (polynomialProjective_coordinate_opens_cover n K)
  intro k
  change ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
      (polynomialScalarProjectiveMap (Polynomial.evalRingHom (0 : K))
        (fun c => ⟨Polynomial.C c, by simp⟩))).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartScalarSchemeMap_global_commutes, Scheme.IdealSheafData.comap_comp,
    homogeneousParameterProjectiveIdealSheaf_restrict,
    homogeneousParameterChartIdealSheaf_at_zero I w p f d hf k hp hw,
    homogeneousProjectiveMonomialIdealSheaf_restrict]

theorem homogeneousParameterProjectiveIdealSheaf_at_one {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
        (polynomialParameterProjectiveEval (1 : K)) =
      homogeneousProjectiveIdealSheaf I f d hf := by
  apply homogeneousProjectiveIdealSheaf_unique
  intro k
  change ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
      (polynomialScalarProjectiveMap (Polynomial.evalRingHom (1 : K))
        (fun c => ⟨Polynomial.C c, by simp⟩))).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartScalarSchemeMap_global_commutes, Scheme.IdealSheafData.comap_comp,
    homogeneousParameterProjectiveIdealSheaf_restrict,
    homogeneousParameterChartIdealSheaf_at_one]

theorem homogeneousParameterProjectiveZeroSubscheme_pullback {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    ∃ e : (homogeneousProjectiveMonomialIdealSheaf I p d
        (homogeneous_support_degree I p f d hf hp)).subscheme ≅
      pullback (polynomialParameterProjectiveEval (0 : K))
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι,
      e.hom ≫ pullback.fst _ _ =
        (homogeneousProjectiveMonomialIdealSheaf I p d
          (homogeneous_support_degree I p f d hf hp)).subschemeι := by
  rw [← homogeneousParameterProjectiveIdealSheaf_at_zero I w p f d hf hp hw]
  exact ⟨(homogeneousParameterProjectiveIdealSheaf I w p f d hf).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

theorem homogeneousParameterProjectiveOneSubscheme_pullback {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    ∃ e : (homogeneousProjectiveIdealSheaf I f d hf).subscheme ≅
      pullback (polynomialParameterProjectiveEval (1 : K))
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι,
      e.hom ≫ pullback.fst _ _ = (homogeneousProjectiveIdealSheaf I f d hf).subschemeι := by
  rw [← homogeneousParameterProjectiveIdealSheaf_at_one I w p f d hf]
  exact ⟨(homogeneousParameterProjectiveIdealSheaf I w p f d hf).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

theorem homogeneousProjectiveIdealSheaf_subscheme_isProper {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    IsProper ((homogeneousProjectiveIdealSheaf I f d hf).subschemeι ≫
      polynomialProjectiveToBase n R) := by
  have := polynomialProjectiveToBase_isProper n R
  infer_instance

end MixedFujita
