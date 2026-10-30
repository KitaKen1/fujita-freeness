/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveAmpleMixedIntersectionPositive
public import MixedFujita.NonzeroEffectiveCartierCut
public import MixedFujita.ProjectiveNumericalIitakaZero
public import MixedFujita.SemiampleNumericalIitakaUpperBound

/-! 正の元飯高指数から第一混合交点数と元数値次元の正値性。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Positive ORIGINAL Iitaka exponent of a semiample divisor forces its
FIRST original ample mixed intersection to be strictly positive. The actual
nonzero effective multiple and its nonempty cut are constructed internally. -/
theorem proper_semiample_positive_iitaka_first_mixed_intersection_positive
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hk : 1 ≤ k) (hkappa : CartierIitakaDimension K D k) :
    0 < cartierMixedIntersection K (D :: List.replicate (n - 1) J)
      (by simp only [List.length_cons, List.length_replicate]; simpa only [Nat.sub_add_cancel hn] using hdim) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  obtain ⟨q, hq, hgen⟩ := hD
  have hkq : CartierIitakaDimension K (q • D) k :=
    (cartierIitakaDimension_nsmul_iff_of_ample_ambient hdim hn hJ D hq k).mp hkappa
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgen
  let f := cartierSectionUnit (q • D) s hs
  let G := cartierSectionZeroDivisor (q • D) s hs
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective (q • D) s hs
  have hGne : G ≠ 0 := by
    intro hzero
    have hEq : q • D = principalCartierDivisor X f⁻¹ := by
      rw [principalCartierDivisor_inv]
      have h : q • D + principalCartierDivisor X f = 0 := hzero
      exact eq_neg_of_add_eq_zero_left h
    have hnum : CartierIsNumericallyTrivial K (q • D) := by
      rw [hEq]
      exact cartierIsNumericallyTrivial_principal f⁻¹
    have hkzero := projective_iitakaZero_of_numericallyTrivial_of_positive_generated_multiple
      hdim hn ⟨J, hJ⟩ (q • D) hnum ⟨1, by decide, by simpa only [one_nsmul] using hgen⟩
    have hkeq : k = 0 := CartierIitakaDimension_unique K hkq hkzero
    omega
  have hne := normal_nonzero_effectiveCartierCut_nonempty hnorm G hG hGne
  have hdim' : topologicalKrullDim X = ((n - 1) + 1 : ℕ) := by
    simpa only [Nat.sub_add_cancel hn] using hdim
  have hpos := proper_effective_nonempty_ample_cartierMixedEuler_positive K (n - 1) hdim'
    G hG hne (List.replicate (n - 1) J) (List.length_replicate ..)
      (fun H hH => (List.mem_replicate.mp hH).2 ▸ hJ) 0
  change 0 < cartierMixedEulerDifference K
    ((q • D + principalCartierDivisor X f) :: List.replicate (n - 1) J) 0 at hpos
  rw [cartierMixedEulerDifference_direction_principal] at hpos
  have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K n hdim.le []
    (List.replicate (n - 1) J) (by simp only [List.length_nil, List.length_replicate]; omega) D 0 q
  simp only [List.nil_append] at hscale
  rw [hscale] at hpos
  exact (mul_pos_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hpos


/-- Every positive original Iitaka exponent forces the ORIGINAL maximum
of positive mixed powers to be at least one. -/
theorem proper_semiample_positive_iitaka_numerical_dimension_pos
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hk : 1 ≤ k) (hkappa : CartierIitakaDimension K D k) :
    1 ≤ cartierNumericalDimension K n hdim D J := by
  have hpos : 0 < cartierMixedPowerIntersection K n hdim D J ⟨1, by omega⟩ :=
    proper_semiample_positive_iitaka_first_mixed_intersection_positive K n hdim hn hnorm D J hJ hD k hk hkappa
  exact Finset.le_sup (f := Fin.val)
    (show (⟨1, by omega⟩ : Fin (n + 1)) ∈ ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun k => 0 < cartierMixedPowerIntersection K n hdim D J k)) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)

end MixedFujita
