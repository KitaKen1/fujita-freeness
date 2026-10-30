/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleCartierEulerLimit
public import MixedFujita.TopMixedEulerHomogeneity
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.FiniteProjectiveCartierAmpleness

/-! 超平面Hilbert次数の正整数規格化と元ample因子の対角正値性。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The diagonal top Euler coefficient for an actual embedded integral
variety is the positive integer in its already proved Hilbert degree
asymptotics. No smoothness, normality or characteristic-zero hypothesis. -/
theorem projectiveHyperplane_cartierMixedEuler_diagonal_positive
    {K : Type u} [Field K] [Infinite K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (e : X ⟶ polynomialProjectiveScheme r K) [IsClosedImmersion e]
    (g : MvPolynomial (Fin r) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (he : e ≫ polynomialProjectiveToBase r K = X ↘ Spec (CommRingCat.of K))
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) :
    ∃ d : ℕ, 1 ≤ d ∧
      cartierMixedEulerDifference K
        (List.replicate n (projectiveHyperplaneCartier e g hg hggen)) 0 = d := by
  let : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper r K
    rw [← he]
    infer_instance
  let H := projectiveHyperplaneCartier e g hg hggen
  obtain ⟨d, hd, hfin, hdlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdim hn
  have hH : CartierIsAmpleProj K H :=
    projectiveHyperplaneCartier_isAmpleProj_of_finite e g hg hggen he
  have hlim := proper_ample_cartier_sections_scaled_limit K n hdim.le H 0 hH
  have hzero (j : ℕ) : Module.finrank K Γ((0 + j • H).sheaf, ⊤) =
      Module.finrank K Γ((j • H).sheaf, ⊤) :=
    moduleSections_finrank_congr K (eqToIso (congrArg CartierDivisor.sheaf (zero_add (j • H))))
  have hlim' := hlim.congr' (Filter.Eventually.of_forall fun (j : ℕ) =>
    congrArg (fun v : ℕ => (v : ℝ) / (j : ℝ) ^ n) (hzero j))
  have heq := tendsto_nhds_unique hlim' hdlim
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hval : (cartierMixedEulerDifference K (List.replicate n H) 0 : ℝ) = d :=
    (div_left_inj' hfac).mp heq
  exact ⟨d, hd, by exact_mod_cast hval⟩


/-- An ORIGINAL ample Cartier class has positive diagonal top coefficient
in every positive dimension over an infinite field. Its projective multiple,
principal shift and positive Hilbert degree are all constructed internally. -/
theorem proper_ample_cartierMixedEuler_diagonal_positive
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H) (E : CartierDivisor X) :
    0 < cartierMixedEulerDifference K (List.replicate n H) E := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hggen, f, hmH⟩ := hH
  let := he
  let J := projectiveHyperplaneCartier e g hg hggen
  let a : (m • H).sheaf ≅ J.sheaf :=
    eqToIso (congrArg CartierDivisor.sheaf hmH) ≪≫ cartierSheafPrincipalShiftIso J f
  have hdirs : List.Forall₂ (fun D F : CartierDivisor X => Nonempty (D.sheaf ≅ F.sheaf))
      (List.replicate n (m • H)) (List.replicate n J) := by
    suffices ∀ k : ℕ, List.Forall₂ (fun D F : CartierDivisor X => Nonempty (D.sheaf ≅ F.sheaf))
        (List.replicate k (m • H)) (List.replicate k J) from this n
    intro k
    induction k with
    | zero => exact .nil
    | succ k ih => exact .cons ⟨a⟩ ih
  have heq := cartierMixedEulerDifference_direction_isos K hdirs E
  have hbase := proper_cartierMixedEulerDifference_top_base_independent K n hdim.le
    (List.replicate n J) (List.length_replicate ..) E 0
  obtain ⟨d, hd, hdegree⟩ := projectiveHyperplane_cartierMixedEuler_diagonal_positive
    e g hg hggen hover n hdim hn
  have hscale := proper_cartierMixedEulerDifference_diagonal_nsmul K n hdim.le H E m
  have hpos : 0 < (m : ℤ) ^ n * cartierMixedEulerDifference K (List.replicate n H) E := by
    rw [← hscale, heq, hbase, hdegree]
    exact_mod_cast (show 0 < d by omega)
  have hmpos : (0 : ℤ) < (m : ℤ) ^ n := pow_pos (by exact_mod_cast (show 0 < m by omega)) n
  exact (mul_pos_iff_of_pos_left hmpos).mp hpos

end MixedFujita
