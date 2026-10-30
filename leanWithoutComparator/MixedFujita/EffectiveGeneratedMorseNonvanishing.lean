/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedPullbackAmpleSerreHilbert
public import MixedFujita.PolynomialStrictLeadingComparison
public import MixedFujita.EffectiveCutHilbertLeadingComparison

/-! 元ample−有効大域生成の全十分大倍数の実非消滅。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] effectiveCartierCutOverField

/-- Weak algebraic Morse nonvanishing for an ORIGINAL ample direction and
an effective globally generated cut. The strict input is the actual intersection
inequality, with no Hilbert-polynomial or cohomological witness supplied. -/
theorem proper_ample_sub_effective_generated_eventually_nonzero_of_mixed_inequality
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (H G : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (hG : G.IsEffective) (hgen : CartierIsGloballyGenerated G)
    (hnum : (n + 1 : ℤ) * cartierMixedEulerDifference K (G :: List.replicate n H) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) H) 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ s : Γ((m • (H - G)).sheaf, ⊤), s ≠ 0 := by
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let P := cartierEulerPolynomial K (n + 1) H 0
  let Q := cartierPulledModuleEulerPolynomial K i (SheafOfModules.unit Y.ringCatSheaf) n H 0
  obtain ⟨a, ha⟩ := rationalPolynomial_eventually_mul_eval_lt_of_top_coeff P Q n
    (cartierEulerPolynomial_natDegree_le K (n + 1) H 0)
    (cartierPulledModuleEulerPolynomial_natDegree_le K i _ n H 0)
    (effectiveCartierCut_EulerPolynomial_top_coeff_lt K n hdim H G hG hnum)
  obtain ⟨b, hb⟩ := (proper_ample_cartierEulerPolynomial_eventually_eq_sections
    K (n + 1) hdim H 0 hH).2
  obtain ⟨c, hc⟩ := proper_closed_pulled_cartierEulerPolynomial_eventually_eq_sections K i n
    (effectiveCartierCut_topologicalKrullDim_le G hG n hdim) H 0 hH
  refine ⟨max (max a b) (max c 1), by omega, fun m hm => ?_⟩
  have hp : P.eval (m : ℚ) = (Module.finrank K Γ((m • H).sheaf, ⊤) : ℚ) := by
    exact (hb m (by omega)).trans (congrArg
      (fun D : CartierDivisor X => (Module.finrank K Γ(D.sheaf, ⊤) : ℚ)) (zero_add _))
  have hq : Q.eval (m : ℚ) =
      (Module.finrank K Γ((Scheme.Modules.pullback i).obj (m • H).sheaf, ⊤) : ℚ) := by
    exact (hc m (by omega)).trans (congrArg
      (fun D : CartierDivisor X =>
        (Module.finrank K Γ((Scheme.Modules.pullback i).obj D.sheaf, ⊤) : ℚ)) (zero_add _))
  have h := ha m (by omega)
  rw [hp, hq] at h
  have hcount : m * Module.finrank K Γ((Scheme.Modules.pullback i).obj (m • H).sheaf, ⊤) <
      Module.finrank K Γ((m • H).sheaf, ⊤) := by exact_mod_cast h
  have he : m • H - m • G = m • (H - G) := (smul_sub m H G).symm
  rw [← he]
  exact proper_exists_nonzero_section_sub_generated_cut_of_count_lt K (m • H) G hG hgen m hcount

end MixedFujita
