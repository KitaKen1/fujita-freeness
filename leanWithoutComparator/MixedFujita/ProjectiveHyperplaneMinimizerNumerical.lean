/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneMinimizerSequence
public import MixedFujita.PointClosureHyperplaneRestriction

/-!
The data of the minimizer for the hyperplane class from the numerical hypothesis (steps 11 and
14).

Let Y be a smooth closed subvariety of dimension m of projective space with hyperplane divisor J,
cut by a linear form g that does not vanish at the closed point x, and take the zero boundary.
The numerical hypothesis of the main statements for A = J asks, for every point η whose closure
has dimension d ≥ 1 and every ε > 0, that for all large j some sections of j J restrict to the
closure of η with dimension at least ((m + 1)^d - ε) j^d/d!. It gives the degree condition of
section 5 with s = m + 1 (`projectiveHyperplane_degreeCondition_of_restrictedGrowth`), and the
closures of points have finite dimension at most m. So, with b = 1, the data of the minimizer
exist at x for every m₀ ≥ 1 as soon as the closedness of the realization sets and the interior
condition (7) hold for all large degrees and all t in [t₀, 1), and the specialization comparison
(6) holds there in the form of section 2.3 of the manuscript: over an uncountable field, at the
closed points of the closure of each generization w ≠ x of x outside countably many proper closed
subsets.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer at x for the hyperplane class with zero boundary, for every m₀ ≥ 1,
from the numerical hypothesis for J, the closedness of the realization sets, the interior
condition (7) and the specialization comparison (6) at very general closed points, at all large
degrees. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_of_restrictedGrowth
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal) {t₀ δ : ℝ} (ht₀ : t₀ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < 1 →
      ∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ)
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < 1 → ∀ w : Y, w ⤳ x → w ≠ x →
      ∃ Z : ℕ → Set Y, (∀ i, IsClosed (Z i)) ∧ (∀ i, w ∉ Z i) ∧
        ∀ y : Y, IsClosed ({y} : Set Y) → (∀ i, y ∉ Z i) → w ⤳ y →
        sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) x
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j ≤
          sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) y
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (projectiveHyperplaneCartier e g hg hggen) m₀ x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  -- the degree condition with s = m + 1
  have hdeg := projectiveHyperplane_degreeCondition_of_restrictedGrowth e g hg hggen he x (m + 1)
    (fun η d hd hd1 ε hε => by
      have h := hgrow η d hd hd1 ε hε
      push_cast
      exact h)
  exact projectiveHyperplane_kltIsolationMinimizerData_of_degree_sequence e g hg hggen he hm cY x
    hxc hgx (b := 1) one_pos le_rfl (m + 1) (by omega) (by push_cast; ring) ht₀ hδ hδ1
    (fun w _ => exists_nat_topologicalKrullDim_closure_eq hdimY w) hdeg hclosed hstart
    (h6.mono fun j hj t h1 h2 w hwx hne => by
      obtain ⟨Z, hZ, hwZ, hZ6⟩ := hj t h1 h2 w hwx hne
      exact ⟨_, closedPointsDenseOver_of_countable Z hZ hwZ,
        fun y hyc hyG hwy => hZ6 y hyc (fun i => Set.mem_iInter.mp hyG i) hwy⟩) m₀ hm₀

end Hyperplane

end MixedFujita
