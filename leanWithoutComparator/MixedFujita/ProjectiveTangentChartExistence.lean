/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightCenterDegree

/-!
The chart data at a general closed point of the centre of a weight, for a closed subscheme of
projective space (the geometric input of the inequalities of one degree, section 5.1).

Let π : X → Y be a morphism from a smooth variety with a simple normal crossing family to a closed
subscheme Y of projective space, over an algebraically closed field of characteristic zero, and w
a weight on the family with a point on all its members of positive weight. There is a point η,
the generic point of a component of the stratum of the members of positive weight, such that for
every coordinate chart k of the projective space containing π(η) and every open set V containing
η there are a closed point z of the closure of η in V over the chart k, a simple normal crossing
chart at z and η, Taylor coordinates at z given by the chart, and a set T of tangent coordinates,
with: the selected coordinates are exactly those of the members of positive weight; the tangent
coordinates are pullbacks of coordinate ratios X_j / X_k minus constants; the pullbacks of all
germs at π(η) have their derivatives in the remaining coordinates outside the family in the
maximal ideal of η; and T is nonempty unless π(η) = π(z). These are the hypotheses on the chart
of `projectiveHyperplane_centerDegreeInequalities`. The general form takes the closed point z in a
given set whose closed points are dense in the closure of η (for the very general points of the
specialization comparison (6)).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {Y X : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] [IsIntegral X] [IsLocallyNoetherian X]
  [X.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]

/-- The chart data at a closed point of the centre of a weight lying in a given set G whose closed
points are dense in the closure of η, for a closed subscheme of projective space. -/
theorem projectiveHyperplane_exists_closedPoint_tangent_chart_dense
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) {r : ℕ}
    (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      (∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η) ∧
      ∀ (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)}),
        π η ∈ projectivePullbackCoordinateOpen e k.val → ∀ V : Set X, IsOpen V → η ∈ V →
        ∀ G : Set X, (∀ O : Set X, IsOpen O → η ∈ O →
          ∃ z ∈ G, IsClosed ({z} : Set X) ∧ z ∈ closure ({η} : Set X) ∧ z ∈ O) →
        ∃ (z : X) (_ : IsClosed ({z} : Set X)) (_ : η ⤳ z) (_ : z ∈ V) (_ : z ∈ G)
          (hzU : π z ∈ projectivePullbackCoordinateOpen e k.val) (c : EtaleChart K X n)
          (σc : Fin r → Option (Fin n)) (hz : z ∈ c.U) (hη : η ∈ c.U) (Tan : Finset (Fin n))
          (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
            (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K),
          IsSNCChart c ξ σc ∧
          (∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
            MvPowerSeries.X i) ∧
          (∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0) ∧
          (∀ b ∈ Tan, ∀ k, σc k ≠ some b) ∧
          (∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k.val} =>
              projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j)), ∃ κ : K,
            etaleChartStalkCoords c z hz (MvPolynomial.X b) =
              π.stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k.val) (π z) hzU
                (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k.val) κ))) ∧
          (∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ Tan →
            etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
              (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
                IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ∧
          (π η ≠ π z → Tan.Nonempty) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨η, hη, hηy, hmax, hall⟩ :=
    exists_closedPoint_tangent_chart_of_weight_dense π ξ hsnc w y hwy
  refine ⟨η, hη, hηy, hmax, fun k hηk V hV hηV G hG => ?_⟩
  obtain ⟨z, hzcl, hηz, hzV, hzG, hzU, c, σc, hz, hηc, Tan, hc, hnu, hiff, hTan, hsat⟩ :=
    hall (projectivePullbackCoordinateOpen e k.val)
      (projectivePullbackCoordinateOpen_isAffineOpen e k.val) hηk
      (Set.range fun j : {j : Fin N // j ≠ k.val} =>
        projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j))
      (projectivePullback_adjoin_coordinates_eq_top e he k.val) V hV hηV G hG
  -- Taylor coordinates at z given by the chart, all of whose coordinates vanish at z
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) z hzcl
  obtain ⟨ez, hez, -⟩ := etaleChart_exists_taylorCoordinates c z hz β
  have hez' : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i := by
    intro i
    have h1 := hez i
    rw [etaleChartCenteredStalkCoords_variable] at h1
    have h0 : rationalAffineGermPoint z hz β (c.coords (MvPolynomial.X i)) = 0 := by
      change β (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X i))) = 0
      exact not_not.mp ((rationalLocalPoint_isUnit_iff β _).not.mp (hnu i))
    rw [h0, map_zero, sub_zero] at h1
    exact h1
  refine ⟨z, hzcl, hηz, hzV, hzG, hzU, c, σc, hz, hηc, Tan, ez, hc, hez', hiff,
    fun b hb => (hTan b hb).1, fun b hb => (hTan b hb).2, hsat, fun hne => ?_⟩
  -- without tangent coordinates the image of the centre would be π(z)
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  exact hne (map_eq_of_forall_derivative_mem π ξ c σc hc w η hηc hη hmax z hz hηz ez hez' hiff
    (fun h' b hb => hsat h' b hb (by rw [hempty]; exact Finset.notMem_empty b)))

/-- The chart data at a general closed point of the centre of a weight, for a closed subscheme
of projective space. -/
theorem projectiveHyperplane_exists_closedPoint_tangent_chart
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) {r : ℕ}
    (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      (∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η) ∧
      ∀ (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)}),
        π η ∈ projectivePullbackCoordinateOpen e k.val → ∀ V : Set X, IsOpen V → η ∈ V →
        ∃ (z : X) (_ : IsClosed ({z} : Set X)) (_ : η ⤳ z) (_ : z ∈ V)
          (hzU : π z ∈ projectivePullbackCoordinateOpen e k.val) (c : EtaleChart K X n)
          (σc : Fin r → Option (Fin n)) (hz : z ∈ c.U) (hη : η ∈ c.U) (Tan : Finset (Fin n))
          (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
            (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K),
          IsSNCChart c ξ σc ∧
          (∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
            MvPowerSeries.X i) ∧
          (∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0) ∧
          (∀ b ∈ Tan, ∀ k, σc k ≠ some b) ∧
          (∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k.val} =>
              projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j)), ∃ κ : K,
            etaleChartStalkCoords c z hz (MvPolynomial.X b) =
              π.stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k.val) (π z) hzU
                (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k.val) κ))) ∧
          (∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ Tan →
            etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
              (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
                IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ∧
          (π η ≠ π z → Tan.Nonempty) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨η, hη, hηy, hmax, hall⟩ :=
    projectiveHyperplane_exists_closedPoint_tangent_chart_dense π e he ξ hsnc w y hwy
  refine ⟨η, hη, hηy, hmax, fun k hηk V hV hηV => ?_⟩
  obtain ⟨z, hzcl, hηz, hzV, -, h⟩ := hall k hηk V hV hηV Set.univ fun O hO hηO => by
    obtain ⟨z, ⟨hzη, hzO⟩, hzcl⟩ := nonempty_inter_closedPoints
      (Z := closure ({η} : Set X) ∩ O) ⟨η, subset_closure rfl, hηO⟩
      (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
    exact ⟨z, Set.mem_univ z, mem_closedPoints_iff.mp hzcl, hzη, hzO⟩
  exact ⟨z, hzcl, hηz, hzV, h⟩

end MixedFujita
