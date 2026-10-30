/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightPartitionBound
public import MixedFujita.ProjectiveChartGenerators
public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.ProjectiveHomogenization

/-!
The cube of tangent monomials from the linear forms of a projective chart (section 5.2 of the
manuscript), and (20) for the hyperplane class with the growth of the restricted sections as the
only remaining hypothesis.

Let Y be a closed subscheme of projective space with hyperplane divisor J, π : X → Y a morphism
and z a point of X over the coordinate chart k, with a chart at z whose tangent coordinates are
pullbacks of coordinate ratios X_j / X_k minus constants (as provided by
`exists_closedPoint_tangent_chart_of_weight` for the generators of `ProjectiveChartGenerators`).

* For every set s of tangent coordinates the product of the corresponding polynomials
  X_j - κ has degree at most the number of elements of s, and the Taylor expansion at z of its
  pullback is the squarefree monomial of s.
* Homogenizing in degree h₀ at least the number of tangent coordinates gives a form of degree h₀
  whose section of h₀ J has graded Taylor expansion exactly the squarefree monomial of s: the cube.
* Hence (20) for the Taylor data of a weight and the hyperplane class, with h₀ the number of
  tangent coordinates, given the root bound for the restricted dimensions at π(η).
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

variable {K : Type u} [Field K] [CharZero K] {N n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K)
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [CharZero K] [IsIntegral Y] [IsLocallyNoetherian X] [π.IsOver (Spec (CommRingCat.of K))] in
/-- The product of the polynomials of a set of tangent coordinates: its degree is at most the
number of the coordinates and the Taylor expansion of its pullback is their squarefree
monomial. -/
theorem exists_polynomial_taylor_eq_tangent_monomial
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (k : Fin N)
    (z : X) (hzU : π z ∈ projectivePullbackCoordinateOpen e k) (c : EtaleChart K X n)
    (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (Tan : Finset (Fin n))
    (hTanU : ∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k} =>
        projectivePullbackAffinePolynomialMap e k (MvPolynomial.X j)), ∃ κ : K,
      etaleChartStalkCoords c z hz (MvPolynomial.X b) =
        π.stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k) (π z) hzU
          (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k) κ)))
    (s : Finset (Fin n)) (hs : s ⊆ Tan) :
    ∃ P : MvPolynomial {j : Fin N // j ≠ k} K, P.totalDegree ≤ s.card ∧
      stalkTaylorExpansion z ez (π.stalkMap z (Y.presheaf.germ
        (projectivePullbackCoordinateOpen e k) (π z) hzU
        (projectivePullbackAffinePolynomialMap e k P))) =
          MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single i 1) 1 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp, ?_⟩
    rw [map_one, map_one, map_one, map_one, Finset.sum_empty]
    exact MvPowerSeries.monomial_zero_one.symm
  | insert b s hb ih =>
    obtain ⟨P, hPdeg, hP⟩ := ih (fun i hi => hs (Finset.mem_insert_of_mem hi))
    obtain ⟨g', ⟨j, rfl⟩, κ, hbκ⟩ := hTanU b (hs (Finset.mem_insert_self b s))
    refine ⟨(MvPolynomial.X j - MvPolynomial.C κ) * P, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hb]
      have h1 : (MvPolynomial.X j - MvPolynomial.C κ :
          MvPolynomial {j : Fin N // j ≠ k} K).totalDegree ≤ 1 :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le
          (by rw [MvPolynomial.totalDegree_X])
          (by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1))
      have h2 := MvPolynomial.totalDegree_mul (MvPolynomial.X j - MvPolynomial.C κ :
        MvPolynomial {j : Fin N // j ≠ k} K) P
      omega
    · rw [map_mul, map_mul, map_mul, map_mul, hP, map_sub,
        projectivePullbackAffinePolynomialMap_C_eq_algebraMap e he k κ, ← hbκ, hez b,
        Finset.sum_insert hb, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

omit [CharZero K] [IsLocallyNoetherian X] in
/-- The cube: for every set s of tangent coordinates and every degree h₀ at least the number of
tangent coordinates, some form section of h₀ J has graded Taylor expansion the squarefree monomial
of s. -/
theorem projectiveHyperplane_exists_section_taylor_eq_tangent_monomial
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)})
    (z : X) (hzU : π z ∈ projectivePullbackCoordinateOpen e k.val) (c : EtaleChart K X n)
    (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (Tan : Finset (Fin n))
    (hTanU : ∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k.val} =>
        projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j)), ∃ κ : K,
      etaleChartStalkCoords c z hz (MvPolynomial.X b) =
        π.stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k.val) (π z) hzU
          (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k.val) κ)))
    (s : Finset (Fin n)) (hs : s ⊆ Tan) (h₀ : ℕ) (hh₀ : Tan.card ≤ h₀) :
    ∃ x : Γ((h₀ • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      cartierGradedPullbackTaylor π (projectiveHyperplaneCartier e g hg hggen) z
        (projectiveHyperplaneUnit e g hg hggen k)
        (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez h₀ x =
          MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single i 1) 1 := by
  obtain ⟨P, hPdeg, hP⟩ := exists_polynomial_taylor_eq_tangent_monomial π e he k.val z hzU c hz
    ez hez Tan hTanU s hs
  have hdeg : P.totalDegree ≤ h₀ := hPdeg.trans ((Finset.card_le_card hs).trans hh₀)
  refine ⟨projectiveFormSection e g hg hggen k h₀ (projectiveHomogenize k.val h₀ P)
    (projectiveHomogenize_isHomogeneous k.val P hdeg), ?_⟩
  change stalkTaylorExpansion z ez (π.stalkMap z (cartierLocalCoefficient
    (h₀ • projectiveHyperplaneCartier e g hg hggen) (π z)
    (projectiveHyperplaneUnit e g hg hggen k ^ h₀)
    (cartierLocalEquation_pow _ (π z) _
      (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) h₀) _)) = _
  rw [projectiveFormSection_localCoefficient e g hg hggen k k (π z) hzU h₀,
    projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_homogenize]
  exact hP

/-- (20) for the Taylor data of a weight and the hyperplane class of a closed subscheme of
projective space, at a general closed point of the centre over the coordinate chart k with
tangent coordinates coming from the coordinate ratios, given the root bound for the restricted
dimensions at π(η). The cube is supplied in degree d + 1, the number of tangent coordinates. -/
theorem projectiveHyperplane_sncWeight_partition_bound
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)}) {r d : ℕ}
    (ξ : Fin r → X) (c : EtaleChart K X n) (σc : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (hzU : π z ∈ projectivePullbackCoordinateOpen e k.val)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (hiff : ∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0)
    (Tan : Finset (Fin n)) (hTan : Tan.card = d + 1) (hTanfree : ∀ b ∈ Tan, ∀ k, σc k ≠ some b)
    (hTanU : ∀ b ∈ Tan, ∃ g' ∈ Set.range (fun j : {j : Fin N // j ≠ k.val} =>
        projectivePullbackAffinePolynomialMap e k.val (MvPolynomial.X j)), ∃ κ : K,
      etaleChartStalkCoords c z hz (MvPolynomial.X b) =
        π.stalkMap z (Y.presheaf.germ (projectivePullbackCoordinateOpen e k.val) (π z) hzU
          (g' - algebraMap K Γ(Y, projectivePullbackCoordinateOpen e k.val) κ)))
    (hsat : ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ Tan →
      etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk η))
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    (m₀ : MonomialOrder (Fin n)) (v : Fin n → ℕ) (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * cartierRestrictedDim K
        (q • projectiveHyperplaneCartier e g hg hggen) (π η) : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (l M : ℕ) (hl : 0 < l) (hM : l * (H + (d + 1) + s ^ (d + 1)) ≤ M) (θ : ℝ)
    (hQM : 0 < ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierGradedPullbackTaylor π (projectiveHyperplaneCartier e g hg hggen)
          z (projectiveHyperplaneUnit e g hg hggen k)
          (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez M)),
      Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range l,
      (((s : ℝ) * (auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l : ℕ) -
        ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * (d + 1 : ℕ))) / M) *
          ((∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
              (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
              (LinearMap.range (cartierGradedPullbackTaylor π
                (projectiveHyperplaneCartier e g hg hggen) z
                (projectiveHyperplaneUnit e g hg hggen k)
                (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez
                (auxiliaryDegree M i l))),
            Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) /
            ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
              (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
              (LinearMap.range (cartierGradedPullbackTaylor π
                (projectiveHyperplaneCartier e g hg hggen) z
                (projectiveHyperplaneUnit e g hg hggen k)
                (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez M)),
            Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ))) ≤
      (∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierGradedPullbackTaylor π
            (projectiveHyperplaneCartier e g hg hggen) z
            (projectiveHyperplaneUnit e g hg hggen k)
            (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez M)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ) *
          ∑ i ∈ Tan, (p i : ℝ)) /
          ((M : ℝ) * ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
            (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
            (LinearMap.range (cartierGradedPullbackTaylor π
              (projectiveHyperplaneCartier e g hg hggen) z
              (projectiveHyperplaneUnit e g hg hggen k)
              (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez M)),
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) +
        (d + 1 : ℝ) / M :=
  sncWeight_partition_bound π ξ c σc hc w hw0 η hη hwη hmax z hz hηz ez hez hiff Tan hTan
    hTanfree hsat (projectiveHyperplaneCartier e g hg hggen)
    (projectiveHyperplaneUnit e g hg hggen k)
    (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) m₀ v (d + 1)
    (fun s' hs' => by
      obtain ⟨x, hx⟩ := projectiveHyperplane_exists_section_taylor_eq_tangent_monomial π e g hg
        hggen he k z hzU c hz ez hez Tan hTanU s' hs' (d + 1) (by rw [hTan])
      exact ⟨x, 1, by rw [map_one]; exact one_ne_zero, by rw [hx, one_mul]⟩)
    s H hroot hH l M hl hM θ hQM

end MixedFujita
