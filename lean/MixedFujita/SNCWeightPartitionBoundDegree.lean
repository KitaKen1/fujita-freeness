/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveTangentCube
public import MixedFujita.ProjectiveRestrictedDimGrowth
public import MixedFujita.TangentCoordinateChain
public import MixedFujita.RootBoundExponent

/-!
The inequality (20) of section 5.3 for the Taylor data of a weight and the hyperplane class, with
the degree of the image of the centre as the only numerical hypothesis.

Let W be the closure of π(η), of dimension D', and s ≥ 1 with s^D' at most the degree of W (the
leading coefficient of h^0(W, D J) = r D^D'/D'! + o(D^D')). Then

* the dimensions of the sections of q J restricted to W satisfy the root bound with every exponent
  d + 1 ≤ D' for q ≥ 2 s^D' + 2^D' D'! (Lemma 4 for the restricted sections and the comparison of
  exponents);
* the number of tangent coordinates d + 1 is at most D' (the chain of images), so (20) holds for
  the Taylor data of the weight at the general closed point z, with the threshold
  H = 2 s^D' + 2^D' D'!, which depends only on s and D'.

The degree is expressed through the limit: every natural number r which is the limit of
D'! h^0(W, D J)/D^D' is at least s^D'.
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
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
  [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [CharZero K] in
/-- The root bound for the sections of q J restricted to the closure W of a point, for every
exponent d + 1 at most the dimension D' of W, when s^D' is at most the degree of W. -/
theorem projectiveHyperplane_restricted_root_bound_of_degree
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (x : Y) {D' : ℕ}
    (hD' : topologicalKrullDim (closure ({x} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι x ≫ e) (genericPoint (pointClosureScheme x))).asHomogeneousIdeal)
    [∀ q : ℕ, FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    (s : ℕ) (hs : 1 ≤ s)
    (hdeg : ∀ r : ℕ, Filter.Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier (pointClosureι x ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
          (D : ℝ) ^ D') Filter.atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    {d : ℕ} (hdD' : d + 1 ≤ D') (q : ℕ) (hq : 2 * s ^ D' + 2 ^ D' * D'.factorial ≤ q) :
    (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial *
        cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) x : ℕ) : ℝ) ^
          ((d : ℝ) + 1)⁻¹ := by
  obtain ⟨D'', rfl⟩ : ∃ D'', D' = D'' + 1 := ⟨D' - 1, by omega⟩
  obtain ⟨r, -, -, hlim, hpow⟩ := projectiveHyperplane_cartierRestrictedDim_pow_lower e g hg hggen
    he x hD' hgW
  have hsr : s ^ (D'' + 1) ≤ r := hdeg r hlim
  have hsq : s ^ (D'' + 1) ≤ q + 1 := by omega
  exact root_bound_of_larger_exponent hdD' hs hq (hpow s q hsr hsq)

/-- (20) for the Taylor data of a weight and the hyperplane class, at a general closed point of
the centre with tangent coordinates coming from the coordinate ratios, when s^D' is at most the
degree of the image W of the centre, D' the dimension of W. -/
theorem projectiveHyperplane_sncWeight_partition_bound_of_degree
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
    (m₀ : MonomialOrder (Fin n)) (v : Fin n → ℕ) (s : ℕ) (hs : 1 ≤ s) {D' : ℕ}
    (hD' : topologicalKrullDim (closure ({π η} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι (π η) ≫ e)
      (genericPoint (pointClosureScheme (π η)))).asHomogeneousIdeal)
    (hdeg : ∀ r : ℕ, Filter.Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier (pointClosureι (π η) ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
          (D : ℝ) ^ D') Filter.atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (l M : ℕ) (hl : 0 < l) (hM : l * (2 * s ^ D' + 2 ^ D' * D'.factorial + (d + 1) + s ^ (d + 1)) ≤ M) (θ : ℝ)
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
  by
  -- the number of tangent coordinates is at most the dimension of the image of the centre
  have hchain := tangent_card_le_topologicalKrullDim π ξ c σc hc w η hη hwη hmax z hz hηz ez hez
    Tan (fun b hb h => by
      obtain ⟨k', -, hk'⟩ := h
      exact hTanfree b hb k' hk') (projectivePullbackCoordinateOpen e k.val) hzU
    (fun b hb => by
      obtain ⟨g', -, κ, hgκ⟩ := hTanU b hb
      exact ⟨_, hgκ⟩)
  rw [hD', hTan] at hchain
  have hdD' : d + 1 ≤ D' := by exact_mod_cast hchain
  have hroot : ∀ q ≥ 2 * s ^ D' + 2 ^ D' * D'.factorial,
      (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
        (((d + 1).factorial * cartierRestrictedDim K
          (q • projectiveHyperplaneCartier e g hg hggen) (π η) : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹ :=
    fun q hq => projectiveHyperplane_restricted_root_bound_of_degree e g hg hggen he (π η) hD' hgW
      s hs hdeg hdD' q hq
  have hH : 0 < (s : ℝ) * ((2 * s ^ D' + 2 ^ D' * D'.factorial : ℕ) : ℝ) -
      (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) := by
    have h1 : s ^ (d + 1) ≤ 2 * s ^ D' + 2 ^ D' * D'.factorial := by
      have h2 : s ^ (d + 1) ≤ s ^ D' := Nat.pow_le_pow_right hs hdD'
      omega
    have h3 : ((s ^ (d + 1) : ℕ) : ℝ) ≤ ((2 * s ^ D' + 2 ^ D' * D'.factorial : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h4 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    rw [Nat.cast_pow] at h3
    nlinarith
  exact projectiveHyperplane_sncWeight_partition_bound π e g hg hggen he k ξ c σc hc w hw0 η hη
    hwη hmax z hz hηz hzU ez hez hiff Tan hTan hTanfree hTanU hsat m₀ v s
    (2 * s ^ D' + 2 ^ D' * D'.factorial) hroot hH l M hl hM θ hQM

end MixedFujita
