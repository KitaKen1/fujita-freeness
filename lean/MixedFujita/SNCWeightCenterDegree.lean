/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightPartitionBoundDegree
public import MixedFujita.SNCWeightInfimum

/-!
The inequalities of one degree of section 5.3 for a minimizing weight (the input of the limit
`exists_parameter_point_centers`).

Let Y be a closed subscheme of projective space with hyperplane divisor J, x a point of Y and w a
weight on a proper simple normal crossing model whose objective for a basis of the sections of
m J is at most the infimum at x (minimality) and at most the infimum at π(z) (the specialization
comparison (6)), where z is a general closed point of the centre with tangent coordinates T from
the coordinate ratios (d + 1 of them) and the degree of the image W of the centre is at least
s^(dim W). With

* N_j the dimension of the sections of j J and f_j the infimum at x of degree j divided by N_j,
* Q_j the sum of exp(-ℓ(p)/m) over the initial exponents of degree j, ℓ the old weight,
* T the tangential moment of degree m, and A the log discrepancy of w,

the inequalities `CenterDegreeInequalities` hold for D = d + 1, λ = s and the constant
C = s (s^(d+1) - 1) + s (d + 1): a ≤ A for any a ≤ A, (16) from the tangential variation, (20)
from the slices, and (21) from testing the scaled weight at the auxiliary degrees.
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

/-- The ratio form of (21): from infj (E1 Qm) ≤ infm (E2 Qj). -/
theorem ratio_bound_of_mul_le {Nj Nm infj infm Qj Qm E1 E2 : ℝ} (hNj : 0 ≤ Nj) (hNm : 0 < Nm)
    (hinfm : 0 ≤ infm) (hQj : 0 ≤ Qj) (hQm : 0 < Qm) (hE1 : 0 < E1) (hE2 : 0 < E2)
    (h : infj * (E1 * Qm) ≤ infm * (E2 * Qj)) :
    (Nj / Nm) * ((infj / Nj) / (infm / Nm)) * (E1 / E2) ≤ Qj / Qm := by
  have hR : 0 ≤ Qj / Qm := div_nonneg hQj hQm.le
  rcases hNj.eq_or_lt with hNj0 | hNjpos
  · rw [← hNj0, zero_div, zero_mul, zero_mul]
    exact hR
  rcases hinfm.eq_or_lt with hinf0 | hinfpos
  · rw [← hinf0, zero_div, div_zero, mul_zero, zero_mul]
    exact hR
  have h1 : (Nj / Nm) * ((infj / Nj) / (infm / Nm)) * (E1 / E2) = infj * E1 / (infm * E2) := by
    field_simp
  rw [h1, div_le_div_iff₀ (mul_pos hinfpos hE2) hQm]
  calc infj * E1 * Qm = infj * (E1 * Qm) := by ring
    _ ≤ infm * (E2 * Qj) := h
    _ = Qj * (infm * E2) := by ring

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X] [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The inequalities of one degree for a minimizing weight at a general closed point of its
centre, for the hyperplane class. -/
theorem projectiveHyperplane_centerDegreeInequalities
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    (k : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)}) {rr dd d : ℕ}
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (hdd : 1 ≤ dd) (D₀ : CartierDivisor Y)
    (cX : EtaleChart K X n) (ξ : Fin rr → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin rr → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin rr → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (x : Y) (hx : π η ⤳ x) (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
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
    (m₀ : MonomialOrder (Fin n)) (s : ℕ) (hs : 1 ≤ s) {D' : ℕ}
    (hD' : topologicalKrullDim (closure ({π η} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι (π η) ≫ e)
      (genericPoint (pointClosureScheme (π η)))).asHomogeneousIdeal)
    (hdeg : ∀ r : ℕ, Filter.Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier (pointClosureι (π η) ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
          (D : ℝ) ^ D') Filter.atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (l m : ℕ) (hl : 0 < l)
    (hM : l * (2 * s ^ D' + 2 ^ D' * D'.factorial + (d + 1) + s ^ (d + 1)) ≤ m)
    (B : Module.Basis (Fin (Module.finrank K
      Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
      Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
        (m • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (t : X) = 0)
    (hNm : 0 < Module.finrank K Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    {t : ℝ} (ht : 0 < t) (a : ℝ)
    (ha : a ≤ ∑ k, w k * (((dd : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k)) / dd))
    (hmin : (∑ i, Real.exp ((∑ k, w k * (((dd : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k)) / dd)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (ξ k) : ℝ)) /
            (m : ℝ))) ≤
      sncWeightInfimum cY fY dd D₀ (m • projectiveHyperplaneCartier e g hg hggen) x
        (Module.finrank K Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t m)
    (hspec : (∑ i, Real.exp ((∑ k, w k * (((dd : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k)) / dd)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (ξ k) : ℝ)) /
            (m : ℝ))) ≤
      sncWeightInfimum cY fY dd D₀ (m • projectiveHyperplaneCartier e g hg hggen) (π z)
        (Module.finrank K Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t m) :
    CenterDegreeInequalities
      (fun j => Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
      (fun j => sncWeightInfimum cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) x
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
          Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
      t s ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * (d + 1 : ℕ)) a l m (d + 1)
      (fun j => ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) (fun i => if i ∈ Tan then 1 else 0)
          (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (j • projectiveHyperplaneCartier e g hg hggen) π z ez)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m))
      (sectionExponentialMoment (initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) (fun i => if i ∈ Tan then 1 else 0)
          (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • projectiveHyperplaneCartier e g hg hggen) π z ez)))
        (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
        (fun p => (natExponentDegree (fun i => if i ∈ Tan then 1 else 0) p : ℝ)) m)
      (∑ k, w k * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k)) / dd)) := by
  -- notation
  obtain ⟨v, hvdef⟩ : ∃ v : Fin n → ℕ, v = fun i => if i ∈ Tan then 1 else 0 := ⟨_, rfl⟩
  rw [← hvdef]
  have hv : ∀ k a, σc k = some a → v a = 0 := by
    intro k' a hka
    rw [hvdef]
    exact ite_eq_right fun ha => hTanfree a ha k' hka
  have hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a := fun k' hk' => (hiff k').mpr hk'
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := lt_of_lt_of_le (Nat.mul_pos hl (by positivity)) hM
    exact_mod_cast this
  have hlm : l ≤ m := le_trans (Nat.le_mul_of_pos_right l (by positivity)) hM
  -- the initial exponents for the chosen equations and for the powers of the chart equation
  have hIMF : ∀ j : ℕ, initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierGradedPullbackTaylor π (projectiveHyperplaneCartier e g hg hggen) z
        (projectiveHyperplaneUnit e g hg hggen k)
        (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez j)) =
      initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (j • projectiveHyperplaneCartier e g hg hggen) π z ez)) := fun j =>
    (initialMonomialFinset_cartierPullbackTaylorLinear_eq_graded π _
      (projectiveHyperplaneCartier e g hg hggen) z _
      (projectiveHyperplane_isLocalEquationAt e g hg hggen k (π z) hzU) ez j).symm
  -- the sum Q_m is positive
  have hcard : (initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (m • projectiveHyperplaneCartier e g hg hggen) π z ez))).card =
      Module.finrank K Γ((m • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    rw [initialMonomialFinset_card,
      LinearMap.finrank_range_of_inj (cartierPullbackTaylorLinear_injective π z ez _)]
  have hQm : 0 < ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
      (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
      (LinearMap.range (cartierPullbackTaylorLinear
        (m • projectiveHyperplaneCartier e g hg hggen) π z ez)),
      Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
    refine Finset.sum_pos (fun p _ => Real.exp_pos _) ?_
    rw [← Finset.card_pos, hcard]
    exact hNm
  -- the tangential degree
  have hnat : ∀ p : Fin n →₀ ℕ, (natExponentDegree v p : ℝ) = ∑ i ∈ Tan, (p i : ℝ) := by
    intro p
    change ((∑ i, v i * p i : ℕ) : ℝ) = _
    rw [hvdef]
    push_cast
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsumv : (∑ a, (v a : ℝ)) = ((d + 1 : ℕ) : ℝ) := by
    rw [hvdef]
    have h1 : (Finset.univ.filter fun i : Fin n => i ∈ Tan) = Tan := by
      ext i
      simp
    push_cast
    rw [Finset.sum_boole, h1, hTan]
    push_cast
    ring
  refine ⟨ha, fun j => Finset.sum_nonneg fun p _ => (Real.exp_pos _).le, hQm, ?_, ?_, ?_⟩
  · -- (16)
    have h16 := sncWeight_tangential_moment_le_of_le_infimum π hπ cY fY dd hdd D₀ cX ξ hinj hξ
      hsnc hBsupp c σc hc z hz ez hez (m • projectiveHyperplaneCartier e g hg hggen) hNm B hGsupp
      w hw0 hwne hwσ v 0 hv (fun _ _ _ => rfl) m₀ ht hmpos hspec
    rw [hsumv] at h16
    exact h16
  · -- (20)
    have h20 := projectiveHyperplane_sncWeight_partition_bound_of_degree π e g hg hggen he k ξ c
      σc hc w hw0 η hη hwη hmax z hz hηz hzU ez hez hiff Tan hTan hTanfree hTanU hsat m₀ v s hs
      hD' hgW hdeg l m hl hM (m : ℝ) (by rw [hIMF]; exact hQm)
    simp only [hIMF] at h20
    have hT : sectionExponentialMoment (initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear
          (m • projectiveHyperplaneCartier e g hg hggen) π z ez)))
        (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
        (fun p => (natExponentDegree v p : ℝ)) m =
      (∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • projectiveHyperplaneCartier e g hg hggen) π z ez)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) *
          ∑ i ∈ Tan, (p i : ℝ)) /
        ((m : ℝ) * ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear
            (m • projectiveHyperplaneCartier e g hg hggen) π z ez)),
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m)) := by
      unfold sectionExponentialMoment sectionExponentialWeightSum
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      show (natExponentDegree v p : ℝ) *
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) = _
      rw [hnat p, mul_comm]
    rw [hT]
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [← hcast] at h20
    exact h20
  · -- (21)
    intro i hi
    rw [Finset.mem_Ico] at hi
    set jj := auxiliaryDegree m i l with hjj
    have hjpos : 0 < jj := by
      rw [hjj, auxiliaryDegree]
      exact Nat.div_pos (le_trans hlm (Nat.le_mul_of_pos_right m hi.1)) hl
    have hjreal : (0 : ℝ) < jj := by exact_mod_cast hjpos
    have h21 := sncWeightInfimum_mul_sum_initialExponents_le π hπ cY fY dd hdd D₀ cX ξ hinj hξ
      hsnc hBsupp c σc hc η hη w hw0 hwne hwη x hx z hz hηz ez hez
      (m • projectiveHyperplaneCartier e g hg hggen) B hGsupp
      (jj • projectiveHyperplaneCartier e g hg hggen) rfl v m₀ (lam := (jj : ℝ) / m) (t := t)
      (j := (m : ℝ)) (t' := t) (j' := (jj : ℝ)) (div_pos hjreal hmpos) hmpos ht hjreal hmin
    -- factor the exponentials
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ k, w k * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k)) / dd) := ⟨_, rfl⟩
    rw [← hA] at h21 ⊢
    have hsum1 : ∀ S : Finset (Fin n →₀ ℕ), (∑ p ∈ S, Real.exp (A / t -
        realExponentWeight (sncChartCoordinateWeights σc w) p / m)) =
        Real.exp (A / t) * ∑ p ∈ S,
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
      intro S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
    have hsum2 : ∀ S : Finset (Fin n →₀ ℕ), (∑ p ∈ S, Real.exp ((jj : ℝ) / m * A / t -
        (jj : ℝ) / m * realExponentWeight (sncChartCoordinateWeights σc w) p / jj)) =
        Real.exp ((jj : ℝ) / m * A / t) * ∑ p ∈ S,
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / m) := by
      intro S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [hsum1, hsum2] at h21
    have hexp : Real.exp ((1 - (jj : ℝ) / m) * A / t) =
        Real.exp (A / t) / Real.exp ((jj : ℝ) / m * A / t) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp]
    refine ratio_bound_of_mul_le (Nat.cast_nonneg _) (by exact_mod_cast hNm)
      (sncWeightInfimum_nonneg _ _ _ _ _ _ _ _ _)
      (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le) hQm (Real.exp_pos _) (Real.exp_pos _) ?_
    exact h21

end MixedFujita
