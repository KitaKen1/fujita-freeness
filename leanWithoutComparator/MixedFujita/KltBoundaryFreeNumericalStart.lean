/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorInteriorLowerGrowth
public import MixedFujita.KltInteriorSpecialization
public import MixedFujita.KltModelCoefficientBound
public import MixedFujita.CartierGradedTaylor

/-!
The numerical ordinary-point start on a boundary-free chart of a projective klt source.
Lemma 1 and the extracted ordinary prime give mult_x(s) <= C j n, uniformly in the point.
An eventual strict dimension lower bound gives (7) by the adapted Taylor basis and lattice
average, without assuming a Hilbert limit for the ample divisor or source smoothness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 1 bounds ordinary multiplicities on the boundary-free chart locus. -/
theorem klt_boundaryFree_vanishingOrder_le (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ L : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : Y), x ∈ cY.U →
      ∀ _β : Y.presheaf.stalk x →ₐ[K] K, D₀.IsLocalEquationAt x (fY ^ d) →
      ∀ (j : ℕ), 1 ≤ j → ∀ (s : Γ((j • L).sheaf, ⊤)), s ≠ 0 →
        ((cartierSectionVanishingOrder (j • L) x s).toNat : ℝ) ≤ (C : ℝ) * j * n := by
  obtain ⟨C, hC, hc⟩ := klt_model_coefficient_le hn cY fY d hd D₀ L hklt hH
  refine ⟨C, hC, ?_⟩
  intro x hx β hD j hj s hs
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hecU, hσe, hJ⟩ :=
    exists_extraction_prime_at_chart_rational_point hn cY x hx β
  have hA := logDiscrepancyDivisor_coefficient_of_local_boundary_zero σ hσ cY fY d D₀
    cU e hecU (by simpa only [hσe] using hD)
  rw [hJ] at hA
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hAnorm : ((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier σ hσ cY fY d D₀ cU etaleCharts_cover) e) / d = n := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hA]
    push_cast
    field_simp
    ring
  have hsm : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint U)
  have hv := cartierPullback_sectionZeroDivisor_coefficient_ge_vanishingOrder σ (j • L) s hs
    (⟨e, he⟩ : CodimensionOnePoint U)
  change ((cartierSectionVanishingOrder (j • L) (σ e) s).toNat : ℤ) ≤
    cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • L) s hs)) e at hv
  rw [hσe] at hv
  have hv' : ((cartierSectionVanishingOrder (j • L) x s).toNat : ℝ) ≤
      (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • L) s hs)) e : ℝ) := by
    exact_mod_cast hv
  have hbound := (hc U σ hσ cU ⟨e, he⟩ j hj s hs).2
  rw [hAnorm] at hbound
  exact hv'.trans hbound

/-- The ordinary-point inequality (7), with one positive scale and gap for all large degrees and
all t in a fixed interval, from only a strict dimension lower bound. -/
theorem klt_boundaryFree_interior_start_of_dimension_lower (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤
      (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ))
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹)
    (x : Y) (hxcl : IsClosed ({x} : Set Y)) (hx : x ∈ cY.U)
    (hD : D₀.IsLocalEquationAt x (fY ^ d)) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      ∀ t, t₀ ≤ t → t ≤ b →
        ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
          minimizationFunctional j t (ζ * n)
            (fun i => ζ * ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) ≤ 1 - δ := by
  have hfin : ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) :=
    cartierIsAmpleProj_finiteDimensional_nsmul (etaleChart_topologicalKrullDim cY) hn hA
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) cY.isAffine x hx hxcl
  obtain ⟨coords, -, -⟩ := etaleChart_exists_taylorCoordinates cY x hx β
  obtain ⟨f, hf⟩ := A.exists_isLocalEquationAt x
  obtain ⟨C, -, hC⟩ := klt_boundaryFree_vanishingOrder_le hn cY fY d hd D₀ A hklt hA
  let T := cartierGradedTaylor A x f hf coords
  have hTinj : ∀ j, Function.Injective (T j) :=
    fun j => cartierGradedTaylor_injective A x f hf coords j
  have heq : ∀ j s, (T j s).order = cartierSectionVanishingOrder (j • A) x s := by
    intro j s
    exact cartierTaylorCoordinates_order_eq_vanishingOrder (j • A) x (f ^ j)
      (cartierLocalEquation_pow A x f hf j) coords s
  have hord : ∀ᶠ j : ℕ in atTop, ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
      realWeightedOrder (fun _ : Fin n => (1 : ℝ)) (T j s) ≤ ((C : ℝ) * n) * j := by
    filter_upwards [eventually_ge_atTop 1] with j hj s hs
    have hT0 : T j s ≠ 0 := fun h => hs (hTinj j (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin n => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    change ((T j s).order.toNat : ℝ) ≤ _
    rw [heq]
    calc ((cartierSectionVanishingOrder (j • A) x s).toNat : ℝ) ≤ (C : ℝ) * j * n :=
        hC x hx β hD j hj s hs
      _ = _ := by ring
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ :=
    taylor_interior_start_of_dimension_lower (show 0 < n from hn) T hTinj hc hb
      (by positivity : (0 : ℝ) ≤ (C : ℝ) * n) hN hord hvol
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hev] with j hj t ht₀t htb
  obtain ⟨B, hB⟩ := hj t ht₀t htb
  refine ⟨B, ?_⟩
  have hvals : (fun i => ζ * realWeightedOrder (fun _ : Fin n => (1 : ℝ)) (T j (B i))) =
      (fun i => ζ * ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) := by
    funext i
    have hT0 : T j (B i) ≠ 0 := fun h => B.ne_zero i (hTinj j (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin n => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    change ζ * ((T j (B i)).order.toNat : ℝ) = _
    rw [heq]
  rwa [hvals] at hB

end MixedFujita
