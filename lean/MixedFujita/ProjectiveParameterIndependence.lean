/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFormOrderBound
public import MixedFujita.LinearSystemRelationBound

/-!
The parameters are algebraically independent on Y. At a closed point the degree-D forms
realize every coefficient-box jet of order D + 1, so dim V_D ≥ (D+1)^d / d^d. A nonzero
homogeneous relation among the parameters modulo the generic point would bound
dim V_D by C (D+1)^(d-1); at D = d^d C the two bounds contradict each other. Closed points
exist because Y is quasi-compact and T0.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section ClosedPoint

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

/-- An actual closed subscheme of projective space over the base field has a closed point. -/
theorem polynomialProjective_closedImmersion_exists_closedPoint
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) :
    ∃ x : Y, IsClosed ({x} : Set Y) := by
  have := polynomialProjectiveToBase_isProper n K
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton
    ⟨genericPoint Y, Set.mem_univ _⟩
  exact ⟨x, hx⟩

end ClosedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Jets at one closed point bound the form-section spaces from below. -/
theorem projectiveFormSectionSpace_finrank_lower
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (x : Y) (hx : IsClosed {x}) (D : ℕ) :
    ((D + 1 : ℕ) : ℝ) ^ d ≤
      (d : ℝ) ^ d * Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let jx : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hJx := projectiveHyperplane_isLocalEquationAt e g hg hggen jx x hk
  let := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨_, _, coords, _, _⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d hn
    (projectiveHyperplaneCartier e g hg hggen) x hx
  let J := projectiveHyperplaneCartier e g hg hggen
  let u := projectiveHyperplaneUnit e g hg hggen jx
  let V := projectiveFormSectionSpace e g hg hggen j₀ he D
  let T : Γ((D • J).sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin d) K :=
    cartierTaylorCoordinates (D • J) x (u ^ D) (cartierLocalEquation_pow J x u hJx D) coords
  let ev : V →ₗ[K] ((Fin d → Fin ((D + 1 - 1) / d + 1)) → K) :=
    (powerSeriesBoxJet d ((D + 1 - 1) / d)).comp (T.domRestrict V)
  have hsurj : Function.Surjective ev := by
    intro v
    have hm : 1 ≤ D + 1 := Nat.le_add_left 1 D
    obtain ⟨yy, hyy⟩ := completionCoordinates_exists_approx coords.toRingEquiv
      (powerSeriesOfBox d ((D + 1 - 1) / d) v) (D + 1)
    obtain ⟨F, hF, hFy⟩ := polynomialProjective_closedImmersion_jet_realized e k x hk hx
      (m := D + 1 - 1) (D := D) (by omega) yy
    refine ⟨⟨projectiveFormSection e g hg hggen j₀ D F hF, ⟨F, hF⟩, rfl⟩, ?_⟩
    change powerSeriesBoxJet d ((D + 1 - 1) / d)
      (T (projectiveFormSection e g hg hggen j₀ D F hF)) = v
    rw [← powerSeriesBoxJet_ofBox d ((D + 1 - 1) / d) v]
    apply powerSeriesBoxJet_eq_of_le_order_sub d (D + 1) hm
    have hT : T (projectiveFormSection e g hg hggen j₀ D F hF) =
        coords (algebraMap (Y.presheaf.stalk x)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x))
          (Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D F hF))) := by
      change cartierTaylorCoordinates (D • J) x (u ^ D)
        (cartierLocalEquation_pow J x u hJx D) coords
          (projectiveFormSection e g hg hggen j₀ D F hF) = _
      rw [cartierTaylorCoordinates_apply,
        projectiveFormSection_localCoefficient e g hg hggen j₀ jx x hk D F hF]
    rw [hT]
    have hmem : Y.presheaf.germ _ x hk (projectivePullbackHomogeneousEquation e k D F hF) - yy ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ (D + 1) := by
      have h' := neg_mem hFy
      rw [neg_sub, Nat.sub_add_cancel hm] at h'
      exact h'
    have h1 := completionCoordinates_order_ge_of_mem_pow coords.toRingEquiv hmem
    rw [map_sub, map_sub] at h1
    have h2 : ((D + 1 : ℕ) : ℕ∞) ≤ (coords.toRingEquiv (algebraMap (Y.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x)) yy) -
          powerSeriesOfBox d ((D + 1 - 1) / d) v).order := by
      rw [← MvPowerSeries.order_neg, neg_sub]
      exact hyy
    have h3 := (le_min h1 h2).trans MvPowerSeries.min_order_le_add
    rw [sub_add_sub_cancel] at h3
    exact h3
  have hrank : Module.finrank K ((Fin d → Fin ((D + 1 - 1) / d + 1)) → K) ≤
      Module.finrank K V := by
    have h := LinearMap.finrank_range_le ev
    rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  have hcard : Module.finrank K ((Fin d → Fin ((D + 1 - 1) / d + 1)) → K) =
      ((D + 1 - 1) / d + 1) ^ d := by
    simp only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin]
  rw [hcard] at hrank
  have hbox := pow_le_pow_mul_boxSide d (D + 1) hd
  have hrank' : ((((D + 1 - 1) / d + 1 : ℕ) : ℝ)) ^ d ≤ Module.finrank K V := by
    exact_mod_cast hrank
  calc ((D + 1 : ℕ) : ℝ) ^ d ≤ (d : ℝ) ^ d * ((((D + 1 - 1) / d + 1 : ℕ) : ℝ)) ^ d := hbox
    _ ≤ (d : ℝ) ^ d * Module.finrank K V :=
        mul_le_mul_of_nonneg_left hrank' (by positivity)

include g hg hggen in
/-- No nonzero homogeneous relation among the parameters holds at the generic point. -/
theorem projective_linearSystem_relation_not_mem
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (y : Fin (d + 1) → MvPolynomial (Fin n) K) (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : Fin n →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration
        ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y (d + 1) t)
    {Φ : MvPolynomial (Fin (d + 1)) K} {δ : ℕ} (hΦ : Φ.IsHomogeneous δ) (hΦ0 : Φ ≠ 0) :
    aeval y Φ ∉ (e (genericPoint Y)).asHomogeneousIdeal := by
  intro hΦP
  obtain ⟨C, hC⟩ := linearSystemQuotientDim_le_of_relation (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal)
    y hy hd hnull hΦ hΦ0 hΦP
  obtain ⟨x, hx⟩ := polynomialProjective_closedImmersion_exists_closedPoint e he
  set D := d ^ d * C
  have hlow := projectiveFormSectionSpace_finrank_lower e g hg hggen he hn hd j₀ x hx D
  have hdim : Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) =
      linearSystemQuotientDim ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y 0 D := by
    rw [projectiveFormSectionSpace_finrank]
    unfold linearSystemQuotientDim
    rw [linearSystemFiltration_zero]
  rw [hdim] at hlow
  have hup := hC D
  have hnat : (D + 1) ^ d ≤ d ^ d * (C * (D + 1) ^ (d - 1)) := by
    have h1 : ((D + 1 : ℕ) : ℝ) ^ d ≤ (d : ℝ) ^ d * ((C * (D + 1) ^ (d - 1) : ℕ) : ℝ) :=
      hlow.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hup) (by positivity))
    exact_mod_cast h1
  have hsplit : (D + 1) ^ d = (D + 1) * (D + 1) ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  rw [hsplit, ← mul_assoc] at hnat
  have hpos : 0 < (D + 1) ^ (d - 1) := pow_pos (Nat.succ_pos D) _
  have h' : D + 1 ≤ D := Nat.le_of_mul_le_mul_right hnat hpos
  omega

end MixedFujita
