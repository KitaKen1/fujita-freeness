/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformChartReduction

/-!
Two inputs of strict transform charts (step 9).

For a dominant morphism ρ : T → Spec A of integral schemes inducing an isomorphism of function
fields and a nonempty open U of T, the map A → Γ(T, U) is injective and every function on U is a
quotient μ(r)/μ(s) with s ≠ 0 (`appLE_top_injective_birational`): in the function field of T the
function is the image of a fraction of A, as A is a domain with fraction field the function field
of Spec A, and germs on U are injective. This is the injectivity and birationality of the chart
ring C = Γ(T, U) over A in the strict transform charts of check-332, for a chart U of a
principalized model T → Spec A.

A bad point y of nonzero functions u_k on a smooth Y gives a bad member of the simple normal
crossing family of any proper principalizing model T of the divisors of the u_k
(`exists_bad_snc_member_of_modelThresholdBadAt`): the minimum formula. For a bad test prime e the
orders o_s of the members along e satisfy Σ_s (1 − b_s) o_s ≤ A(e) and Σ_s G_s o_s = ord_e(u_k)
for some k, with G the principalized divisor and b the crepant boundary, so some member with
o_s > 0 has M (1 − b_s) ≤ G_s, and its image contains the centre of e. This is the bad component
on the principalized model from which the connectedness lemma starts.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Birational

variable {A : Type u} [CommRing A] [IsDomain A] {T : Scheme.{u}} [IsIntegral T]

/-- The functions on a nonempty open of a birational model of Spec A are fractions of A. -/
theorem appLE_top_injective_birational (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom) (U : T.Opens) [Nonempty U] :
    Function.Injective
        (fun a : A => ρ.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) ∧
      ∀ c : Γ(T, U), ∃ r s : A, s ≠ 0 ∧
        ρ.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) * c =
          ρ.appLE ⊤ U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r) := by
  have key : ∀ a : Γ(Spec (CommRingCat.of A), ⊤),
      T.germToFunctionField U (ρ.appLE ⊤ U le_top a) =
        (dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤ a) :=
    fun a => (dominantFunctionFieldMap_germ ρ ⊤ U le_top a).symm
  refine ⟨fun a b h => ?_, fun c => ?_⟩
  · have h' := congrArg (T.germToFunctionField U) h
    simp only at h'
    rw [key, key] at h'
    have h2 := (dominantFunctionFieldMap ρ).hom.injective h'
    have h3 := Scheme.germToFunctionField_injective (Spec (CommRingCat.of A)) ⊤ h2
    have h4 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom h3
    rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h4
  · have : IsFractionRing Γ(Spec (CommRingCat.of A), ⊤) (Spec (CommRingCat.of A)).functionField :=
      functionField_isFractionRing_of_isAffineOpen _ ⊤ (isAffineOpen_top _)
    obtain ⟨q, hq⟩ := hρ.2 (T.germToFunctionField U c)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Spec (CommRingCat.of A), ⊤)) q
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hgb : (Spec (CommRingCat.of A)).germToFunctionField ⊤ b ≠ 0 := fun h0 =>
      hb0 (Scheme.germToFunctionField_injective _ ⊤ (h0.trans (map_zero _).symm))
    have hdb : (dominantFunctionFieldMap ρ).hom
        ((Spec (CommRingCat.of A)).germToFunctionField ⊤ b) ≠ 0 := (map_ne_zero _).mpr hgb
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom a, (Scheme.ΓSpecIso (CommRingCat.of A)).hom b,
      ?_, ?_⟩
    · intro h0
      apply hb0
      have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv h0
      rwa [Iso.hom_inv_id_apply, map_zero] at h1
    · apply Scheme.germToFunctionField_injective T U
      rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply, map_mul, key, key]
      rw [← hq, map_div₀]
      change (dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤ b) *
        ((dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤ a) /
          (dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤ b)) = _
      field_simp

end Birational


section BadMember

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The minimum formula: a bad point of nonzero functions gives a bad member of the simple normal
crossing family of a proper principalizing model, whose image contains the point. -/
theorem exists_bad_snc_member_of_modelThresholdBadAt (cY : EtaleChart K Y n) {J : Type}
    [Finite J] (u : J → Y.functionFieldˣ)
    (hA : ∀ k, (principalCartierDivisor Y (u k)).IsEffective) (M : ℕ) (hM : 1 ≤ M)
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ Y) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hcoh : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
        etaleCharts_cover) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hGc0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient Gc (t : T) = 0)
    (hGcI : effectiveCartierIdealSheaf Gc hGc =
      (⨆ k, effectiveCartierIdealSheaf (principalCartierDivisor Y (u k)) (hA k)).comap ρ)
    (y : Y)
    (hbad : ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
      (fun k => (u k : Y.functionField)) M) :
    ∃ s, (M : ℤ) * (1 - cartierCoefficient (crepantBoundaryCartier ρ hρ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
        etaleCharts_cover) (ξ s)) ≤ cartierCoefficient Gc (ξ s) ∧
      y ∈ ρ '' closure ({ξ s} : Set T) := by
  classical
  set D₀ : CartierDivisor Y :=
    1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)) with hD₀
  set crep : Fin r → ℤ := fun s =>
    cartierCoefficient (crepantBoundaryCartier ρ hρ cY (1 : Y.functionFieldˣ) 1 D₀ cT
      etaleCharts_cover) (ξ s) with hcrep
  set G : Fin r → ℤ := fun s => cartierCoefficient Gc (ξ s) with hG
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hApos, hineq⟩ := hbad
  obtain ⟨o, t₀, ht₀, ho, hosupp, -, ⟨-, j₀, hj₀⟩, hdisc⟩ :=
    exists_snc_orders_at_test_prime ρ hρ cY (1 : Y.functionFieldˣ) 1 D₀ cT ξ hinj hcoh hsnc hsupp
      (fun k => principalCartierDivisor Y (u k)) hA Gc hGc hGc0 hGcI σ hσ cU e
  set logY : ℤ := cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1
    D₀ cU etaleCharts_cover) (e : U) with hlogY
  have hord : ∀ k, cartierCoefficient (cartierPullback σ (principalCartierDivisor Y (u k)))
      (e : U) = U.ord ((dominantFunctionFieldMap σ).hom (u k : Y.functionField)) (e : U) := by
    intro k
    rw [cartierPullback_principal, cartierCoefficient_principal]
    rfl
  have hb := hineq j₀ (Units.ne_zero (u j₀))
  rw [← hord j₀, ← hj₀, Nat.cast_one, div_one] at hb
  rw [Nat.cast_one, div_one] at hApos
  have hbZ : (M : ℤ) * (1 + logY) ≤ ∑ s, G s * o s := by exact_mod_cast hb
  have hAZ : 0 < 1 + logY := by exact_mod_cast hApos
  have hdisc' : (1 : ℤ) * ∑ s, o s - ∑ s, crep s * o s ≤ 1 + logY := by exact_mod_cast hdisc
  have hsum : (M : ℤ) * ∑ s, (1 + -crep s) * o s ≤ ∑ s, G s * o s := by
    have h1 : ∑ s, (1 + -crep s) * o s = (1 : ℤ) * ∑ s, o s - ∑ s, crep s * o s := by
      rw [one_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [h1]
    have hM0 : (0 : ℤ) ≤ M := by positivity
    exact (mul_le_mul_of_nonneg_left hdisc' hM0).trans hbZ
  have hpos : 0 < ∑ s, G s * o s := by
    have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    nlinarith
  obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge ho hsum hpos
  refine ⟨s, by linarith [hs], ?_⟩
  rw [← ht₀] at hye
  exact closure_minimal
    (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem ρ (hosupp s hos.ne')))
    ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure) hye

end BadMember

end MixedFujita
