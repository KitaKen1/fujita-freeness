/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSNCModelOrderBound
public import MixedFujita.PrincipalizedIdealCoefficients
public import MixedFujita.PrincipalizedGlobalGeneration

/-!
A simple normal crossing model principalizing a sum of ideal sheaves of effective Cartier
divisors (step 7). Let X be an integral scheme of finite type and separated over a field of
characteristic zero with a log pair, finitely many Cartier divisors G_j and finitely many
effective Cartier divisors A_k. The model T of the log pair constructed by resolution can be
chosen so that, in addition, the inverse image on T of the sum of the ideal sheaves of the A_k is
the ideal sheaf of an effective Cartier divisor G: all prime components of G, of the pullbacks of
the G_j and of the pullbacks of the A_k belong to the simple normal crossing family, and at every
point the coefficient of G is the minimum of the coefficients of the pullbacks of the A_k. If M
is a Cartier divisor of X such that every M - A_k is globally generated, then ρ*M - G is globally
generated and nef on T.
Finitely many further ideal sheaves of X can be principalized at the same time, so that T
dominates the blow-up of X along each of them; this is how a prescribed exceptional divisor is
kept on the model.

Over an algebraically closed field, and if X carries an ample Cartier divisor, the model moreover
carries a very ample Cartier divisor and has the uniform linear bound for the vanishing orders of
pulled back sections. This is the model on which the divisors computing a minimum are isolated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
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

section CharZero

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

omit [CharZero K] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))] in
/-- The generic point does not lie in the support of a sum of ideal sheaves of effective Cartier
divisors indexed by a nonempty type. -/
theorem genericPoint_notMem_support_iSup_effectiveCartierIdealSheaf {κ : Type*} [Nonempty κ]
    (A : κ → CartierDivisor X) (hA : ∀ k, (A k).IsEffective) :
    genericPoint X ∉ ((⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).support : Set X) := by
  obtain ⟨k₀⟩ := ‹Nonempty κ›
  intro h
  have hle : effectiveCartierIdealSheaf (A k₀) (hA k₀) ≤
      ⨆ k, effectiveCartierIdealSheaf (A k) (hA k) :=
    le_iSup (fun k => effectiveCartierIdealSheaf (A k) (hA k)) k₀
  exact genericPoint_notMem_support_effectiveCartierIdealSheaf (A k₀) (hA k₀)
    (Scheme.IdealSheafData.support_antitone hle h)

/-- A projective simple normal crossing model of a log pair, finitely many Cartier divisors,
finitely many effective Cartier divisors A_k and finitely many ideal sheaves 𝔟_j exists on which
the inverse image of the sum of the ideal sheaves of the A_k is the ideal sheaf of an effective
Cartier divisor. The prime components of this divisor and of the pullbacks of all the given
divisors belong to the simple normal crossing family, and at every point its coefficient is at
most the coefficient of the pullback of each A_k and equal to the coefficient of the pullback of
one of them; for every Cartier divisor M of the source with all M - A_k globally generated, the
difference of the pullback of M and this divisor is globally generated and nef. The inverse image
of each 𝔟_j is invertible and the model dominates the blow-up of the source along 𝔟_j. -/
theorem exists_projective_snc_model_principalizing_sum {ι κ μ : Type*} [Finite ι] [Finite κ]
    [Nonempty κ] [Finite μ] (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor X) (G : ι → CartierDivisor X) (A : κ → CartierDivisor X)
    (hA : ∀ k, (A k).IsEffective) (𝔟 : μ → X.IdealSheafData)
    (h𝔟 : ∀ j, genericPoint X ∉ ((𝔟 j).support : Set X)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      (∀ (k : κ) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (A k)) (t : T) = 0) ∧
      (∀ (N : ℕ) (e : X ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
        e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K) →
        ∃ (M : ℕ) (e' : T ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
          e' ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K)) ∧
      (∀ j : μ, ((𝔟 j).comap ρ).IsInvertible ∧
        (∃ g : T ⟶ (𝔟 j).blowUp, g ≫ (𝔟 j).blowUpπ = ρ) ∧
        ∃ (E : CartierDivisor T) (hE : E.IsEffective),
          effectiveCartierIdealSheaf E hE = (𝔟 j).comap ρ ∧
          ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        (t : T) ∉ ((⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ).support) ∧
      ∃ (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
        effectiveCartierIdealSheaf Gc hGc =
          (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ ∧
        (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
          cartierCoefficient Gc (t : T) = 0) ∧
        (∀ t : T,
          (∀ k, cartierCoefficient Gc t ≤ cartierCoefficient (cartierPullback ρ (A k)) t) ∧
          ∃ k, cartierCoefficient Gc t = cartierCoefficient (cartierPullback ρ (A k)) t) ∧
        ∀ M : CartierDivisor X, (∀ k, CartierIsGloballyGenerated (M - A k)) →
          CartierIsGloballyGenerated (cartierPullback ρ M - Gc) ∧
          CartierIsNef K (cartierPullback ρ M - Gc) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, hemb, hoff, hall⟩ :=
    exists_projective_snc_model_principalizing c f d D (Sum.elim G A)
      (fun o : Option μ => o.elim (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)) 𝔟)
      (fun o => by
        cases o with
        | none => exact genericPoint_notMem_support_iSup_effectiveCartierIdealSheaf A hA
        | some j => exact h𝔟 j)
  obtain ⟨-, -, Gc, hGc, hGcI, hGc0⟩ := hall none
  have hGcI' : effectiveCartierIdealSheaf Gc hGc =
      (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ := hGcI
  refine ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, fun j => hG (Sum.inl j), fun k => hG (Sum.inr k), hemb,
    fun j => hall (some j), hoff none, Gc, hGc, hGcI', hGc0,
    fun t => cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
      ρ A hA Gc hGc hGcI' t,
    fun M hM => ?_⟩
  have hgg : CartierIsGloballyGenerated (cartierPullback ρ M - Gc) :=
    cartierIsGloballyGenerated_cartierPullback_sub_of_principalized ρ M A hA hM Gc hGc hGcI'
  exact ⟨hgg, cartierIsGloballyGenerated_isNef hgg⟩

end CharZero

section AlgClosed

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- On a scheme with an ample Cartier divisor over an algebraically closed field of
characteristic zero, the principalizing simple normal crossing model carries a very ample Cartier
divisor and has a uniform linear bound for the vanishing orders of all pulled back sections of
the multiples of any Cartier divisor of the source. -/
theorem exists_projective_snc_model_principalizing_sum_with_order_bound {ι κ μ : Type*}
    [Finite ι] [Finite κ] [Nonempty κ] [Finite μ] (hn : 1 ≤ n) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (G : ι → CartierDivisor X)
    (A : κ → CartierDivisor X) (hA : ∀ k, (A k).IsEffective) (𝔟 : μ → X.IdealSheafData)
    (h𝔟 : ∀ j, genericPoint X ∉ ((𝔟 j).support : Set X)) {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      (∀ (k : κ) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (A k)) (t : T) = 0) ∧
      (∃ J : CartierDivisor T, CartierIsVeryAmpleProj K J) ∧
      (∀ L : CartierDivisor X, ∃ C : ℕ, ∀ x : T, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
        ∀ s : Γ((j • L).sheaf, ⊤), s ≠ 0 →
          cartierSectionVanishingOrder (cartierPullback ρ (j • L)) x
            (cartierDominantPullbackSection ρ (j • L) s) ≤ ((C * j : ℕ) : ℕ∞)) ∧
      (∀ j : μ, ((𝔟 j).comap ρ).IsInvertible ∧
        ∃ g : T ⟶ (𝔟 j).blowUp, g ≫ (𝔟 j).blowUpπ = ρ) ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        (t : T) ∉ ((⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ).support) ∧
      ∃ (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
        effectiveCartierIdealSheaf Gc hGc =
          (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ ∧
        (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
          cartierCoefficient Gc (t : T) = 0) ∧
        (∀ t : T,
          (∀ k, cartierCoefficient Gc t ≤ cartierCoefficient (cartierPullback ρ (A k)) t) ∧
          ∃ k, cartierCoefficient Gc t = cartierCoefficient (cartierPullback ρ (A k)) t) ∧
        ∀ M : CartierDivisor X, (∀ k, CartierIsGloballyGenerated (M - A k)) →
          CartierIsGloballyGenerated (cartierPullback ρ M - Gc) ∧
          CartierIsNef K (cartierPullback ρ M - Gc) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, hAk, hemb, h𝔟T, hoff, hGc⟩ :=
    exists_projective_snc_model_principalizing_sum c f d D G A hA 𝔟 h𝔟
  obtain ⟨m, -, N, e, he, hbase, -⟩ := hH
  obtain ⟨M, e', he', hbase'⟩ := hemb N e he hbase
  obtain ⟨J, hJ⟩ := exists_cartierIsVeryAmpleProj_of_closedImmersion e' hbase'
  have hsm : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hft : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := inferInstance
  have hdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp, hG,
    hAk, ⟨J, hJ⟩, fun L => pulledSection_vanishingOrder_le_of_ample_model hdim hn
      (cartierIsAmpleProj_of_veryAmple hJ) ρ L, (fun j => ⟨(h𝔟T j).1, (h𝔟T j).2.1⟩), hoff, hGc⟩

end AlgClosed

end MixedFujita
