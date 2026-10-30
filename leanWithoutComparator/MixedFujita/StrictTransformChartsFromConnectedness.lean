/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NondegenerateFunctionSNCModel

/-!
The remaining connectedness input and the complete strict-transform chart assembly.

Connectedness below is a statement about the actual non-klt components over a closed point of
the original hyperplane on a proper projective SNC principalizing model. It asks for no chart,
Jacobian factorization, quotient point, coefficient data or freeness conclusion. Assuming this
input, the original NondegenerateStrictTransformChartStatement follows for every finite family,
including zero generators. Together with sum KV it gives the existing original F1 statement.
The connectedness statement itself, its derivation from relative vanishing, and KV remain open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- The non-klt union over the specified hyperplane point is preconnected on the actual
principalizing model. All divisors in the coefficient inequality are the actual geometric ones. -/
def StrictTransformConnectednessStatement (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra K A] [IsNoetherianRing A] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    {J : Type} [Finite J] (g : J → A), (∃ j, g j ∉ Ideal.span {φ (MvPolynomial.X 0)}) →
    ∀ (χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K) (M : ℕ), 1 ≤ N → 1 ≤ M →
    ∀ (T : Scheme.{u}) [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] [IsNoetherian T]
      [SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K))]
      (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
      [IsProper ρ] [IsProjective ρ]
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T (N + 1)) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K (N + 1) ξ →
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (z : T) = 0) →
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (z : T) = 0) →
      ∀ (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Gc (z : T) = 0) →
      effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
        effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2)) (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ →
      _root_.IsPreconnected (⋃ s ∈ {s : Fin r | (M : ℤ) ≤ (M : ℤ) *
        (cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (ξ s) +
          cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
            (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
            cT etaleCharts_cover) (ξ s)) + cartierCoefficient Gc (ξ s)},
        closure ({ξ s} : Set T) ∩ ρ ⁻¹' Set.singleton (specAlgHomPoint
          (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})))))

set_option maxHeartbeats 1600000 in
/-- Complete the original nondegenerate chart statement from the geometric connectedness input.
All chart, coefficient, quotient, Jacobian and generator witnesses are constructed internally. -/
theorem nondegenerateStrictTransformChartStatement_of_connectedness
    {K : Type u} [Field K] [CharZero K] (hconn : StrictTransformConnectednessStatement K) :
    NondegenerateStrictTransformChartStatement K := by
  classical
  intro A _ _ _ N _ cX φ hφ _ J _ g M hN hM χ hnd hbad
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := n + 1 + 1)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : (Ideal.span {φ (MvPolynomial.X 0)}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, Gc, hGc,
      hinj, hcoh, hsnc, hcrep, hH, hgsupp, hGc0, hGcI, hmin,
      ⟨s₀, himage, -, hh₀, hk₀, ha₀⟩, hbadmem⟩ :=
    exists_nondegenerate_function_snc_model cX φ hφ g hnd
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + 2) _
  let H := cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
    (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))
  let Bc := crepantBoundaryCartier ρ hρ cX 1 1
    (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) cT etaleCharts_cover
  let x := specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})))
  obtain ⟨s₁, hs₁, hx₁⟩ := hbadmem x M hM hbad
  have hHsrc : (principalCartierDivisor (Spec (CommRingCat.of A))
      (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0)).IsEffective :=
    (CartierDivisor.isEffective_principalCartierDivisor_iff _).mpr
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv (φ (MvPolynomial.X 0)), rfl⟩
  have hHnonneg (s : Fin r) : 0 ≤ cartierCoefficient H (ξ s) :=
    cartierCoefficient_nonneg_of_isEffective H (cartierPullback_isEffective ρ _ hHsrc) _
  have hk_nonneg (s : Fin r) : 0 ≤ -cartierCoefficient Bc (ξ s) :=
    neg_nonneg.mpr (crepantBoundaryCartier_coefficient_nonpos ρ hρ cX cT _)
  have hconnected := hconn A (n + 1) cX φ hφ g hnd χ M hN hM T ρ hρ cT r ξ
    hinj hcoh hsnc hcrep hH Gc hGc hGc0 hGcI
  obtain ⟨j, t, c, σ, hj, hineq, ht₀, htj, htx, ht, hc, hσ₀, hσj, hμ, hbir,
      het, hfe, hprime, w, hw, hker, P, hP, hPx, hl, hmem⟩ :=
    exists_connected_strictTransform_quotient_chart ρ hρ φ χ ξ hsnc M (by exact_mod_cast (Nat.zero_lt_of_lt hM))
      (fun s => cartierCoefficient H (ξ s)) (fun s => -cartierCoefficient Bc (ξ s))
      (fun s => cartierCoefficient Gc (ξ s))
      (by simpa only [sub_neg_eq_add] using hconnected) s₀ s₁ hh₀ (neg_eq_zero.mpr hk₀) ha₀
      (hHnonneg s₁) (hk_nonneg s₁) (by simpa only [sub_eq_add_neg] using hs₁) himage hx₁
  let Rρ := birationalRelativeCanonicalDivisor (n + 2) ρ hρ cX etaleCharts_cover cT etaleCharts_cover
  have hR : Rρ = -Bc := by
    dsimp only [Bc]
    rw [crepantBoundaryCartier_eq_neg_discrepancy, neg_neg, logDiscrepancyDivisor_boundary_zero,
      one_nsmul]
  have hRcoeff (z : T) : cartierCoefficient Rρ z = -cartierCoefficient Bc z := by
    rw [hR, cartierCoefficient_neg]
  have hR0 : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Rρ (z : T) = 0 := by
    intro z hz
    rw [hRcoeff, hcrep z hz, neg_zero]
  obtain ⟨κ, J₁, J₂, hJ₁, hJ₂, hJac, hκ⟩ := exists_modelChart_jacobian_quotient_monomial ρ hρ
    cX cT φ hφ c ξ hinj hcoh σ hc hR0 s₀ hσ₀ (by rw [hRcoeff, hk₀, neg_zero]) t ht P (hmem ht)
  obtain ⟨η, W₁, W₂, hW₁, hW₂, hwfac, hη⟩ := exists_modelChart_factor_quotient_monomial ρ
    (φ (MvPolynomial.X 0)) (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0) rfl
    c ξ hinj hcoh σ hc hH s₀ hσ₀ hh₀ t ht w hw P (hmem ht)
  have : (Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime := hprime
  let B := Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}
  have : IsDomain B := inferInstance
  let a := (cartierCoefficient Gc (ξ j)).toNat
  have ha : (a : ℤ) = cartierCoefficient Gc (ξ j) :=
    Int.toNat_of_nonneg (cartierCoefficient_nonneg_of_isEffective Gc hGc _)
  have hg : ∀ k, ∃ q V : B, V ∉ P ∧
      Ideal.Quotient.mk _ (modelChartAlgHom (K := K) ρ c.U (g k)) * V =
        hyperplaneCoords c.coords (MvPolynomial.X (0 : Fin (n + 1))) ^ a * q := by
    intro k
    by_cases hgk : g k = 0
    · exact ⟨0, 1, hP.one_notMem, by simp only [hgk, map_zero, zero_mul, mul_zero]⟩
    · exact exists_modelChart_generator_quotient_factor ρ (g k) (specFunctionRationalUnit (g k) hgk)
        rfl c ξ hinj hcoh σ hc (hgsupp ⟨k, hgk⟩) j 0 hσj a
        (ha.le.trans ((hmin (ξ j)).1 ⟨k, hgk⟩)) t ht P (hmem ht)
  have hπ : ∀ b : B, ∃ c' d : Γ(T, c.U), Ideal.Quotient.mk _ d ≠ (0 : B) ∧
      Ideal.Quotient.mk _ d * b = Ideal.Quotient.mk _ c' := by
    intro b
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨c', 1, by simp, by simp⟩
  refine ⟨Γ(T, c.U), inferInstance, inferInstance, inferInstance, c.coords, c.formallyEtale,
    modelChartAlgHom (K := K) ρ c.U, hμ, hbir, w, hw, B, inferInstance, inferInstance, inferInstance,
    AlgHom.id K B, het, hfe, hker, hπ, P, hP, hPx, 0, hl, κ, η, J₁, J₂, W₁, W₂,
    hJ₁, hJ₂, hW₁, hW₂, hJac, hwfac, a, hg, ?_⟩
  rw [hκ j 0 hσj, hη j 0 hσj, ha, hRcoeff]
  simpa only [H, add_sub_assoc] using hineq

/-- The original F1 statement now follows from sum KV and the explicit geometric connectedness
input. Neither vanishing nor connectedness is asserted by this conditional theorem. -/
theorem mixedFujitaFreeness_of_kvSum_of_strictTransformConnectedness
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hconn : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      StrictTransformConnectednessStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_nondegenerateCharts hKV
    (fun K _ _ _ => nondegenerateStrictTransformChartStatement_of_connectedness (hconn K))

end MixedFujita
