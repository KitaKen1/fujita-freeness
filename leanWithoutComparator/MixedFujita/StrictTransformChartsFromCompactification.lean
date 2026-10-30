/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompactifiedModelVanishing
public import MixedFujita.StrictTransformChartsFromConnectedness
public import MixedFujita.StrictTransformConnectednessFromVanishing

/-!
The strict-transform charts, and F1, from Kawamata–Viehweg vanishing and SNC compactifications of
the principalizing models (step 9).

`HasSNCCompactification K n T G_c` says that `T` is the complement of an effective nef and big divisor
`D̄` in a smooth projective `T̄`, and that `G_c` is the restriction of an effective divisor `Ḡ` supported
on an SNC family with `c D̄ - Ḡ` nef. On such a model, the roundup H¹ vanishing of the connectedness
argument holds by Kawamata–Viehweg vanishing on the projective `T̄` (check-388; only the projective
form `KawamataViehwegVanishingSNCProjective` is needed, check-394). The proof of check-349 then gives
the connectedness of the non-klt components over a hyperplane point
(`compactifiableStrictTransformConnectedness_of_kvSum`). The chart assembly of check-347 gives the
original `NondegenerateStrictTransformChartStatement`
(`nondegenerateStrictTransformChartStatement_of_kvSum_of_compactifiedModels`) once the principalizing
SNC models of `exists_nondegenerate_function_snc_model` can be chosen with SNC compactifications
(`CompactifiedStrictTransformModelStatement`). Hence F1 follows from sum KV and the existence of
such models (`mixedFujitaFreeness_of_kvSum_of_compactifiedModels`). The existence of compactified
models is a purely geometric statement: a projective closure, Hironaka's resolution and
principalization. The model morphisms are only required to be proper: projectivity over `Spec A`
is not used by these arguments (it was removed from both statements in check-393, where the
compactified models are constructed as open parts of models of the projective closure).
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

/-- `T` is the complement of an effective nef and big divisor in a smooth projective variety, and
`G_c` is the restriction of an effective divisor supported on an SNC family with `c D̄ - Ḡ` nef. -/
def HasSNCCompactification (K : Type u) [Field K] (n : ℕ) (T : Scheme.{u}) [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))] (Gc : CartierDivisor T) : Prop :=
  ∃ (Tb : Scheme.{u}) (_ : IsIntegral Tb) (_ : IsNoetherian Tb)
    (_ : Tb.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K)))
    (_ : IsProper (Tb ↘ Spec (CommRingCat.of K)))
    (_ : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Tb)))
    (_ : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H)
    (r : ℕ) (ξ : Fin r → Tb) (Gb Db : CartierDivisor Tb) (c : ℕ)
    (ι : T ⟶ Tb) (_ : IsOpenImmersion ι) (_ : IsDominant ι)
    (_ : ι.IsOver (Spec (CommRingCat.of K))),
    Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
    (∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ → cartierCoefficient Gb (t : Tb) = 0) ∧
    Db.IsEffective ∧ CartierIsNef K Db ∧ CartierIsBig K Db ∧ CartierIsNef K (c • Db - Gb) ∧
    Function.Bijective (dominantFunctionFieldAlgHom (K := K) ι) ∧
    (∀ x : Tb, x ∈ ι.opensRange ↔ Db.IsLocalEquationAt x 1) ∧ cartierPullback ι Gb = Gc

/-- The connectedness statement of check-347 for principalizing models with an SNC
compactification. -/
def CompactifiableStrictTransformConnectednessStatement (K : Type u) [Field K] : Prop :=
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
      [IsProper ρ]
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
      HasSNCCompactification K (N + 1) T Gc →
      _root_.IsPreconnected (⋃ s ∈ {s : Fin r | (M : ℤ) ≤ (M : ℤ) *
        (cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (ξ s) +
          cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
            (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
            cT etaleCharts_cover) (ξ s)) + cartierCoefficient Gc (ξ s)},
        closure ({ξ s} : Set T) ∩ ρ ⁻¹' Set.singleton (specAlgHomPoint
          (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})))))

set_option maxHeartbeats 1600000 in
/-- On principalizing models with an SNC compactification, Kawamata–Viehweg vanishing on the
compactification gives the connectedness of the non-klt components over a hyperplane point. -/
theorem compactifiableStrictTransformConnectedness_of_kvSum {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (hKV : ∀ n, KawamataViehwegVanishingSNCProjective K n) :
    CompactifiableStrictTransformConnectednessStatement K := by
  intro A _ _ _ _ N _ cX φ hφ _ J _ g _hnd χ M _hN hM T _ _ _ _
    ρ _ _ _ hρ cT r ξ hinj hξ hsnc hcrep hH G hG hGsupport hI hcomp
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (N + 1) _
  let H := cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
    (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))
  let B := strictTransformConnectednessBoundary ρ hρ cX cT H G M
  have hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0 :=
    strictTransformConnectednessBoundary_supported ρ hρ cX cT H G M ξ hH hcrep hGsupport
  obtain ⟨_hgen, _hGnef, hnef, E, S, hE, hS, hround, hSc, hdisj, _hexc, hunit⟩ :=
    original_function_connectedness_preparation cX φ hφ g ρ hρ cT ξ hinj hξ hsnc G hG hI M hM hsupp
  let : IsIso (effectiveCartierPushforwardUnitMap ρ E hE) := hunit
  obtain ⟨Tb, _, _, _, _, _, _, hProj, r', ξb, Gb, Db, c, ι, _, _, _, hinjb, hξb, hsncb, hGbsupp,
    hDeff, hDnef, hDbig, hGnef, hι, hV, hGcb⟩ := hcomp
  obtain ⟨cTb, -⟩ : ∃ c : EtaleChart K Tb (N + 1), genericPoint Tb ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Tb) (n := N + 1)).symm ▸ Opens.mem_top _)
  have hcoho := model_roundup_H1_vanishing_of_compactification K (hKV (N + 1)) (by omega) cX
    (specAlgebraEtaleChart φ hφ) rfl ρ hρ cT _ G (E - S) M hM hround hProj cTb ξb hinjb hξb hsncb
    Gb Db
    hGbsupp hDeff hDnef hDbig c hGnef ι hι hV hGcb
  have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hES (t : CodimensionOnePoint T) (ht : 0 < cartierCoefficient S (t : T)) :
      cartierCoefficient E (t : T) = 0 := by
    rcases hdisj t with h | h
    · exact h
    · omega
  have hc := threshold_member_union_fibre_preconnected_of_H1 ρ hnorm B E S hE hS
    M hM ξ hξ hsupp hSc hES hcoho
    (specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))
  simp only [B, strictTransformConnectednessBoundary_coefficient, H] at hc
  convert hc using 1

/-- Principalizing SNC models of the original family as in `exists_nondegenerate_function_snc_model`,
which are in addition open parts of SNC compactifications (`HasSNCCompactification`). -/
def CompactifiedStrictTransformModelStatement (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra K A] [IsNoetherianRing A] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    {J : Type} [Finite J] (g : J → A), (∃ j, g j ∉ Ideal.span {φ (MvPolynomial.X 0)}) →
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ Spec (CommRingCat.of A)) (_ : IsDominant ρ)
      (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T (N + 1)) (r : ℕ) (ξ : Fin r → T)
      (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K (N + 1) ξ ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (z : T) = 0) ∧
      (∀ (j : {j : J // g j ≠ 0}) (z : CodimensionOnePoint T), (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2))) (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Gc (z : T) = 0) ∧
      effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
        effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2)) (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ ∧
      (∀ t : T,
        (∀ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t ≤ cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t) ∧
        ∃ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t = cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t) ∧
      (∃ s₀ : Fin r,
        (ρ (ξ s₀)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)} ∧
        Function.Bijective (ρ.stalkMap (ξ s₀)) ∧
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (ξ s₀) = 1 ∧
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (ξ s₀) = 0 ∧ cartierCoefficient Gc (ξ s₀) = 0) ∧
      HasSNCCompactification K (N + 1) T Gc ∧
      ∀ (x : Spec (CommRingCat.of A)) (M : ℕ), 1 ≤ M →
        ModelThresholdBadAt cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) x
          (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
        ∃ s₁ : Fin r,
          (M : ℤ) * (1 - cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
            (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
            cT etaleCharts_cover) (ξ s₁)) ≤ cartierCoefficient Gc (ξ s₁) ∧
          x ∈ ρ '' closure ({ξ s₁} : Set T)

set_option maxHeartbeats 1600000 in
/-- The original nondegenerate chart statement from sum KV and compactified principalizing models. -/
theorem nondegenerateStrictTransformChartStatement_of_kvSum_of_compactifiedModels
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (hKV : ∀ n, KawamataViehwegVanishingSNCProjective K n)
    (hcm : CompactifiedStrictTransformModelStatement K) :
    NondegenerateStrictTransformChartStatement K := by
  classical
  intro A _ _ _ N _ cX φ hφ _ J _ g M hN hM χ hnd hbad
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := n + 1 + 1)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : (Ideal.span {φ (MvPolynomial.X 0)}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, Gc, hGc,
      hinj, hcoh, hsnc, hcrep, hH, hgsupp, hGc0, hGcI, hmin,
      ⟨s₀, himage, -, hh₀, hk₀, ha₀⟩, hcomp, hbadmem⟩ :=
    hcm A (n + 1) cX φ hφ g hnd
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
  have hconnected := compactifiableStrictTransformConnectedness_of_kvSum hKV A (n + 1) cX φ hφ g hnd
    χ M hN hM T ρ hρ cT r ξ hinj hcoh hsnc hcrep hH Gc hGc hGc0 hGcI hcomp
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

/-- F1 from sum KV and principalizing models with SNC compactifications. -/
theorem mixedFujitaFreeness_of_kvSum_of_compactifiedModels
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcm : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      CompactifiedStrictTransformModelStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_nondegenerateCharts hKV
    (fun K _ _ _ => nondegenerateStrictTransformChartStatement_of_kvSum_of_compactifiedModels
      (fun n => kawamataViehwegVanishingSNCProjective_of_usual
        (kawamataViehwegVanishingSNC_of_sum (hKV K n))) (hcm K))

end MixedFujita
