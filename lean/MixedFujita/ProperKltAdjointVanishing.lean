/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltAdjointH1Vanishing
public import MixedFujita.ProjectiveKawamataViehweg
public import MixedFujita.DominantCartierPullbackSheaf
public import MixedFujita.CrepantKltDescent
public import MixedFujita.ChowCartierAmpleModel
public import MixedFujita.KodairaLemmaStatementProof

/-!
Klt adjoint `H¹` vanishing on proper varieties from the projective Kawamata–Viehweg statement
(step 10, R0′).

* A log pair on a proper variety `X` (no ample divisor) has a smooth projective simple normal
  crossing model: on Chow's projective model `q : Y → X`, the crepant pullback
  `(c_Y, q*ω, d, q*D)` has a projective SNC model `ρ : T → Y` (the Hironaka model, using the
  ample divisor of `Y`), and the crepant boundary of `X` along `ρ ≫ q` is the one of `Y` along `ρ`
  (`crepantBoundaryCartier_comp`) (`exists_projective_snc_model_of_proper`).
* With the nef pullback and the sheaf isomorphism of check 467 (no ample divisor on `X`), the
  argument of check-242 gives `H¹(X, O(P)) = 0` for every klt pair on a proper normal `X` and every
  `P` with `d P − D` nef and big, from the projective statement on `T`
  (`klt_adjoint_H1_vanishing_of_projective_KV`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- **A smooth projective SNC model of a log pair on a proper variety**: no ample divisor on `X`
is assumed; the model carries an ample Cartier divisor. -/
theorem exists_projective_snc_model_of_proper (K : Type u) [Field K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (p : T ⟶ X) (_ : IsDominant p) (_ : p.IsOver (Spec (CommRingCat.of K))) (_ : IsProper p)
      (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier p hp c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      ∃ J : CartierDivisor T, CartierIsAmpleProj K J := by
  obtain ⟨Y, hY, hYo, q, hover, hproj, hsurj, U, hU, hiso, A, hA⟩ :=
    proper_integral_exists_chow_model_with_ample_cartier K (X := X)
  let := hY
  let := hYo
  let := hover
  let := hproj
  let := hsurj
  let := hiso
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := q)]
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  have hq : Function.Bijective (dominantFunctionFieldAlgHom (K := K) q) :=
    dominantFunctionFieldMap_bijective_of_isIso_nonempty_restrict q U hU
  have hdimY : topologicalKrullDim Y = n :=
    (birational_topologicalKrullDim_eq q hq).trans (etaleChart_topologicalKrullDim c)
  obtain ⟨cY⟩ := nonempty_etaleChart_of_charZero (K := K) hdimY
  obtain ⟨T, hT, hTo, hTN, hTs, ρ, hdom, hrover, hrprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp,
      -, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cY (crepantPullbackFormUnit q hq c f cY) d
      (cartierPullback q D) (fun i : PEmpty.{1} => i.elim) hA
  let := hT
  let := hTo
  let := hdom
  let := hrover
  let := hrprop
  refine ⟨T, hT, hTo, hTN, hTs, ρ ≫ q, inferInstance, inferInstance, inferInstance,
    dominantFunctionFieldAlgHom_comp_bijective q ρ hq hρ, cT, r, ξ, hinj, hcoh, hsnc, ?_, J,
    cartierIsAmpleProj_of_veryAmple hJ⟩
  intro t ht
  rw [crepantBoundaryCartier_comp q ρ hq hρ c f d D cY cT etaleCharts_cover]
  exact hsupp t ht

/-- **Klt adjoint `H¹` vanishing on a proper normal variety from the projective
Kawamata–Viehweg statement**: no projectivity of `X` is assumed. -/
theorem klt_adjoint_H1_vanishing_of_projective_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNCProjective K n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (P : CartierDivisor X)
    (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    Subsingleton (Scheme.Modules.Cohomology P.sheaf 1) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, J, hJ⟩ := exists_projective_snc_model_of_proper K cX fX d D
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨E, hE, hEc, hexc⟩ := exists_effective_exceptional_klt_boundary_roundup p hp
    hnorm hcov cX fX d hd D heff hklt cT ξ hinj hξ hsnc hsupp
  let C := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  let fT := crepantPullbackFormUnit p hp cX fX cT
  let P₀ := cartierPullback p P - principalCartierDivisor T fT
  have hadj : d • (P₀ - smoothCanonicalDivisor cT) - C = cartierPullback p (d • P - D) := by
    have hrec := crepantBoundaryCartier_smooth_recombine p hp cX fX d D cT
    dsimp [P₀, C, fT]
    rw [cartierPullback_sub, cartierPullback_nsmul, ← hrec]
    module
  have hnefT : CartierIsNef K (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsNef_cartierPullback_of_dominant p hnef
  have hbigT : CartierIsBig K (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsBig_cartierPullback hnorm hnormT p hp
      ((etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim cX).symm) hbig
  have hsrc := signed_snc_roundup_H1_vanishing_of_projective_KV K hKV ⟨J, hJ⟩ cT ξ hinj hξ hsnc
    C E P₀ d hd hsupp hEc hnefT hbigT
  have he : (P₀ + E) + principalCartierDivisor T fT = cartierPullback p P + E := by
    dsimp [P₀]
    abel
  let b : (P₀ + E).sheaf ≅ (cartierPullback p P + E).sheaf :=
    (cartierSheafPrincipalShiftIso (P₀ + E) fT).symm ≪≫ eqToIso (congrArg CartierDivisor.sheaf he)
  let : Subsingleton (Scheme.Modules.Cohomology (P₀ + E).sheaf 1) := hsrc
  let : Subsingleton (Scheme.Modules.Cohomology (cartierPullback p P + E).sheaf 1) :=
    (actualCohomologyLinearEquivOfIso b 1).symm.subsingleton
  obtain ⟨aP⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant p P
  let a : ((Scheme.Modules.pullback p).obj P.sheaf ⊗ E.sheaf) ≅
      (cartierPullback p P + E).sheaf := tensorIso aP (Iso.refl _) ≪≫ cartierTensorSheafIso _ _
  exact proper_birational_exceptional_cartier_H1_descent K p hp hnorm hnormT E hE hexc P
    (actualCohomologyLinearEquivOfIso a 1).subsingleton

end MixedFujita
