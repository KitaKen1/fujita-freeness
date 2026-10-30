/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedCartierApproximation
public import MixedFujita.SignedSNCKawamataViehweg
public import MixedFujita.ProjectiveKawamataViehweg
public import MixedFujita.ProperNormalBigAddNef
public import MixedFujita.EtaleChartDimension
public import MixedFujita.LocalBirationalOrders
public import MixedFujita.SNCComponentCartier
public import MixedFujita.FloorDivisorLifting
public import MixedFujita.StrictTransformRoundupGeometry
public import MixedFujita.AffineRelativeCanonicalNef

/-!
Kawamata–Viehweg vanishing on a compactified model and its restriction to the open model
(step 9, relative vanishing from global vanishing).

Let `T̄` be a smooth projective variety, `Ḡ` an effective divisor supported on a simple normal crossing
family, `M ≥ 1`, `E` the Cartier divisor with coefficients `⌈-ḡ/M⌉`, and `D̄` an effective nef and
big divisor with `c D̄ - Ḡ` nef. For `M m ≥ c + 1` the adjoint `M (K + m D̄ - K) - Ḡ = D̄ + ((M m - 1 - c)
D̄ + (c D̄ - Ḡ))` is big and nef, so Kawamata–Viehweg vanishing (the signed roundup form,
check-242) gives `H¹(T̄, 𝒪(K + m D̄ + E)) = 0` (`compactified_twist_H1_vanishing`). On the open model
`T = T̄ ∖ D̄` these twists give `H¹(T, 𝒪(ι^*(K + E))) = 0` (check-387,
`open_model_H1_vanishing_of_compactification`). The vanishing theorem is used only on the
projective `T̄` (`KawamataViehwegVanishingSNCProjective`, check-394).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

section Compactified

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

/-- **Kawamata–Viehweg vanishing for the twists by a nef and big boundary divisor.** On a smooth
projective variety, for an effective `Ḡ` supported on an SNC family, the Cartier divisor `E` with
coefficients `⌈-ḡ/M⌉`, and an effective nef and big `D̄` with `c D̄ - Ḡ` nef, the first cohomology
of `𝒪(K + m D̄ + E)` vanishes as soon as `M m ≥ c + 1`. -/
theorem compactified_twist_H1_vanishing (hKV : KawamataViehwegVanishingSNCProjective K n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ H : CartierDivisor T, CartierIsAmpleProj K H) (hn : 1 ≤ n)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (G E D : CartierDivisor T) (M : ℕ) (hM : 1 ≤ M)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient G (t : T) = 0)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient G (t : T) : ℝ) / (M : ℝ))⌉)
    (hDnef : CartierIsNef K D) (hDbig : CartierIsBig K D) (c : ℕ)
    (hGnef : CartierIsNef K (c • D - G)) (m : ℕ) (hm : c + 1 ≤ M * m) :
    Subsingleton (Scheme.Modules.Cohomology
      ((smoothCanonicalDivisor cT + m • D) + E).sheaf 1) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  obtain ⟨k, hk⟩ : ∃ k, M * m = 1 + k + c := ⟨M * m - 1 - c, by omega⟩
  have hadj : M • ((smoothCanonicalDivisor cT + m • D) - smoothCanonicalDivisor cT) - G =
      D + (k • D + (c • D - G)) := by
    rw [add_sub_cancel_left, smul_smul, hk, add_nsmul, add_nsmul, one_nsmul]
    abel
  have hN : CartierIsNef K (k • D + (c • D - G)) :=
    cartierIsNef_add (cartierIsNef_nsmul hDnef _) hGnef
  have hnef : CartierIsNef K
      (M • ((smoothCanonicalDivisor cT + m • D) - smoothCanonicalDivisor cT) - G) := by
    rw [hadj]
    exact cartierIsNef_add hDnef hN
  have hbig : CartierIsBig K
      (M • ((smoothCanonicalDivisor cT + m • D) - smoothCanonicalDivisor cT) - G) := by
    rw [hadj]
    exact proper_normal_cartierIsBig_add_of_isNef K n hdim hn hnormT D _ hDbig hN
  exact signed_snc_roundup_H1_vanishing_of_projective_KV K hKV hProj cT ξ
    hinj hξ hsnc G E (smoothCanonicalDivisor cT + m • D) M hM hsupport hE hnef hbig

/-- **Vanishing on the open model of a compactification.** In the situation of
`compactified_twist_H1_vanishing`, let `ι : Y → T` be an open immersion of integral schemes onto the
locus where `1` is a local equation of `D`. Then `H¹(Y, 𝒪(ι^*(K + E))) = 0`. -/
theorem open_model_H1_vanishing_of_compactification
    (hKV : KawamataViehwegVanishingSNCProjective K n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from T))]
    (hProj : ∃ H : CartierDivisor T, CartierIsAmpleProj K H) (hn : 1 ≤ n)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (G E D : CartierDivisor T) (M : ℕ) (hM : 1 ≤ M)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient G (t : T) = 0)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient G (t : T) : ℝ) / (M : ℝ))⌉)
    (hDeff : D.IsEffective) (hDnef : CartierIsNef K D) (hDbig : CartierIsBig K D) (c : ℕ)
    (hGnef : CartierIsNef K (c • D - G))
    {Y : Scheme.{u}} [IsIntegral Y] (ι : Y ⟶ T) [IsOpenImmersion ι] [IsDominant ι]
    (hV : ∀ x : T, x ∈ ι.opensRange ↔ D.IsLocalEquationAt x 1) :
    Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ι (smoothCanonicalDivisor cT + E)).sheaf 1) := by
  refine cartierPullback_H1_subsingleton_of_twists ι (smoothCanonicalDivisor cT + E) D hDeff hV
    (c + 1) fun m hm => ?_
  have hmM : c + 1 ≤ M * m := le_trans hm (Nat.le_mul_of_pos_left m hM)
  have h := compactified_twist_H1_vanishing K hKV hProj hn cT ξ hinj hξ hsnc G E D M hM hsupport hE
    hDnef hDbig c hGnef m hmM
  rwa [add_right_comm] at h

end Compactified

section Canonical

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The canonical divisor for a reference chart covering the whole scheme is zero. -/
theorem smoothCanonicalDivisor_eq_zero_of_top {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (c₀ : EtaleChart K X n) (h : c₀.U = ⊤) : smoothCanonicalDivisor c₀ = 0 := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  refine ⟨1, ?_, CartierDivisor.isLocalEquationAt_zero x⟩
  have hx : x ∈ c₀.U := by rw [h]; trivial
  have h1 := canonicalDivisor_isLocalEquationAt c₀ etaleCharts_cover c₀ hx
  have heq : etaleChartCanonicalEquation c₀ c₀ = 1 := by
    apply Units.ext
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self, Units.val_one]
  rw [heq] at h1
  exact h1

/-- With a reference chart covering the whole scheme, every canonical divisor is principal. -/
theorem smoothCanonicalDivisor_eq_principal_of_top {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (c₀ c : EtaleChart K X n) (h : c₀.U = ⊤) :
    smoothCanonicalDivisor c = principalCartierDivisor X (etaleChartCanonicalEquation c c₀) := by
  have h1 := canonicalDivisor_change_reference c₀ c (etaleCharts_cover (K := K) (X := X) (n := n))
  have h0 := smoothCanonicalDivisor_eq_zero_of_top c₀ h
  unfold smoothCanonicalDivisor at h0 ⊢
  rw [h1, h0, zero_add]

/-- The relative canonical divisor of an open immersion of smooth varieties is zero. -/
theorem birationalRelativeCanonicalDivisor_eq_zero_of_isOpenImmersion {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ι : T ⟶ X) [IsOpenImmersion ι] [IsDominant ι] [ι.IsOver (Spec (CommRingCat.of K))]
    (hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ι))
    (cX : EtaleChart K X n) (cT : EtaleChart K T n) :
    birationalRelativeCanonicalDivisor n ι hι cX etaleCharts_cover cT etaleCharts_cover = 0 := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm
  intro z
  rw [cartierCoefficient_zero]
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K X n, ι (z : T) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸ Opens.mem_top _)
  obtain ⟨c', hc'⟩ : ∃ c : EtaleChart K T n, (z : T) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top _)
  have hf := relativeCanonicalDivisor_isLocalEquationAt ι cX etaleCharts_cover cT etaleCharts_cover
    (isUnit_chartRelativeJacobianDet_of_bijective ι hι cX cT) (z : T) c hc c' hc'
  have hbij : Function.Bijective (ι.stalkMap (z : T)) := ConcreteCategory.bijective_of_isIso _
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord hf, IsUnit.unit_spec]
  haveI := (hnorm (z : T))
  haveI := normal_codimensionOne_stalk_DVR z
  exact chartRelativeJacobianDet_ord_zero_of_stalkMap_bijective ι z hbij c hc c' hc'

end Canonical

section Model

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem int_ceil_neg_mul_add_div (M : ℕ) (hM : 1 ≤ M) (h g : ℤ) :
    ⌈-((((M : ℤ) * h + g : ℤ) : ℝ) / (M : ℝ))⌉ = -h + ⌈-((g : ℝ) / (M : ℝ))⌉ := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have : -((((M : ℤ) * h + g : ℤ) : ℝ) / (M : ℝ)) = ((-h : ℤ) : ℝ) + -((g : ℝ) / (M : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [this, Int.ceil_intCast_add]

/-- **The roundup H¹ vanishing on the open model of a compactification.** Let `ρ : T → X` be a
birational model of a smooth variety with a chart covering `X`, `H = ρ^* div u`, `G_c` a divisor on
`T`, and `C` a Cartier divisor with coefficients `⌈-b/M⌉` for the boundary
`B = M (H + B_crep) + G_c` of the connectedness argument. Suppose `T` is an open subscheme of a
smooth projective `T̄`, the complement of an effective nef and big `D̄`, and `G_c` is the restriction of an
effective `Ḡ` supported on an SNC family with `c D̄ - Ḡ` nef. Then Kawamata–Viehweg vanishing on `T̄`
gives `H¹(T, 𝒪(C)) = 0`. -/
theorem model_roundup_H1_vanishing_of_compactification
    (hKV : KawamataViehwegVanishingSNCProjective K n)
    (hn : 1 ≤ n) {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (cX c₀ : EtaleChart K X n) (hc₀ : c₀.U = ⊤)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cT : EtaleChart K T n)
    (u : X.functionFieldˣ) (Gc C : CartierDivisor T) (M : ℕ) (hM : 1 ≤ M)
    (hC : ∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-((cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT
        (cartierPullback ρ (principalCartierDivisor X u)) Gc M) (t : T) : ℝ) / (M : ℝ))⌉)
    {Tb : Scheme.{u}} [IsIntegral Tb] [IsNoetherian Tb] [Tb.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K))]
    [IsProper (Tb ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Tb))]
    (hProj : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H)
    (cTb : EtaleChart K Tb n) {r : ℕ} (ξ : Fin r → Tb)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (Gb Db : CartierDivisor Tb)
    (hGbsupp : ∀ t : CodimensionOnePoint Tb, (t : Tb) ∉ Set.range ξ →
      cartierCoefficient Gb (t : Tb) = 0)
    (hDeff : Db.IsEffective) (hDnef : CartierIsNef K Db) (hDbig : CartierIsBig K Db) (c : ℕ)
    (hGnef : CartierIsNef K (c • Db - Gb))
    (ι : T ⟶ Tb) [IsOpenImmersion ι] [IsDominant ι] [ι.IsOver (Spec (CommRingCat.of K))]
    (hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ι))
    (hV : ∀ x : Tb, x ∈ ι.opensRange ↔ Db.IsLocalEquationAt x 1)
    (hGc : cartierPullback ι Gb = Gc) :
    Subsingleton (Scheme.Modules.Cohomology C.sheaf 1) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (Tb ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hnormTb : ∀ t : Tb, IsIntegrallyClosed (Tb.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  -- the roundup of `-Ḡ/M` on the compactification
  obtain ⟨F, -, -, hFc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  let a : Fin r → ℤ := fun i => ⌈-((cartierCoefficient Gb (ξ i) : ℝ) / (M : ℝ))⌉
  let Eb : CartierDivisor Tb := ∑ i, a i • F i
  have hEb : ∀ t : CodimensionOnePoint Tb, cartierCoefficient Eb (t : Tb) =
      ⌈-((cartierCoefficient Gb (t : Tb) : ℝ) / (M : ℝ))⌉ := by
    intro t
    rcases cartierCoefficient_member_combination ξ hinj F hFc a t with ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
    · rw [hci, hGbsupp t hti]
      norm_num
  have hvan := open_model_H1_vanishing_of_compactification K hKV hProj hn cTb ξ hinj hξ hsnc Gb Eb Db M
    hM hGbsupp hEb hDeff hDnef hDbig c hGnef ι hV
  -- the correction divisor is principal
  let H := cartierPullback ρ (principalCartierDivisor X u)
  let Rρ := birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover
  let P : CartierDivisor T := -H + Rρ - cartierPullback ι (smoothCanonicalDivisor cTb)
  have hprin : P ∈ (principalCartierDivisorAddHom T).range := by
    have hR := affine_relative_adjoint_eq_ordinary ρ hρ cX cT 0 0 1
    have hRι := affine_relative_adjoint_eq_ordinary ι hι cTb cT 0 0 1
    rw [birationalRelativeCanonicalDivisor_eq_zero_of_isOpenImmersion ι hι cTb cT] at hRι
    simp only [one_nsmul, zero_sub, sub_zero] at hR hRι
    rw [smoothCanonicalDivisor_eq_principal_of_top c₀ cX hc₀, cartierPullback_principal] at hR
    have hmem : ∀ f : T.functionFieldˣ,
        principalCartierDivisor T f ∈ (principalCartierDivisorAddHom T).range :=
      fun f => ⟨Additive.ofMul f, principalCartierDivisorAddHom_apply T _⟩
    have hH : H ∈ (principalCartierDivisorAddHom T).range := by
      dsimp only [H]
      rw [cartierPullback_principal]
      exact hmem _
    obtain ⟨a, b, hab⟩ : ∃ a b : T.functionFieldˣ, -Rρ = -smoothCanonicalDivisor cT +
        principalCartierDivisor T a + principalCartierDivisor T b := ⟨_, _, hR⟩
    obtain ⟨c', hc'⟩ : ∃ c' : T.functionFieldˣ, 0 = -smoothCanonicalDivisor cT +
        cartierPullback ι (smoothCanonicalDivisor cTb) + principalCartierDivisor T c' := ⟨_, hRι⟩
    have e1 : Rρ = smoothCanonicalDivisor cT - principalCartierDivisor T a -
        principalCartierDivisor T b := by
      rw [← neg_neg Rρ, hab]
      abel
    have e2 : smoothCanonicalDivisor cT = cartierPullback ι (smoothCanonicalDivisor cTb) +
        principalCartierDivisor T c' := by
      have h0 : smoothCanonicalDivisor cT - (cartierPullback ι (smoothCanonicalDivisor cTb) +
          principalCartierDivisor T c') = 0 := by
        rw [show smoothCanonicalDivisor cT - (cartierPullback ι (smoothCanonicalDivisor cTb) +
            principalCartierDivisor T c') = -(-smoothCanonicalDivisor cT +
            cartierPullback ι (smoothCanonicalDivisor cTb) + principalCartierDivisor T c') by abel,
          ← hc', neg_zero]
      exact sub_eq_zero.mp h0
    have hPeq : P = -H + principalCartierDivisor T c' - principalCartierDivisor T a -
        principalCartierDivisor T b := by
      dsimp only [P]
      rw [e1, e2]
      abel
    rw [hPeq]
    exact sub_mem (sub_mem (add_mem (neg_mem hH) (hmem _)) (hmem _)) (hmem _)
  obtain ⟨f, hf⟩ := hprin
  have hfP : principalCartierDivisor T (Additive.toMul f) = P :=
    (principalCartierDivisorAddHom_apply T f).symm.trans hf
  -- the actual roundup is the restriction of the compactified roundup up to `P`
  let Bc := crepantBoundaryCartier ρ hρ cX 1 1
    (1 • (smoothCanonicalDivisor cX + principalCartierDivisor X 1)) cT etaleCharts_cover
  have hRB : Rρ = -Bc := by
    dsimp only [Bc, Rρ]
    rw [crepantBoundaryCartier_eq_neg_discrepancy, neg_neg, logDiscrepancyDivisor_boundary_zero,
      one_nsmul]
  have hCeq : C = cartierPullback ι (smoothCanonicalDivisor cTb + Eb) +
      principalCartierDivisor T (Additive.toMul f) := by
    rw [hfP]
    apply cartierDivisor_eq_of_forall_coefficient_eq hnormT
    intro t
    have hbij : Function.Bijective (ι.stalkMap (t : T)) := ConcreteCategory.bijective_of_isIso _
    have hcoh : Order.coheight (ι (t : T)) = 1 :=
      (coheight_eq_of_stalkMap_bijective ι (t : T) hbij).symm.trans t.property
    haveI := hnormT (t : T)
    haveI := normal_codimensionOne_stalk_DVR t
    haveI := hnormTb (ι (t : T))
    haveI := normal_codimensionOne_stalk_DVR (⟨ι (t : T), hcoh⟩ : CodimensionOnePoint Tb)
    have hpullE := cartierCoefficient_pullback_of_stalkMap_bijective ι t hcoh hbij Eb
    have hpullG := cartierCoefficient_pullback_of_stalkMap_bijective ι t hcoh hbij Gb
    rw [hGc] at hpullG
    have hEbt := hEb ⟨ι (t : T), hcoh⟩
    rw [hC t, strictTransformConnectednessBoundary_coefficient]
    simp only [P, cartierPullback_add, cartierCoefficient_add, cartierCoefficient_sub,
      cartierCoefficient_neg, hpullE]
    change _ = _ + cartierCoefficient Eb (ι (t : T)) + _
    rw [hEbt, ← hpullG, hRB, cartierCoefficient_neg]
    change ⌈-((((M : ℤ) * (cartierCoefficient H (t : T) + cartierCoefficient Bc (t : T)) +
        cartierCoefficient Gc (t : T) : ℤ) : ℝ) / (M : ℝ))⌉ = _
    rw [int_ceil_neg_mul_add_div M hM]
    ring
  rw [hCeq]
  let e := cartierSheafPrincipalShiftIso (cartierPullback ι (smoothCanonicalDivisor cTb + Eb))
    (Additive.toMul f)
  let : Subsingleton ((Sheaf.functorH.{u} _ 1).obj ((SheafOfModules.toSheaf T.ringCatSheaf).obj
      (cartierPullback ι (smoothCanonicalDivisor cTb + Eb)).sheaf)) := hvan
  exact ((Sheaf.functorH.{u} _ 1).mapIso
    ((SheafOfModules.toSheaf T.ringCatSheaf).mapIso e)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Model

end MixedFujita
