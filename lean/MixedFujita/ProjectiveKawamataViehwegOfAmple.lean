/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleKawamataViehweg
public import MixedFujita.PrincipalizationRelativeAmple
public import MixedFujita.ProperKawamataViehwegReduction
public import MixedFujita.PrincipalizingSNCBaseSequence
public import MixedFujita.KodairaLemmaNormal
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.PrincipalizedGlobalGeneration
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.BirationalPrimeLifts
public import MixedFujita.SmoothProperCurveSections
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.BirationalExceptionalH1Descent
public import MixedFujita.KltIsolationGeneration
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.LocalBirationalOrders

/-!
The projective Kawamata–Viehweg statement from the ample one (step 10, R1).

Let `N = m (Q − K_T) − Σ a_k E_k` be nef and big on a smooth projective `T`. Kodaira's lemma gives
`j N − H = F` up to a principal divisor with `F` effective. A principalization `μ : T' → T` of the
supports of the `E_k` and of `F` (with centres over them) carries `μ*(c H₀) − G` ample with `G`
effective over the centres (check 473), and `k H − H₀` is nef for large `k`. For the klt pair
`(T, Σ (a_k/m) E_k)` with crepant boundary `C` on `T'` and `s = j c' t` (`c' = c k`, `t` large),
the boundary `s C + c' μ*F + G` has the same roundup as `C` (`ceil_neg_div_perturb`) and
`m s (P₀ − K_{T'}) − (s C + c' μ*F + G) = j c' (t − 1) μ*N + (c' μ*H − G) − c' div(μ*u)` is ample.
The ample statement on `T'` (check 474) and the descent of check 468 give `H¹(T, O(Q)) = 0`
(`kawamataViehwegVanishingSNCProjective_of_ample`). Hence F1 follows from the ample statement
alone (`mixedFujitaFreeness_of_ampleKV`).
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

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- **A small perturbation does not change the roundup**: for integers `C` and `0 ≤ e < s`,
`⌈−(s C + e)/(m s)⌉ = ⌈−C/m⌉`. -/
theorem ceil_neg_div_perturb (C e : ℤ) (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (he0 : 0 ≤ e)
    (hes : e < s) :
    ⌈-((((s : ℤ) * C + e : ℤ) : ℝ) / ((m * s : ℕ) : ℝ))⌉ = ⌈-((C : ℝ) / (m : ℝ))⌉ := by
  set q := ⌈-((C : ℝ) / (m : ℝ))⌉ with hq
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : (q : ℝ) - 1 < -((C : ℝ) / (m : ℝ)) := by
    have := Int.ceil_lt_add_one (-((C : ℝ) / (m : ℝ)))
    linarith
  have h2 : -((C : ℝ) / (m : ℝ)) ≤ q := Int.le_ceil _
  have hA : (m : ℤ) * (q - 1) < -C := by
    have : (m : ℝ) * ((q : ℝ) - 1) < -(C : ℝ) := by
      have := mul_lt_mul_of_pos_left h1 hm'
      rwa [mul_neg, mul_div_cancel₀ _ hm'.ne'] at this
    exact_mod_cast this
  have hB : -C ≤ (m : ℤ) * q := by
    have : -(C : ℝ) ≤ (m : ℝ) * q := by
      have := mul_le_mul_of_nonneg_left h2 hm'.le
      rwa [mul_neg, mul_div_cancel₀ _ hm'.ne'] at this
    exact_mod_cast this
  rw [Int.ceil_eq_iff]
  have hms : (0 : ℝ) < ((m * s : ℕ) : ℝ) := by push_cast; positivity
  constructor
  · rw [lt_neg, neg_sub, div_lt_iff₀ hms]
    have hint : (s : ℤ) * C + e < (m : ℤ) * s * (1 - q) := by nlinarith
    have : (((s : ℤ) * C + e : ℤ) : ℝ) < ((m : ℤ) * s * (1 - q) : ℤ) := by exact_mod_cast hint
    push_cast at this ⊢
    linarith
  · rw [neg_le, le_div_iff₀ hms]
    have hint : -((m : ℤ) * s * q) ≤ (s : ℤ) * C + e := by nlinarith
    have : ((-((m : ℤ) * s * q) : ℤ) : ℝ) ≤ (((s : ℤ) * C + e : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at this ⊢
    linarith

section Shift

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Ampleness is invariant under principal shifts. -/
theorem cartierIsAmpleProj_add_principalCartierDivisor {A : CartierDivisor Y}
    (hA : CartierIsAmpleProj K A) (g : Y.functionFieldˣ) :
    CartierIsAmpleProj K (A + principalCartierDivisor Y g) := by
  obtain ⟨m, hm, n, e, he, hbase, g', hg', hggen, f, hmA⟩ := hA
  exact ⟨m, hm, n, e, he, hbase, g', hg', hggen, f * g ^ m, by
    rw [smul_add, hmA, principalCartierDivisor_mul, principalCartierDivisor_power, add_assoc]⟩

/-- For an ample `H` and any `H₀`, `k H − H₀` is nef for some `k ≥ 1`. -/
theorem exists_nsmul_sub_isNef {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H)
    (H₀ : CartierDivisor Y) : ∃ k : ℕ, 1 ≤ k ∧ CartierIsNef K (k • H - H₀) := by
  obtain ⟨k₀, hk₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (-H₀)
  refine ⟨max k₀ 1, le_max_right _ _, ?_⟩
  have h := cartierIsGloballyGenerated_isNef (K := K) (hk₀ (max k₀ 1) (le_max_left _ _))
  rwa [neg_add_eq_sub] at h

end Shift

/-- **The projective Kawamata–Viehweg statement from the ample one.** -/
theorem kawamataViehwegVanishingSNCProjective_of_ample (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (hKV : KawamataViehwegVanishingSNCAmple K n) :
    KawamataViehwegVanishingSNCProjective K n := by
  intro T _ _ _ _ _ hProj cT r ξ hinj hξ hsnc E hEc Q m hm a ha hnef hbig
  -- dimension zero: Grothendieck vanishing
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := properOverField_scheme_isNoetherian (K := K) (X := T)
    have hdim : topologicalKrullDim T ≤ ((0 : ℕ) : WithBot ℕ∞) :=
      (etaleChart_topologicalKrullDim cT).le
    have : Subsingleton (Q.sheaf.H 1) :=
      moduleCohomology_subsingleton_of_topologicalKrullDim_le Q.sheaf hdim 1 (by norm_num)
    exact (sgaCohomologyLinearEquiv Q.sheaf 1).symm.toEquiv.subsingleton
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let hTN : IsNoetherian T := properOverField_scheme_isNoetherian (K := K) (X := T)
  let : IsRegular T := ⟨fun y => isRegularLocalRing_stalk (T ↘ Spec (CommRingCat.of K)) y⟩
  have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcov : CodimOneChartCovered n K T := fun x _ =>
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top x)
  have hdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  obtain ⟨H, hH⟩ := hProj
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hH
  set N := m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k with hN
  -- Kodaira's lemma for the nef and big divisor `N`
  obtain ⟨j, hj, sK, hsK⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdim hn hnorm cT
    N H hbig hH
  set F := cartierSectionZeroDivisor (j • N - H) sK hsK with hFdef
  have hFeff : F.IsEffective := cartierSectionZeroDivisor_isEffective _ _ _
  have hFeq := cartierSectionZeroDivisor_sub (j • N - H) sK hsK
  -- the closed set to principalize
  obtain ⟨Z, hZ⟩ : ∃ Z : Closeds T, (Z : Set T) =
      (⋃ k, (cartierSupportCloseds (E k) : Set T)) ∪ (cartierSupportCloseds F : Set T) :=
    ⟨⟨_, (isClosed_iUnion_of_finite fun k => (cartierSupportCloseds (E k)).isClosed).union
      (cartierSupportCloseds F).isClosed⟩, rfl⟩
  have hZη : genericPoint T ∉ (Z : Set T) := by
    rw [hZ]
    rintro (h | h)
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact genericPoint_notMem_cartierSupportCloseds _ hk
    · exact genericPoint_notMem_cartierSupportCloseds _ h
  have hEZ : ∀ (k : Fin r) (x : T), x ∉ (Z : Set T) → x ∉ (cartierSupportCloseds (E k) : Set T) :=
    fun k x hx h => hx (by rw [hZ]; exact Or.inl (Set.mem_iUnion.mpr ⟨k, h⟩))
  have hFZ : ∀ x : T, x ∉ (Z : Set T) → x ∉ (cartierSupportCloseds F : Set T) :=
    fun x hx h => hx (by rw [hZ]; exact Or.inr h)
  -- the principalization
  obtain ⟨S, hc, hBi, instB, hBN, hBsm, hμdom, hμover, hμprop, hμproj, hBft, hBqc, hBsep, cB, hμ,
      -, r', ξ', hinj', hξ', hsnc', hβ, -⟩ :=
    exists_principalizing_smooth_snc_base_sequence (K := K) cT Z hZη ⊤
      (by rw [Scheme.IdealSheafData.support_top]; exact fun x hx => absurd hx (by simp))
  let := hBi
  let := instB
  let := hBN
  let := hBsm
  let := hμdom
  let := hμover
  let := hμprop
  let := hBsep
  let := he
  let : IsProper (S.last ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := S.composite)]
    infer_instance
  let : Smooth (S.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormB : ∀ t : S.last, IsIntegrallyClosed (S.last.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  -- off the SNC family the model is an isomorphism on the stalks of codimension-one points
  have hstalk : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      Function.Bijective (S.composite.stalkMap (t : S.last)) ∧
        Order.coheight (S.composite (t : S.last)) = 1 ∧
        S.composite (t : S.last) ∉ (Z : Set T) := by
    intro t ht
    have hnZ := hβ t ht
    have hiso : IsIso (S.composite.stalkMap (t : S.last)) :=
      blowUpSequence_isIso_stalkMap_of_centers_over S Z hc (t : S.last) hnZ
    have hbij : Function.Bijective (S.composite.stalkMap (t : S.last)) :=
      ConcreteCategory.bijective_of_isIso _
    refine ⟨hbij, ?_, hnZ⟩
    rw [← coheight_eq_of_stalkMap_bijective S.composite (t : S.last) hbij]
    exact t.property
  -- the klt pair `(T, Σ (a_k / m) E_k)` and its crepant boundary on the model
  set D := m • smoothCanonicalDivisor cT + ∑ k, a k • E k with hDdef
  have heff : LogPairBoundaryEffective cT 1 m D := snc_logPairBoundaryEffective cT ξ E hEc m a
  have hklt : LogPairIsKlt cT 1 m D := snc_logPairIsKlt cT ξ hinj hξ hsnc E hEc m hm a ha
  let C := crepantBoundaryCartier S.composite hμ cT 1 m D cB etaleCharts_cover
  have hCsupp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      cartierCoefficient C (t : S.last) = 0 := by
    intro t ht
    obtain ⟨hbij, hcoht, hnZ⟩ := hstalk t ht
    have := smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨S.composite (t : S.last), hcoht⟩ : CodimensionOnePoint T)
    have := smoothOverField_codimensionOne_stalk_DVR (K := K) t
    obtain ⟨c, hcU⟩ : ∃ c : EtaleChart K T n, S.composite (t : S.last) ∈ c.U :=
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top _)
    have hK : cartierCoefficient (smoothCanonicalDivisor cT) (S.composite (t : S.last)) =
        T.ord ((etaleChartCanonicalEquation cT c : T.functionFieldˣ) : T.functionField)
          (S.composite (t : S.last)) :=
      cartierCoefficient_eq_ord (canonicalDivisor_isLocalEquationAt cT etaleCharts_cover c hcU)
    have hE0 : ∀ k, cartierCoefficient (E k) (S.composite (t : S.last)) = 0 := fun k =>
      cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds (E k) _ hcoht (hEZ k _ hnZ)
    rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective S.composite hμ cT 1 m D cB t
      hcoht hbij c hcU, hDdef, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_sum, hK, one_mul]
    simp only [cartierCoefficient_nsmul, hE0, mul_zero, Finset.sum_const_zero, add_zero, sub_self]
  -- the pullback of `F` lives on the SNC family
  have hFsupp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      cartierCoefficient (cartierPullback S.composite F) (t : S.last) = 0 := by
    intro t ht
    obtain ⟨hbij, hcoht, hnZ⟩ := hstalk t ht
    have := smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨S.composite (t : S.last), hcoht⟩ : CodimensionOnePoint T)
    have := smoothOverField_codimensionOne_stalk_DVR (K := K) t
    rw [cartierCoefficient_pullback_of_stalkMap_bijective S.composite t hcoht hbij]
    exact cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds F _ hcoht (hFZ _ hnZ)
  -- the effective exceptional roundup of the crepant boundary
  obtain ⟨Eex, hEex, hEexc, hexc⟩ := exists_effective_exceptional_klt_boundary_roundup
    S.composite hμ hnorm hcov cT 1 m hm D heff hklt cB ξ' hinj' hξ' hsnc' hCsupp
  -- relative ampleness of the principalization, compared with `H`
  obtain ⟨H₀, cc, G, hH₀, hcc, hGeff, hG0, hGamp⟩ :=
    blowUpSequence_exists_relative_ample e hbase S Z hZη hc
  obtain ⟨kk, hkk, hkH⟩ := exists_nsmul_sub_isNef hH H₀
  have hGsupp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      cartierCoefficient G (t : S.last) = 0 := fun t ht => hG0 _ (hβ t ht)
  -- the perturbation `X' = (c k) μ*F + G` and its size on the SNC family
  obtain ⟨X', hX'⟩ : ∃ X' : CartierDivisor S.last,
      X' = (cc * kk) • cartierPullback S.composite F + G := ⟨_, rfl⟩
  have hX'nn : ∀ t : S.last, 0 ≤ cartierCoefficient X' t := by
    intro t
    rw [hX', cartierCoefficient_add, cartierCoefficient_nsmul]
    have h1 := cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_isEffective S.composite F hFeff) t
    have h2 := cartierCoefficient_nonneg_of_isEffective G hGeff t
    positivity
  have hX'supp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      cartierCoefficient X' (t : S.last) = 0 := by
    intro t ht
    rw [hX', cartierCoefficient_add, cartierCoefficient_nsmul, hFsupp t ht, hGsupp t ht]
    simp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, cartierCoefficient X' (ξ' i) ≤ M := by
    refine ⟨∑ i, (cartierCoefficient X' (ξ' i)).toNat, fun i => ?_⟩
    have h1 := Int.self_le_toNat (cartierCoefficient X' (ξ' i))
    have h2 : (cartierCoefficient X' (ξ' i)).toNat ≤ ∑ i, (cartierCoefficient X' (ξ' i)).toNat :=
      Finset.single_le_sum (f := fun i => (cartierCoefficient X' (ξ' i)).toNat)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h3 : (((cartierCoefficient X' (ξ' i)).toNat : ℕ) : ℤ) ≤
        ((∑ i, (cartierCoefficient X' (ξ' i)).toNat : ℕ) : ℤ) := by exact_mod_cast h2
    linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = j * (cc * kk) * (M + 1) := ⟨_, rfl⟩
  have hs1 : M + 1 ≤ s := by
    rw [hsdef]
    have : 1 ≤ j * (cc * kk) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega)))
    nlinarith
  have hX'lt : ∀ t : CodimensionOnePoint S.last, cartierCoefficient X' (t : S.last) < s := by
    intro t
    by_cases ht : (t : S.last) ∈ Set.range ξ'
    · obtain ⟨i, hi⟩ := ht
      rw [← hi]
      have := hM i
      have : ((M + 1 : ℕ) : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
      push_cast at this
      linarith
    · rw [hX'supp t ht]
      have : ((M + 1 : ℕ) : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
      push_cast at this
      linarith
  -- the perturbed boundary
  obtain ⟨B', hB'⟩ : ∃ B' : CartierDivisor S.last, B' = s • C + X' := ⟨_, rfl⟩
  have hB'supp : ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ' →
      cartierCoefficient B' (t : S.last) = 0 := by
    intro t ht
    rw [hB', cartierCoefficient_add, cartierCoefficient_nsmul, hCsupp t ht, hX'supp t ht]
    simp
  have hms : 1 ≤ m * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hEB' : ∀ t : CodimensionOnePoint S.last, cartierCoefficient Eex (t : S.last) =
      ⌈-((cartierCoefficient B' (t : S.last) : ℝ) / ((m * s : ℕ) : ℝ))⌉ := by
    intro t
    have hcoef : cartierCoefficient B' (t : S.last) =
        (s : ℤ) * cartierCoefficient C (t : S.last) + cartierCoefficient X' (t : S.last) := by
      rw [hB', cartierCoefficient_add, cartierCoefficient_nsmul]
    rw [hEexc t, hcoef, ceil_neg_div_perturb _ _ m s hm (by omega) (hX'nn _) (hX'lt t)]
  -- the adjoint divisor and the ample identity
  let fT := crepantPullbackFormUnit S.composite hμ cT 1 cB
  let P₀ := cartierPullback S.composite Q - principalCartierDivisor S.last fT
  have hadj : m • (P₀ - smoothCanonicalDivisor cB) = cartierPullback S.composite N + C := by
    have hrec := crepantBoundaryCartier_smooth_recombine S.composite hμ cT 1 m D cB
    have hD : m • Q - D = N := by
      rw [hDdef, hN, nsmul_sub]
      abel
    rw [← hD, cartierPullback_sub, cartierPullback_nsmul, ← hrec]
    dsimp only [P₀, C, fT]
    module
  let w : S.last.functionFieldˣ := (Units.map (dominantFunctionFieldMap S.composite).hom.toMonoidHom
    (cartierSectionUnit (j • N - H) sK hsK) ^ (cc * kk))⁻¹
  have hμF : cartierPullback S.composite F = j • cartierPullback S.composite N -
      cartierPullback S.composite H + principalCartierDivisor S.last
        (Units.map (dominantFunctionFieldMap S.composite).hom.toMonoidHom
          (cartierSectionUnit (j • N - H) sK hsK)) := by
    rw [hFdef, cartierSectionZeroDivisor, cartierPullback_add, cartierPullback_sub,
      cartierPullback_nsmul, cartierPullback_principal]
  have hident : (m * s) • (P₀ - smoothCanonicalDivisor cB) - B' =
      ((((j * (cc * kk) * M) • cartierPullback S.composite N +
        cc • cartierPullback S.composite (kk • H - H₀)) +
        (cartierPullback S.composite (cc • H₀) - G)) + principalCartierDivisor S.last w) := by
    rw [mul_comm m s, ← smul_smul, hadj, hB', hX', hμF]
    dsimp only [w]
    rw [principalCartierDivisor_inv, principalCartierDivisor_power,
      cartierPullback_sub S.composite (kk • H) H₀, cartierPullback_nsmul S.composite H kk,
      cartierPullback_nsmul S.composite H₀ cc, hsdef]
    module
  have hamp : CartierIsAmpleProj K ((m * s) • (P₀ - smoothCanonicalDivisor cB) - B') := by
    rw [hident]
    refine cartierIsAmpleProj_add_principalCartierDivisor ?_ w
    refine proper_nef_add_ample_isAmpleProj K _ _ ?_ hGamp
    exact cartierIsNef_add
      (cartierIsNef_nsmul (cartierIsNef_cartierPullback_of_dominant S.composite hnef) _)
      (cartierIsNef_nsmul (cartierIsNef_cartierPullback_of_dominant S.composite hkH) _)
  -- the ample statement on the model and the descent
  have hsrc := signed_snc_roundup_H1_vanishing_of_ample_KV K hKV cB ξ' hinj' hξ' hsnc'
    B' Eex P₀ (m * s) hms hB'supp hEB' hamp
  have hP : (P₀ + Eex) + principalCartierDivisor S.last fT =
      cartierPullback S.composite Q + Eex := by
    dsimp only [P₀]
    abel
  let b : (P₀ + Eex).sheaf ≅ (cartierPullback S.composite Q + Eex).sheaf :=
    (cartierSheafPrincipalShiftIso (P₀ + Eex) fT).symm ≪≫
      eqToIso (congrArg CartierDivisor.sheaf hP)
  let : Subsingleton (Scheme.Modules.Cohomology (P₀ + Eex).sheaf 1) := hsrc
  let : Subsingleton (Scheme.Modules.Cohomology (cartierPullback S.composite Q + Eex).sheaf 1) :=
    (actualCohomologyLinearEquivOfIso b 1).symm.subsingleton
  obtain ⟨aP⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant S.composite Q
  let aa : ((Scheme.Modules.pullback S.composite).obj Q.sheaf ⊗ Eex.sheaf) ≅
      (cartierPullback S.composite Q + Eex).sheaf :=
    tensorIso aP (Iso.refl _) ≪≫ cartierTensorSheafIso _ _
  exact proper_birational_exceptional_cartier_H1_descent K S.composite hμ hnorm hnormB Eex hEex
    hexc Q (actualCohomologyLinearEquivOfIso aa 1).subsingleton

/-- **F1 from the ample Kawamata–Viehweg statement.** -/
theorem mixedFujitaFreeness_of_ampleKV
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCAmple K n) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_projectiveKV fun K _ _ _ n =>
    kawamataViehwegVanishingSNCProjective_of_ample K (hKV K n)

end MixedFujita
