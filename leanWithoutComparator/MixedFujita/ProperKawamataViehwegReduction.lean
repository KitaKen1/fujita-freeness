/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperKltAdjointVanishing
public import MixedFujita.CompactifiedPrincipalizingModels
public import MixedFujita.ModuleCohomologyVanishing
public import MixedFujita.SGACohomologyComparison
public import MixedFujita.ThresholdModelLifting
public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.ProperNormalBigAddNef
public import MixedFujita.EtaleRelativeJacobian

/-!
The proper Kawamata–Viehweg statements from the projective one, and F1 from the projective
statement (step 10, R0′).

* On a smooth variety the identity model has trivial relative Jacobian, so its crepant boundary
  is `D − d (K_T + div f)` (`crepantBoundaryCartier_id`). For a simple normal crossing family
  `E_k` and `a_k < m` the pair `(T, Σ (a_k/m) E_k)`, i.e. `(c_T, 1, m, m K_T + Σ a_k E_k)`, is
  therefore klt (the one-SNC-model criterion `logPairIsKlt_of_crepant_snc_model` on the identity
  model, `snc_logPairIsKlt`) and has effective
  boundary (`snc_logPairBoundaryEffective`).
* With check 468, `KawamataViehwegVanishingSNC K n` follows from the projective statement
  (`kawamataViehwegVanishingSNC_of_projective`); with "big plus nef is big" on proper normal
  varieties in positive dimension and Grothendieck vanishing in dimension zero, so does the sum
  form (`kawamataViehwegVanishingSNCSum_of_projective`).
* Hence **F1 follows from the projective Kawamata–Viehweg statement**
  (`mixedFujitaFreeness_of_projectiveKV`); the 78 modules carrying the proper statements are
  unchanged.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Identity

variable {K : Type u} [Field K] {n : ℕ} {T : Scheme.{u}} [IsIntegral T]
  [T.Over (Spec (CommRingCat.of K))]

/-- The function-field algebra map of the identity is the identity. -/
theorem dominantFunctionFieldAlgHom_id :
    dominantFunctionFieldAlgHom (K := K) (𝟙 T) = AlgHom.id K T.functionField := by
  apply AlgHom.ext
  intro x
  change (dominantFunctionFieldMap (𝟙 T)).hom x = x
  rw [dominantFunctionFieldMap_id]
  rfl

/-- The relative Jacobian of the identity in one chart is `1`. -/
theorem chartRelativeJacobianDet_id (c : EtaleChart K T n) :
    chartRelativeJacobianDet (𝟙 T) c c = 1 := by
  unfold chartRelativeJacobianDet
  rw [dominantFunctionFieldAlgHom_id, etaleRelativeJacobian_id_det _ _
    (etaleChartFunctionFieldCoords_formallyEtale c) (etaleChartFunctionFieldCoords_formallyEtale c),
    Module.Basis.det_self]

/-- The pulled form coefficient along the identity in one chart is the form coefficient. -/
theorem crepantPullbackFormUnit_id (c : EtaleChart K T n) (f : T.functionFieldˣ) :
    crepantPullbackFormUnit (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) c f c = f := by
  apply Units.ext
  simp only [crepantPullbackFormUnit, Units.val_mul, Units.coe_map, IsUnit.unit_spec,
    chartRelativeJacobianDet_id, mul_one]
  rw [dominantFunctionFieldMap_id]
  rfl

variable [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

theorem pullbackFormDivisor_id (c : EtaleChart K T n) (f : T.functionFieldˣ) :
    pullbackFormDivisor (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) c f c
        etaleCharts_cover =
      smoothCanonicalDivisor c + principalCartierDivisor T f := by
  change canonicalDivisor n c etaleCharts_cover + principalCartierDivisor T
    (crepantPullbackFormUnit (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) c f c) = _
  rw [crepantPullbackFormUnit_id]
  rfl

/-- **The crepant boundary of the identity model** is `D − d (K_T + div f)`. -/
theorem crepantBoundaryCartier_id (c : EtaleChart K T n) (f : T.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor T) :
    crepantBoundaryCartier (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) c f d D c
        etaleCharts_cover =
      D - d • (smoothCanonicalDivisor c + principalCartierDivisor T f) := by
  unfold crepantBoundaryCartier
  rw [cartierPullback_id, pullbackFormDivisor_id]

variable [IsLocallyNoetherian T]

/-- **A simple normal crossing boundary with coefficients `a_k / m < 1` is klt.** -/
theorem snc_logPairIsKlt (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ k, Order.coheight (ξ k) = 1)
    (hsnc : IsSNCFamily K n ξ) (E : Fin r → CartierDivisor T)
    (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξ k then 1 else 0)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin r → ℕ) (ha : ∀ k, a k < m) :
    LogPairIsKlt cT 1 m (m • smoothCanonicalDivisor cT + ∑ k, a k • E k) := by
  have hb : crepantBoundaryCartier (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) cT 1 m
      (m • smoothCanonicalDivisor cT + ∑ k, a k • E k) cT etaleCharts_cover = ∑ k, a k • E k := by
    rw [crepantBoundaryCartier_id, principalCartierDivisor_one, add_zero]
    abel
  refine logPairIsKlt_of_crepant_snc_model (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T))
    cT 1 m hm _ cT ξ hinj hξ hsnc ?_ ?_
  · intro t ht
    rw [hb, cartierCoefficient_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : ¬((t : T) = ξ k) := fun h => ht ⟨k, h.symm⟩
    rw [cartierCoefficient_nsmul, hEc k t]
    simp [hk]
  · intro i
    rw [hb, cartierCoefficient_sum, Finset.sum_eq_single i]
    · rw [cartierCoefficient_nsmul, hEc i ⟨ξ i, hξ i⟩]
      simpa using (show ((a i : ℕ) : ℤ) < m by exact_mod_cast ha i)
    · intro k _ hki
      have hk : ¬(ξ i = ξ k) := fun h => hki (hinj h).symm
      rw [cartierCoefficient_nsmul, hEc k ⟨ξ i, hξ i⟩]
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- **A simple normal crossing boundary with nonnegative coefficients is effective.** -/
theorem snc_logPairBoundaryEffective (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (E : Fin r → CartierDivisor T)
    (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξ k then 1 else 0)
    (m : ℕ) (a : Fin r → ℕ) :
    LogPairBoundaryEffective cT 1 m (m • smoothCanonicalDivisor cT + ∑ k, a k • E k) := by
  intro c x hx hcx
  have h0 := smooth_logPairBoundaryEffective_zero cT 1 m c x hx hcx
  rw [principalCartierDivisor_one, add_zero] at h0
  have hG : 0 ≤ cartierCoefficient (∑ k, a k • E k) x := by
    rw [cartierCoefficient_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [cartierCoefficient_nsmul, hEc k ⟨x, hcx⟩]
    split_ifs <;> positivity
  rw [cartierCoefficient_add]
  linarith

end Identity

/-- **The Kawamata–Viehweg statement on smooth proper varieties from the projective one.** -/
theorem kawamataViehwegVanishingSNC_of_projective (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (hKV : KawamataViehwegVanishingSNCProjective K n) :
    KawamataViehwegVanishingSNC K n := by
  intro T _ _ _ _ _ cT r ξ hinj hξ hsnc E hEc Q m hm a ha hnef hbig
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcov : CodimOneChartCovered n K T := fun x _ =>
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top x)
  have hD : m • Q - (m • smoothCanonicalDivisor cT + ∑ k, a k • E k) =
      m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k := by
    rw [nsmul_sub]
    abel
  refine klt_adjoint_H1_vanishing_of_projective_KV K hKV hnorm hcov cT 1 m hm _
    (snc_logPairBoundaryEffective cT ξ E hEc m a) (snc_logPairIsKlt cT ξ hinj hξ hsnc E hEc m hm a ha)
    Q ?_ ?_
  · rw [hD]
    exact hnef
  · rw [hD]
    exact hbig

/-- **The sum form of the Kawamata–Viehweg statement from the projective one.** -/
theorem kawamataViehwegVanishingSNCSum_of_projective (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (hKV : KawamataViehwegVanishingSNCProjective K n) :
    KawamataViehwegVanishingSNCSum K n := by
  intro T _ _ _ _ _ cT r ξ hinj hξ hsnc E hEc Q m hm a ha D₁ D₂ heq hnef₁ hbig₁ hnef₂
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := properOverField_scheme_isNoetherian (K := K) (X := T)
    have hdim : topologicalKrullDim T ≤ ((0 : ℕ) : WithBot ℕ∞) :=
      (etaleChart_topologicalKrullDim cT).le
    have : Subsingleton (Q.sheaf.H 1) :=
      moduleCohomology_subsingleton_of_topologicalKrullDim_le Q.sheaf hdim 1 (by norm_num)
    exact (sgaCohomologyLinearEquiv Q.sheaf 1).symm.toEquiv.subsingleton
  · let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
      fun t => smooth_stalk_isIntegrallyClosed (K := K) t
    refine kawamataViehwegVanishingSNC_of_projective K hKV T cT r ξ hinj hξ hsnc E hEc Q m hm a ha
      ?_ ?_
    · rw [heq]
      exact cartierIsNef_add hnef₁ hnef₂
    · rw [heq]
      exact proper_normal_cartierIsBig_add_of_isNef K n (etaleChart_topologicalKrullDim cT) hn
        hnorm D₁ D₂ hbig₁ hnef₂

/-- **F1 from the projective Kawamata–Viehweg statement.** -/
theorem mixedFujitaFreeness_of_projectiveKV
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCProjective K n) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum fun K _ _ _ n =>
    kawamataViehwegVanishingSNCSum_of_projective K (hKV K n)

end MixedFujita
