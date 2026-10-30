/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSmoothProjectiveAmpleModel
public import MixedFujita.BirationalActualCartierBigness
public import MixedFujita.NefAmpleApplications
public import MixedFujita.ZeroDimensionalCartierFreeness

/-! projectivity不要のnormal proper big＋nefと元全次元Statement。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Big plus nef is big on ANY proper normal positive-dimensional source.
Chow and resolution construct the projective source internally; no projectivity
or ample Cartier divisor is assumed on the original target. -/
theorem proper_normal_cartierIsBig_add_of_isNef
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (B N : CartierDivisor X) (hB : CartierIsBig K B) (hN : CartierIsNef K N) :
    CartierIsBig K (B + N) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  obtain ⟨T, hT, hTo, hTN, hTs, p, hdom, hover, hprop, hp, hdimT, A, hA⟩ :=
    proper_integral_exists_smooth_projective_birational_ample_model K n hdim
  let := hT
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdim' : topologicalKrullDim T = topologicalKrullDim X := hdimT.trans hdim.symm
  obtain ⟨BT, ⟨aB⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor B p
  obtain ⟨NT, ⟨aN⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor N p
  have hBT : CartierIsBig K BT :=
    (proper_birational_cartier_representative_isBig_iff K p hp hnorm hnormT hdim' B BT aB).mpr hB
  have hNT : CartierIsNef K NT := cartierIsNef_of_pullback_representative K p N NT aN hN
  have hsum := cartierIsBig_add_of_isNef_on_projective hdimT hn hnormT hA hBT hNT
  let a : (Scheme.Modules.pullback p).obj (B + N).sheaf ≅ (BT + NT).sheaf :=
    (Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso B N).symm ≪≫
      cartierPullbackTensorIso B p N.sheaf ≪≫ tensorIso aB aN ≪≫ cartierTensorSheafIso BT NT
  exact (proper_birational_cartier_representative_isBig_iff
    K p hp hnorm hnormT hdim' (B + N) (BT + NT) a).mp hsum


/-- Every Cartier divisor on a zero-dimensional proper integral source is
big in the original section-growth definition. -/
theorem proper_zeroDimensional_cartierIsBig
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) : CartierIsBig K D := by
  refine ⟨0, by simpa only [Nat.cast_zero] using hdim, 1, by norm_num, ?_⟩
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro m
  let := proper_cartier_sections_finite K (m • D)
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (zeroDimensional_cartier_globallyGenerated hdim (m • D))
  have hpos : 0 < Module.finrank K Γ((m • D).sheaf, ⊤) := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s, hs⟩
  simpa only [pow_zero, one_mul] using (show (1 : ℝ) ≤
    (Module.finrank K Γ((m • D).sheaf, ⊤) : ℝ) by exact_mod_cast hpos)


/-- The ORIGINAL unrestricted-proper big-plus-nef statement holds in every
dimension, including zero; no projectivity assumption is added to its type. -/
theorem bigAddNefStatement_holds
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) : BigAddNefStatement K n := by
  intro T _ _ _ _ _ D₁ D₂ _hnef₁ hbig₁ hnef₂
  have hdim : topologicalKrullDim T = n := by
    let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (CommRingCat.of K))
    obtain ⟨x, _, hx⟩ := (isClosed_univ (X := T)).exists_closed_singleton
      ⟨genericPoint T, Set.mem_univ _⟩
    have hloc := (TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (T ↘ Spec (CommRingCat.of K)) n).mp inferInstance
    exact (TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
      (T ↘ Spec (CommRingCat.of K)) hx).symm.trans (hloc.2 x hx)
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  by_cases hn : n = 0
  · exact proper_zeroDimensional_cartierIsBig K (by simpa only [hn, Nat.cast_zero] using hdim) _
  · exact proper_normal_cartierIsBig_add_of_isNef K n hdim (by omega)
      (fun t => smooth_stalk_isIntegrallyClosed (K := K) t) D₁ D₂ hbig₁ hnef₂

end MixedFujita
