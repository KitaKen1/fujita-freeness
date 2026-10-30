/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DominantAmplePullbackMixedPositive
public import MixedFujita.CartierNumericalDimensionPullbackBound
public import MixedFujita.LowIitakaNumericalDimensionDictionary
public import MixedFujita.NormalSteinIitakaDescent

/-! 正常射影源の全semiample因子・全飯高次元で元ν=κと指数の内部存在。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- ORIGINAL numerical dimension equals the ACTUAL base dimension for
an ample pullback. Neither a positive mixed coefficient nor a quotient is an input. -/
theorem cartierNumericalDimension_eq_base_dimension_of_ample_pullback
    (K : Type u) [Field K] [Infinite K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hX : topologicalKrullDim X = n) (d : ℕ) (hB : topologicalKrullDim B = d) (hdn : d ≤ n)
    (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor B) (D J : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (hJ : CartierIsAmpleProj K J)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf) :
    cartierNumericalDimension K n hX D J = d := by
  apply le_antisymm (cartierNumericalDimension_le_base_dimension_of_pullback K n hX d hB.le p H D J a)
  have hpos := proper_dominant_ample_pullback_top_mixedPower_positive K n hX d hB hdn p H D J hH hJ a
  exact Finset.le_sup (f := Fin.val)
    (show (⟨d, by omega⟩ : Fin (n + 1)) ∈ ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun k => 0 < cartierMixedPowerIntersection K n hX D J k)) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)


/-- A positive multiple of the ORIGINAL divisor may be the ample
pullback; exact original numerical scaling invariance removes that multiple. -/
theorem cartierNumericalDimension_eq_base_dimension_of_multiple_ample_pullback
    (K : Type u) [Field K] [Infinite K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hX : topologicalKrullDim X = n) (d : ℕ) (hB : topologicalKrullDim B = d) (hdn : d ≤ n)
    (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor B) (D J : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (hJ : CartierIsAmpleProj K J)
    (q : ℕ) (hq : 0 < q) (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ (q • D).sheaf) :
    cartierNumericalDimension K n hX D J = d := by
  have h := cartierNumericalDimension_eq_base_dimension_of_ample_pullback K n hX d hB hdn p H (q • D) J hH hJ a
  rwa [cartierNumericalDimension_nsmul K n hX D J q hq] at h


/-- The ORIGINAL mixed-intersection numerical dimension equals the
ORIGINAL Iitaka exponent for EVERY semiample divisor on a normal projective
source. All intermediate exponents are covered; characteristic zero is unnecessary. -/
theorem proper_semiample_cartierNumericalDimension_eq_iitaka
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) :
    cartierNumericalDimension K n hdim D J = k := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hkn := proper_cartierIitakaDimension_le_dim K n hdim J hJ D k hkappa
  obtain ⟨q, hq, hgen⟩ := hD
  have hkq : CartierIitakaDimension K (q • D) k :=
    (cartierIitakaDimension_nsmul_iff_of_ample_ambient hdim hn hJ D hq k).mp hkappa
  have hfree : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → CartierIsGloballyGenerated (t • (q • D)) :=
    ⟨0, fun t _ => cartierIsGloballyGenerated_nsmul (q • D) hgen t⟩
  obtain ⟨B, hB, hBN, hBO, hBft, p, hpdom, hpo, H, f, hp, hpropB, hconn,
      hdimB, hnormB, hcovB, happ, hH, hEq⟩ :=
    eventuallyGloballyGenerated_exists_normal_ample_cartier_contraction
      hdim hn hJ (q • D) hfree hnorm hkq
  let := hB
  let := hBN
  let := hBO
  let := hBft
  let := hpdom
  let := hpo
  let := hp
  let := hpropB
  let a : (Scheme.Modules.pullback p).obj H.sheaf ≅ (q • D).sheaf :=
    projectiveCartierPullbackIso ⟨H, hH⟩ p H ≪≫
      (cartierSheafPrincipalShiftIso (cartierPullback p H) f).symm ≪≫
        eqToIso (congrArg CartierDivisor.sheaf hEq.symm)
  exact cartierNumericalDimension_eq_base_dimension_of_multiple_ample_pullback K n hdim k hdimB hkn
    p H D J hH hJ q hq a


/-- The original Iitaka predicate holds AT the original numerical
dimension for every original semiample divisor in the full projective scope. -/
theorem proper_semiample_iitaka_at_cartierNumericalDimension
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) :
    CartierIitakaDimension K D (cartierNumericalDimension K n hdim D J) := by
  rw [proper_semiample_cartierNumericalDimension_eq_iitaka K n hdim hn hnorm D J hJ hD k hkappa]
  exact hkappa


/-- The FULL original semiample numerical/Iitaka dictionary without
any supplied Iitaka exponent or growth premise: the actual original
numerical dimension itself satisfies the original Iitaka predicate. -/
theorem proper_semiample_cartierIitakaDimension_numericalDimension
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    CartierIitakaDimension K D (cartierNumericalDimension K n hdim D J) := by
  obtain ⟨q, hq, hgen⟩ := hD
  obtain ⟨k, hkq⟩ := eventuallyGloballyGenerated_exists_iitakaDimension_of_normal_projective
    hdim hn hJ (q • D) ⟨0, fun t _ => cartierIsGloballyGenerated_nsmul (q • D) hgen t⟩ hnorm
  have hk : CartierIitakaDimension K D k :=
    (cartierIitakaDimension_nsmul_iff_of_ample_ambient hdim hn hJ D hq k).mpr hkq
  exact proper_semiample_iitaka_at_cartierNumericalDimension K n hdim hn hnorm D J hJ
    ⟨q, hq, hgen⟩ k hk

end MixedFujita
