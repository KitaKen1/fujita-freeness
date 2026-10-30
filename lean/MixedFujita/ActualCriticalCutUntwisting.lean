/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCutPushforwardQuotient
public import MixedFujita.NormalCartierPowerRoot
public import MixedFujita.EffectiveCartierIdealSheaf

/-! 正常Cartier格子の交わりによる実未捻り臨界切断の単射・順像同型。 check-272：高次ample捻りの実大域切断全射と有限生成から、対象層だけの連接性で実層写像の全射性を検出。実射影公式の自然性を写像で証明し、引き戻したample捻りの全大H1消滅からproper順像の商全射・短完全性を内部構成。通常の絶対H1版KVを明示した入力として、元の孤立lc中心から実SNCモデル・例外roundup E・非零臨界Cartier切断Sを内部構成し、内在商 O(E)/O(E-S) の順像を正確な被約中心構造層と、元の単位写像を保って同定。さらに正常源上のCartier格子の交わりをDVR次数で制御し、共通成分のないE/Sについて、実際の未捻り切断Sの構造層から内在商への標準単射を構成。通常KVによる商全射性でこの写像の順像が同型となるため、元の孤立lc中心について実際の未捻り臨界切断の構造層順像＝被約中心構造層まで、モデル・相対消滅・中心正規性を追加仮定せず接続。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- On a normal source, a regular function in O(E-S) already lies in
O(-S) when E has zero coefficient on every component of S. -/
theorem normal_regular_mem_negative_of_mem_disjoint_subcut
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hS : S.IsEffective)
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0)
    (U : T.Opens) [Nonempty U] (a : Γ(T, U))
    (ha : Scheme.Modules.Hom.app (toRationalFunctions T) U a ∈ (E - S).sections U) :
    Scheme.Modules.Hom.app (toRationalFunctions T) U a ∈ (-S).sections U := by
  let : ∀ t : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (t : T)) :=
    fun t => by let := hnorm (t : T); exact normal_codimensionOne_stalk_DVR t
  let z := T.germToFunctionField U a
  have heq : Scheme.Modules.Hom.app (toRationalFunctions T) U a =
      (rationalFunctionsEquiv (X := T) U).symm z := by
    apply (rationalFunctionsEquiv (X := T) U).injective
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, LinearEquiv.apply_symm_apply]
  rw [heq] at ha ⊢
  apply (normal_cartier_rational_mem_sections_iff_prime_orders hnorm (-S) U z).mpr
  rcases (normal_cartier_rational_mem_sections_iff_prime_orders hnorm (E - S) U z).mp ha with hz | ho
  · exact Or.inl hz
  · right
    intro t ht
    have hn := Scheme.ord_germToFunctionField_nonneg a ht
    have hs := cartierCoefficient_nonneg_of_isEffective S hS (t : T)
    by_cases htS : cartierCoefficient S (t : T) = 0
    · simpa only [cartierCoefficient_neg, htS, neg_zero] using hn
    · have he := hES t (by omega)
      have hp := ho t ht
      simpa only [cartierCoefficient_sub, he, zero_sub, cartierCoefficient_neg] using hp


/-- The regular unit map to O(E) kills the actual negative-S ideal after
passing to the intrinsic Cartier cut quotient. All maps are canonical. -/
theorem negativeCartierToUnit_effective_cut_cokernel_zero
    {T : Scheme.{u}} [IsIntegral T] (E S : CartierDivisor T)
    (hE : E.IsEffective) (hS : S.IsEffective) :
    negativeCartierToUnit T S hS ≫ E.unitToSheaf hE ≫
      cokernel.π (cartierEffectiveInclusion E S hS) = 0 := by
  have hle (U : T.Opens) : (-S).sections U ≤ (E - S).sections U := by
    have h := cartier_sections_sub_le (E - S) E hE U
    have he : (E - S) - E = -S := by abel
    rwa [he] at h
  let l : (-S).sheaf ⟶ (E - S).sheaf := CartierDivisor.sheafLift _ (-S).sheafι
    (fun U s => hle U ((-S).sheafι_app_mem U s))
  have hl : l ≫ (E - S).sheafι = (-S).sheafι := CartierDivisor.sheafLift_ι _ _ _
  have hc : negativeCartierToUnit T S hS ≫ E.unitToSheaf hE =
      l ≫ cartierEffectiveInclusion E S hS := by
    apply (cancel_mono E.sheafι).mp
    rw [Category.assoc, E.unitToSheaf_ι, negativeCartierToUnit_toRationalFunctions,
      Category.assoc, cartierEffectiveInclusion_ι, hl]
  rw [← Category.assoc, hc, Category.assoc, cokernel.condition, comp_zero]


/-- The ACTUAL structure module of the effective cut maps canonically into
its intrinsic E-twisted Cartier quotient. -/
noncomputable def effectiveCartierCutToIntrinsicQuotient
    {T : Scheme.{u}} [IsIntegral T] (E S : CartierDivisor T)
    (hE : E.IsEffective) (hS : S.IsEffective) :
    (Scheme.Modules.pushforward (effectiveCartierIdealSheaf S hS).subschemeι).obj
      (CohomologyAux.unitModule (effectiveCartierIdealSheaf S hS).subscheme) ⟶
        cokernel (cartierEffectiveInclusion E S hS) :=
  (CokernelCofork.IsColimit.desc' (effectiveCartierQuotientShortComplex_shortExact S hS).gIsCokernel
    (E.unitToSheaf hE ≫ cokernel.π (cartierEffectiveInclusion E S hS))
    (negativeCartierToUnit_effective_cut_cokernel_zero E S hE hS)).val


/-- The preceding map carries the actual cut unit quotient to the
intrinsic Cartier quotient of the actual effective-divisor unit map. -/
theorem effectiveCartierCutToIntrinsicQuotient_unit
    {T : Scheme.{u}} [IsIntegral T] (E S : CartierDivisor T)
    (hE : E.IsEffective) (hS : S.IsEffective) :
    schemeUnitToPushforwardUnit (effectiveCartierIdealSheaf S hS).subschemeι ≫
      effectiveCartierCutToIntrinsicQuotient E S hE hS =
        E.unitToSheaf hE ≫ cokernel.π (cartierEffectiveInclusion E S hS) :=
  (CokernelCofork.IsColimit.desc' (effectiveCartierQuotientShortComplex_shortExact S hS).gIsCokernel
    (E.unitToSheaf hE ≫ cokernel.π (cartierEffectiveInclusion E S hS))
    (negativeCartierToUnit_effective_cut_cokernel_zero E S hE hS)).property


/-- Removing the exceptional twist is injective on the ACTUAL cut when
the two effective Cartier divisors have no common component. The cut need
not be integral, normal or reduced. -/
theorem effectiveCartierCutToIntrinsicQuotient_mono
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0) :
    Mono (effectiveCartierCutToIntrinsicQuotient E S hE hS) := by
  let I := effectiveCartierIdealSheaf S hS
  let f := effectiveCartierCutToIntrinsicQuotient E S hE hS
  apply moduleHom_mono_of_affine_app_injective f
  intro U
  have hzero : ∀ x, Scheme.Modules.Hom.app f U.1 x = 0 → x = 0 := by
    intro x hx
    by_cases hU : Nonempty U.1
    · let := hU
      obtain ⟨a, ha⟩ := I.subschemeι_app_surjective U x
      have hz : Scheme.Modules.Hom.app (cokernel.π (cartierEffectiveInclusion E S hS)) U.1
          (Scheme.Modules.Hom.app (E.unitToSheaf hE) U.1 a) = 0 := by
        have hc := congrArg (fun g : CohomologyAux.unitModule T ⟶
            cokernel (cartierEffectiveInclusion E S hS) => Scheme.Modules.Hom.app g U.1 a)
          (effectiveCartierCutToIntrinsicQuotient_unit E S hE hS)
        change Scheme.Modules.Hom.app f U.1 (I.subschemeι.app U.1 a) =
          Scheme.Modules.Hom.app (cokernel.π (cartierEffectiveInclusion E S hS)) U.1
            (Scheme.Modules.Hom.app (E.unitToSheaf hE) U.1 a) at hc
        rw [ha, hx] at hc
        exact hc.symm
      obtain ⟨b, hb⟩ := moduleSections_exists_of_app_eq_zero
        (cartierEffectiveInclusion_cokernelSequence_shortExact E S hS) U.1 _ hz
      have hi := congrArg (fun g : (E - S).sheaf ⟶ rationalFunctions T => Scheme.Modules.Hom.app g U.1 b)
        (cartierEffectiveInclusion_ι E S hS)
      have hu := congrArg (fun g : CohomologyAux.unitModule T ⟶ rationalFunctions T =>
          Scheme.Modules.Hom.app g U.1 a) (E.unitToSheaf_ι hE)
      have hrat : Scheme.Modules.Hom.app (E - S).sheafι U.1 b =
          Scheme.Modules.Hom.app (toRationalFunctions T) U.1 a :=
        hi.symm.trans ((congrArg (Scheme.Modules.Hom.app E.sheafι U.1) hb).trans hu)
      have hmem : Scheme.Modules.Hom.app (toRationalFunctions T) U.1 a ∈ (-S).sections U.1 :=
        normal_regular_mem_negative_of_mem_disjoint_subcut hnorm E S hS hES U.1 a
          (hrat ▸ (E - S).sheafι_app_mem U.1 b)
      obtain ⟨c, hc⟩ := (negativeCartierToUnit_range_iff T S hS U.1 a).mpr hmem
      have hzero : Scheme.Modules.Hom.app (schemeUnitToPushforwardUnit I.subschemeι) U.1 a = 0 := by
        rw [← hc]
        change Scheme.Modules.Hom.app
          (negativeCartierToUnit T S hS ≫ schemeUnitToPushforwardUnit I.subschemeι) U.1 c = 0
        have hcomp : negativeCartierToUnit T S hS ≫ schemeUnitToPushforwardUnit I.subschemeι = 0 :=
          (effectiveCartierQuotientShortComplex S hS).zero
        rw [hcomp]
        rfl
      exact ha.symm.trans hzero
    · have hbot : U.1 = ⊥ := (Opens.not_nonempty_iff_eq_bot U.1).mp
        (fun ⟨z, hz⟩ => hU ⟨⟨z, hz⟩⟩)
      let : Subsingleton Γ((Scheme.Modules.pushforward I.subschemeι).obj
          (CohomologyAux.unitModule I.subscheme), U.1) :=
        abelianSheaf_empty_sections_subsingleton
          ((SheafOfModules.toSheaf T.ringCatSheaf).obj
            ((Scheme.Modules.pushforward I.subschemeι).obj (CohomologyAux.unitModule I.subscheme))) hbot
      exact Subsingleton.elim _ _
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by rw [map_sub, hxy, sub_self]))


/-- The canonical comparison commutes with the ACTUAL unit maps after
pushforward, including the originally chosen scheme morphism. -/
theorem effectiveCartierCutToIntrinsicQuotient_pushforward_unit
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (p : T ⟶ X) (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective) :
    schemeUnitToPushforwardUnit p ≫
      (Scheme.Modules.pushforward p).map (schemeUnitToPushforwardUnit (effectiveCartierIdealSheaf S hS).subschemeι) ≫
        (Scheme.Modules.pushforward p).map (effectiveCartierCutToIntrinsicQuotient E S hE hS) =
      effectiveCartierPushforwardUnitMap p E hE ≫
        (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS)) := by
  rw [← Functor.map_comp, effectiveCartierCutToIntrinsicQuotient_unit, Functor.map_comp]
  rfl


/-- The actual untwisted cut and its intrinsic E-twisted quotient have
ISOMORPHIC direct images once the canonical cut quotient sequence is exact.
No center normality or higher-direct-image vanishing is assumed. -/
theorem effectiveCartierCutToIntrinsicQuotient_pushforward_isIso
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0)
    (hpush : ((ShortComplex.cokernelSequence (cartierEffectiveInclusion E S hS)).map
      (Scheme.Modules.pushforward p)).ShortExact) :
    IsIso ((Scheme.Modules.pushforward p).map (effectiveCartierCutToIntrinsicQuotient E S hE hS)) := by
  let : (Scheme.Modules.pushforward p).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  let := effectiveCartierCutToIntrinsicQuotient_mono hnorm E S hE hS hES
  let f := (Scheme.Modules.pushforward p).map (effectiveCartierCutToIntrinsicQuotient E S hE hS)
  let : Mono f := (Scheme.Modules.pushforward p).map_mono _
  let : Epi ((Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS))) := hpush.epi_g
  let u := schemeUnitToPushforwardUnit p ≫
    (Scheme.Modules.pushforward p).map (schemeUnitToPushforwardUnit (effectiveCartierIdealSheaf S hS).subschemeι)
  have he : u ≫ f = effectiveCartierPushforwardUnitMap p E hE ≫
      (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS)) :=
    effectiveCartierCutToIntrinsicQuotient_pushforward_unit p E S hE hS
  have hg : Epi (effectiveCartierPushforwardUnitMap p E hE ≫
      (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS))) := inferInstance
  let : Epi (u ≫ f) := he.symm ▸ hg
  let : Epi f := epi_of_epi u f
  exact isIso_of_mono_of_epi f

end MixedFujita
