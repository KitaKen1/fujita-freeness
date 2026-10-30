/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DominatingEffectiveCutComponent
public import MixedFujita.HyperplanePowerSemiampleBridge
public import MixedFujita.HyperplanePowerCutNonempty
public import MixedFujita.SemiamplePositiveClosedQuotient
public import MixedFujita.MixedAmpleCartierIntersection
public import MixedFujita.ProjectiveCartierPullbackDictionary
public import MixedFujita.CartierNumericalDimension

/-! 実基底次元帰納による元ample引き戻しの基底次元混合冪の厳密正値性。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The mixed coefficient of a dominant ample pullback is strictly
positive THROUGH the base dimension. All actual cuts and positive closed
quotients are constructed internally, by induction on the base dimension. -/
theorem proper_dominant_hyperplanePower_pullback_mixed_positive
    (K : Type u) [Field K] [Infinite K] (d : ℕ) :
    ∀ (X B : Scheme.{u}) [IsIntegral X] [IsIntegral B]
      [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
      [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
      (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
      (H : CartierDivisor B) (D : CartierDivisor X)
      (hH : CartierHasHyperplanePower K H)
      (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf)
      (A : List (CartierDivisor X)) (hA : ∀ J ∈ A, CartierHasHyperplanePower K J),
      topologicalKrullDim X = (d + A.length : ℕ) → topologicalKrullDim B = d →
      0 < cartierMixedEulerDifference K (List.replicate d D ++ A) 0 := by
  induction d with
  | zero =>
    intro X B _ _ _ _ _ _ p _ _ _ H D hH a A hA hX hB
    simp only [List.replicate_zero, List.nil_append]
    cases A with
    | nil =>
      rw [← cartierPulledModuleMixedEulerDifference_id_unit,
        cartierPulledModuleMixedEulerDifference_empty_zero_unit]
      exact proper_zeroDimensional_unitEulerChar_positive K (by simpa using hX.le) inferInstance
    | cons J A =>
      exact proper_hyperplanePowers_mixedEuler_positive K A.length X
        (by simpa only [zero_add, List.length_cons] using hX) (J :: A) rfl hA
  | succ d ih =>
    intro X B _ _ _ _ _ _ p _ _ _ H D hH a A hA hX hB
    obtain ⟨q, hq, G, hG, ⟨b⟩⟩ := hyperplanePower_exists_effective_multiple_iso K H hH
    have hne := proper_hyperplanePower_effective_multiple_cut_nonempty K d hB H hH G hG q hq b
    let F := cartierPullback p G
    have hF : F.IsEffective := cartierPullback_isEffective p G hG
    let I := effectiveCartierIdealSheaf F hF
    let W := I.subscheme
    let jW : W ⟶ X := I.subschemeι
    let : W.Over (Spec (CommRingCat.of K)) := ⟨jW ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : jW.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (W ↘ Spec (CommRingCat.of K)) := by
      change IsProper (jW ≫ (X ↘ Spec (CommRingCat.of K)))
      infer_instance
    have hX' : topologicalKrullDim X = ((d + A.length) + 1 : ℕ) := by
      simpa [add_assoc, add_comm, add_left_comm] using hX
    obtain ⟨T, C, i, j, r, hT, hC, hi, hj, hr, hdimT, hdimC, hfac⟩ :=
      proper_effectiveCut_exists_dominating_expected_component K p (d + A.length) d hX' hB G hG hne
    let := hT
    let := hC
    let := hi
    let := hj
    let := hr
    let : T.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (W ↘ Spec (CommRingCat.of K))⟩
    let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
      change IsProper (i ≫ (W ↘ Spec (CommRingCat.of K)))
      infer_instance
    let : C.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (B ↘ Spec (CommRingCat.of K))⟩
    let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (C ↘ Spec (CommRingCat.of K)) := by
      change IsProper (j ≫ (B ↘ Spec (CommRingCat.of K)))
      infer_instance
    let t : T ⟶ X := i ≫ jW
    let : t.IsOver (Spec (CommRingCat.of K)) := inferInstance
    let : r.IsOver (Spec (CommRingCat.of K)) := ⟨by
      change r ≫ (j ≫ (B ↘ Spec (CommRingCat.of K))) = i ≫ (jW ≫ (X ↘ Spec (CommRingCat.of K)))
      rw [← Category.assoc, hfac]
      simp only [HomIsOver.comp_over]⟩
    let : IsProper (r ≫ (C ↘ Spec (CommRingCat.of K))) := by
      rw [HomIsOver.comp_over]
      infer_instance
    let : IsProper r := IsProper.of_comp r (C ↘ Spec (CommRingCat.of K))
    obtain ⟨HC, ⟨aHC⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor H j
    have hHC : CartierHasHyperplanePower K HC :=
      cartierHasHyperplanePower_of_closed_representative K j H HC aHC hH
    obtain ⟨DT, ⟨aDT⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D t
    obtain ⟨AT, hAT⟩ := exists_cartier_direction_representations t A
    have hATpower := hyperplanePower_list_of_closed_representatives K t hAT hA
    let aTD : (Scheme.Modules.pullback r).obj HC.sheaf ≅ DT.sheaf :=
      (Scheme.Modules.pullback r).mapIso aHC.symm ≪≫
        (Scheme.Modules.pullbackCompIso' r j (t ≫ p) hfac H.sheaf).symm ≪≫
        Scheme.Modules.pullbackCompIso' t p (t ≫ p) rfl H.sheaf ≪≫
        (Scheme.Modules.pullback t).mapIso a ≪≫ aDT
    have hposT := ih T C r HC DT hHC aTD AT hATpower
      (by simpa only [hAT.length_eq] using hdimT) hdimC
    have hrep : ∀ m : ℕ, List.Forall₂
        (fun H J => Nonempty ((Scheme.Modules.pullback t).obj H.sheaf ≅ J.sheaf))
        (List.replicate m D) (List.replicate m DT) := by
      intro m
      induction m with
      | zero => exact .nil
      | succ m hm => exact .cons ⟨aDT⟩ hm
    let L := List.replicate d D ++ A
    have hpos : 0 < cartierPulledModuleMixedEulerDifference K t (CohomologyAux.unitModule T) L 0 := by
      rw [cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K t
        (List.rel_append (hrep d) hAT) 0 0
        ((Scheme.Modules.pullback t).mapIso (cartierZeroSheafIso X) ≪≫
          Scheme.Modules.pullbackObjUnitIso t ≪≫ (cartierZeroSheafIso T).symm)]
      exact hposT
    have hDsem := cartierSemiample_of_pullback_representative p H D a (cartierHasHyperplanePower_semiample K H hH)
    have hLsem : ∀ J ∈ L, ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • J) := by
      intro J hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · exact (List.mem_replicate.mp hJ).2 ▸ hDsem
      · exact cartierHasHyperplanePower_semiample K J (hA J hJ)
    have hlenL : L.length = d + A.length := by simp only [L, List.length_append, List.length_replicate]
    have hdimW : topologicalKrullDim W ≤ L.length := by
      rw [hlenL]
      exact effectiveCartierCut_topologicalKrullDim_le F hF (d + A.length) hX'.le
    have hposW := proper_semiample_unit_mixed_positive_of_closed_quotient K jW L hdimW hLsem i hpos
    let aF : (q • D).sheaf ≅ F.sheaf :=
      (cartierPullbackGradedIso H p D a q).symm ≪≫
        (Scheme.Modules.pullback p).mapIso b ≪≫
        projectiveCartierPullbackIso (cartierHasHyperplanePower_exists_ample K H hH) p G
    have hcut := proper_cartierMixedIntersection_scaled_effective_cut K L D F hF q aF
      (by rw [hlenL]; simpa using hX')
    change (q : ℤ) * cartierMixedEulerDifference K (List.replicate (d + 1) D ++ A) 0 =
      cartierPulledModuleMixedEulerDifference K jW (CohomologyAux.unitModule W) L 0 at hcut
    have hprod : 0 < (q : ℤ) * cartierMixedEulerDifference K (List.replicate (d + 1) D ++ A) 0 :=
      hcut.symm ▸ hposW
    exact (mul_pos_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hprod


/-- The ORIGINAL base-dimensional mixed power of an ORIGINAL ample
pullback is positive, in arbitrary ambient dimension over any infinite field. -/
theorem proper_dominant_ample_pullback_top_mixedPower_positive
    (K : Type u) [Field K] [Infinite K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hX : topologicalKrullDim X = n) (d : ℕ) (hB : topologicalKrullDim B = d) (hdn : d ≤ n)
    (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor B) (D J : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (hJ : CartierIsAmpleProj K J)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf) :
    0 < cartierMixedPowerIntersection K n hX D J ⟨d, by omega⟩ := by
  exact proper_dominant_hyperplanePower_pullback_mixed_positive K d X B p H D
    (cartierHasHyperplanePower_of_isAmpleProj K H hH) a (List.replicate (n - d) J)
    (fun L hL => (List.mem_replicate.mp hL).2 ▸ cartierHasHyperplanePower_of_isAmpleProj K J hJ)
    (by simpa only [List.length_replicate, Nat.add_sub_of_le hdn] using hX) hB

end MixedFujita
