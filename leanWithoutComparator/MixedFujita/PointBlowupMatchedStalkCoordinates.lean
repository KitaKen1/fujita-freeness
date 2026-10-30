/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialMorphismStalkCoordinates

/-! Actual point-blow-up equations at the same stalk of the original blow-up.
The exceptional coordinate is a nonunit whenever the point lies over the centre.
Neither a supplied differential basis nor a supplied coordinate equation is used. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme.Hom
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of K))] {Z : X.IdealSheafData} {x : X}
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

theorem etalePointBlowupChartToGlobal_comp_projection
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n Z x) (k : Fin n) :
    etalePointBlowupChartToGlobal E k ≫ Z.blowUpπ =
      pullback.fst (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt) ≫
        (Z.comap E.U.1.ι).blowUpπ ≫ E.U.1.ι := by
  rw [etalePointBlowupChartToGlobal, Category.assoc, blowUpMap_π]

set_option maxHeartbeats 800000 in
theorem etalePointBlowup_matched_stalk_coordinates
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n Z x)
    (hxZ : x ∈ Z.support) (q : Z.blowUp) (hq : Z.blowUpπ q = x) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] Z.blowUp.presheaf.stalk q),
      τ.toRingHom.FormallyEtale ∧ ¬ IsUnit (τ (MvPolynomial.X k)) ∧
      ∀ i, Z.blowUpπ.stalkMap q
        (X.presheaf.germ E.U.1 (Z.blowUpπ q) (hq.symm ▸ E.mem) (E.v i)) =
        if i = k then τ (MvPolynomial.X k) else τ (MvPolynomial.X i) * τ (MvPolynomial.X k) := by
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  obtain ⟨k, p, rfl⟩ := etalePointBlowupChartToGlobal_covers_fibre E q hq
  let Y := etalePointBlowupChart E k
  let σ := pullback.snd (etalePointBlowupModelMap E)
    (CoordinateSubspace.modelChart K n n k k.isLt)
  let : Y.Over (Spec (.of K)) :=
    ⟨σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))⟩
  let ρ := etalePointBlowupChartToGlobal E k
  have : ρ.IsOver (Spec (.of K)) := ⟨etalePointBlowupChartToGlobal_comp_base E k⟩
  let a := pullback.fst (etalePointBlowupModelMap E)
    (CoordinateSubspace.modelChart K n n k k.isLt) ≫ (Z.comap E.U.1.ι).blowUpπ
  have hμ : a ≫ E.U.1.ι = ρ ≫ Z.blowUpπ :=
    (etalePointBlowupChartToGlobal_comp_projection E k).symm
  obtain ⟨V, hp⟩ := Scheme.IdealSheafData.exists_affineOpens_mem p
  let τY := polynomialStalkAlgHom σ rfl V p hp
  let e := AlgEquiv.ofBijective (schemeStalkMapAlgHom (K := K) ρ p)
    (ConcreteCategory.bijective_of_isIso (ρ.stalkMap p))
  let τ := e.symm.toAlgHom.comp τY
  have hτ : τ.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp
    (polynomialStalkAlgHom_formallyEtale σ rfl V p hp)
    (ringHom_formallyEtale_of_etale e.symm.toRingEquiv.toRingHom
      (RingHom.Etale.of_bijective e.symm.bijective))
  have hcoords (i : Fin n) : ρ.stalkMap p
      (Z.blowUpπ.stalkMap (ρ p) (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p))
        (hq.symm ▸ E.mem) (E.v i))) = τY (polynomialPointBlowupMap k (MvPolynomial.X i)) := by
    have h := germ_sectionsHom_toAffineSpace (X ↘ Spec (.of K)) E.U.1 E.v a V.1 p hp i
    have hg : (a ≫ E.U.1.ι).stalkMap p
        (X.presheaf.germ E.U.1 ((a ≫ E.U.1.ι) p) (a p).2 (E.v i)) =
        ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p)
          (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p)) (hq.symm ▸ E.mem) (E.v i))) := by
      exact (stalkMap_germ_congr hμ E.U.1 p (a p).2 (hq.symm ▸ E.mem) (E.v i)).trans
        (congrArg (fun g => g (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p))
          (hq.symm ▸ E.mem) (E.v i))) (Scheme.Hom.stalkMap_comp ρ Z.blowUpπ p))
    rw [hg] at h
    rw [show a ≫ toAffineSpace (X ↘ Spec (.of K)) E.U.1 E.v =
      σ ≫ Spec.map (CommRingCat.ofHom (polynomialPointBlowupMap (K := K) k).toRingHom) from
        etalePointBlowupChart_projection E k, sectionsHom_comp_specMap] at h
    exact h.symm
  let J := ((Z.comap E.U.1.ι).comap (Z.comap E.U.1.ι).blowUpπ).comap
    (pullback.fst (etalePointBlowupModelMap E) (CoordinateSubspace.modelChart K n n k k.isLt))
  have hJ : J = Z.comap (ρ ≫ Z.blowUpπ) := by
    dsimp [J]
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hμ]
  have hpJ : p ∈ J.support := by
    rw [hJ, Scheme.IdealSheafData.support_comap]
    change Z.blowUpπ (ρ p) ∈ Z.support
    rw [hq]
    exact hxZ
  have hnonunitY : ¬ IsUnit (τY (MvPolynomial.X k)) := by
    have hzero := (J.mem_support_iff_of_mem (U := V) hp).mp hpJ
    have hmem : sectionsHom σ V.1 (MvPolynomial.X k) ∈ J.ideal V := by
      rw [show J.ideal V = _ from etalePointBlowupChart_exceptionalIdeal_affine E k V]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hn := (Y.mem_zeroLocus_iff _ p).mp hzero _ hmem
    exact fun hu => hn ((Y.mem_basicOpen _ p hp).mpr hu)
  have heτ (g : MvPolynomial (Fin n) K) : e (τ g) = τY g := by
    change e (e.symm (τY g)) = τY g
    exact e.apply_symm_apply _
  refine ⟨k, τ, hτ, ?_, ?_⟩
  · intro hu
    apply hnonunitY
    have he := hu.map e.toRingHom
    change IsUnit (e (τ (MvPolynomial.X k))) at he
    rwa [heτ] at he
  · intro i
    apply e.injective
    by_cases hi : i = k
    · rw [ite_eq_left hi, heτ]
      change ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p) _) = _
      simpa only [hi, polynomialPointBlowupMap_X_self] using hcoords i
    · rw [ite_eq_right hi, map_mul, heτ, heτ]
      change ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p) _) = _
      simpa only [polynomialPointBlowupMap_X_other k i hi, map_mul] using hcoords i

end MixedFujita
