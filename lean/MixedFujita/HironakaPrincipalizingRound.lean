/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaBlowUpModels
public import MixedFujita.DominantCartierPullback
public import Hironaka.Resolution.Algebraic.Hir64.MainTheoremI
public import Hironaka.Resolution.Algebraic.Hir64.ComponentwiseCorollaries
public import Hironaka.Scheme.BlowUp.Glue.Product

/-!
Principalization of an ideal sheaf together with a boundary (step 7). Let Y be an integral
regular scheme of finite type and separated over a field K of characteristic zero, Z a closed
subset not containing the generic point and 𝔠 an ideal sheaf whose support lies in Z. Then there
is a succession of blow-ups of Y with centres over Z whose last stage is regular, on which the
inverse image of 𝔠 is invertible and the reduced preimage of Z has only normal crossings.

The same holds for finitely many ideal sheaves at once, and then the last stage dominates the
blow-up of each of them.

Proof. Three rounds, kept as one succession of blow-ups of Y. First blow up 𝔠 (for several ideal
sheaves, one after the other, each time the inverse image of the next one): its inverse image
becomes invertible, and stays invertible along every further blow-up. The blow-up is integral and
is an isomorphism on the stalks off Z; as Y is regular, its singular locus lies over Z. Hironaka's
Main Theorem I gives one more blow-up with centre supported on that singular locus whose result
is regular, hence smooth over K. Hironaka's Corollary 3, applied to the preimage of Z there, gives
a succession with centres over that preimage, regular, on which the reduced preimage of Z has only
normal crossings. All centres lie over Z.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Topology

variable {T : Scheme.{u}} [IsIntegral T]

/-- A closed subset of an integral scheme not containing the generic point is nowhere dense. -/
theorem isNowhereDense_of_isClosed_of_genericPoint_notMem {Z : Set T} (hZ : IsClosed Z)
    (h : genericPoint T ∉ Z) : IsNowhereDense Z := by
  change interior (closure Z) = ∅
  rw [hZ.closure_eq]
  by_contra hne
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hgen : genericPoint T ∈ interior Z :=
    ((genericPoint_spec T).mem_open_set_iff isOpen_interior).mpr ⟨y, Set.mem_univ y, hy⟩
  exact h (interior_subset hgen)

end Topology

section OneBlowUp

variable {Y : Scheme.{u}}

/-- A blow-up is an isomorphism on the stalks at every point not over the support of its
centre. -/
theorem blowUp_isIso_stalkMap_of_notMem_support (D : Y.IdealSheafData) (t : D.blowUp)
    (ht : D.blowUpπ t ∉ (D.support : Set Y)) : IsIso (D.blowUpπ.stalkMap t) := by
  have hiso : IsIso (D.blowUpπ ∣_ D.support.compl) :=
    Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support D
  have h1 : IsIso ((D.blowUpπ ∣_ D.support.compl).stalkMap ⟨t, ht⟩) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap D.blowUpπ D.support.compl ⟨t, ht⟩)).mp h1

/-- The centres of a blow-up followed by a succession of blow-ups lie over a set as soon as the
support of the first centre lies in it and the centres of the succession lie over its
preimage. -/
theorem blowUpSequence_cons_centers_over (D : Y.IdealSheafData)
    (rest : Scheme.BlowUpSequence D.blowUp) (Z : Set Y) (hD : (D.support : Set Y) ⊆ Z)
    (hrest : ∀ (i : Fin rest.length) (z : rest.stage i.castSucc), z ∈ (rest.center i).support →
      rest.stageMap i.castSucc z ∈ D.blowUpπ ⁻¹' Z) :
    ∀ (i : Fin (Scheme.BlowUpSequence.cons Y D rest).length)
      (z : (Scheme.BlowUpSequence.cons Y D rest).stage i.castSucc),
      z ∈ ((Scheme.BlowUpSequence.cons Y D rest).center i).support →
      (Scheme.BlowUpSequence.cons Y D rest).stageMap i.castSucc z ∈ Z
  | ⟨0, _⟩, z, hz => hD hz
  | ⟨j + 1, hj⟩, z, hz => by
    have h := hrest ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z hz
    let w : rest.stage (⟨j, Nat.lt_of_succ_lt_succ hj⟩ : Fin rest.length).castSucc := z
    have h2 : (rest.stageMap (⟨j, Nat.lt_of_succ_lt_succ hj⟩ : Fin rest.length).castSucc ≫
        D.blowUpπ) w ∈ Z := by
      rw [Scheme.Hom.comp_apply]
      exact h
    exact h2

/-- One blow-up, as a succession, has its centre over the support of the centre. -/
theorem blowUpSequence_single_centers_over (D : Y.IdealSheafData) :
    ∀ (i : Fin (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)).length)
      (z : (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)).stage
        i.castSucc),
      z ∈ ((Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)).center
        i).support →
      (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)).stageMap
        i.castSucc z ∈ (D.support : Set Y) :=
  blowUpSequence_cons_centers_over D (Scheme.BlowUpSequence.nil D.blowUp) (D.support : Set Y)
    subset_rfl fun i => absurd i.2 (Nat.not_lt_zero _)

/-- The composite of one blow-up, as a succession, is the blow-up morphism. -/
theorem blowUpSequence_single_composite (D : Y.IdealSheafData) :
    (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)).composite =
      D.blowUpπ :=
  Category.id_comp _

/-- The blow-up of an integral locally Noetherian scheme along a centre whose support does not
contain the generic point is integral. -/
theorem blowUp_isIntegral_of_genericPoint_notMem_support [IsIntegral Y] [IsLocallyNoetherian Y]
    (D : Y.IdealSheafData) (hη : genericPoint Y ∉ (D.support : Set Y)) : IsIntegral D.blowUp :=
  blowUpSequence_isIntegral_last_of_centers_over
    (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)) D.support
    (blowUpSequence_single_centers_over D) hη

/-- The blow-up of an integral scheme along a centre whose support does not contain the generic
point is dominant. -/
theorem blowUp_isDominant_of_genericPoint_notMem_support [IsIntegral Y] (D : Y.IdealSheafData)
    (hη : genericPoint Y ∉ (D.support : Set Y)) : IsDominant D.blowUpπ :=
  blowUpSequence_single_composite D ▸ blowUpSequence_isDominant_of_centers_over
    (Scheme.BlowUpSequence.cons Y D (Scheme.BlowUpSequence.nil D.blowUp)) D.support
    (blowUpSequence_single_centers_over D) hη

/-- The inverse image of an invertible ideal sheaf along a succession of blow-ups is
invertible. -/
theorem blowUpSequence_isInvertible_comap_composite :
    ∀ {Y : Scheme.{u}} (S : Scheme.BlowUpSequence Y) (J : Y.IdealSheafData),
      J.IsInvertible → (J.comap S.composite).IsInvertible
  | _, Scheme.BlowUpSequence.nil Y, J, hJ => by
    change (J.comap (𝟙 Y)).IsInvertible
    rw [Scheme.IdealSheafData.comap_id]
    exact hJ
  | _, Scheme.BlowUpSequence.cons Y D rest, J, hJ => by
    change (J.comap (rest.composite ≫ D.blowUpπ)).IsInvertible
    rw [Scheme.IdealSheafData.comap_comp]
    exact blowUpSequence_isInvertible_comap_composite rest (J.comap D.blowUpπ)
      (Scheme.IdealSheafData.blowUp.isInvertible_comap_of_isInvertible D J hJ)

/-- A round on a blow-up is a round on the base: a succession of blow-ups of the blow-up of D
with centres over the preimage of a set Z containing the support of D, regular last stage,
invertible inverse images of the ideal sheaves of a list and a normal crossing boundary supported
on the preimage of Z, gives such a succession of the base. -/
theorem exists_blowUpSequence_round_of_blowUp (D : Y.IdealSheafData) (Z : Set Y)
    (hD : (D.support : Set Y) ⊆ Z) (l : List Y.IdealSheafData)
    (h : ∃ S : Scheme.BlowUpSequence D.blowUp,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ D.blowUpπ ⁻¹' Z) ∧
      IsRegular S.last ∧
      (∀ J ∈ l, ((J.comap D.blowUpπ).comap S.composite).IsInvertible) ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' (D.blowUpπ ⁻¹' Z)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ Z) ∧
      IsRegular S.last ∧ (∀ J ∈ l, (J.comap S.composite).IsInvertible) ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' Z := by
  obtain ⟨S, hc, hreg, hinv, E, hE, hEs⟩ := h
  refine ⟨Scheme.BlowUpSequence.cons Y D S, blowUpSequence_cons_centers_over D S Z hD hc, hreg,
    fun J hJ => ?_, E, hE, ?_⟩
  · change (J.comap (S.composite ≫ D.blowUpπ)).IsInvertible
    rw [Scheme.IdealSheafData.comap_comp]
    exact hinv J hJ
  · refine hEs.trans (Set.ext fun t => ?_)
    change D.blowUpπ (S.composite t) ∈ Z ↔ (S.composite ≫ D.blowUpπ) t ∈ Z
    rw [Scheme.Hom.comp_apply]

end OneBlowUp

section Rounds

variable {K : Type u} [Field K] [CharZero K]

/-- Hironaka's Corollary 3 for a closed subset: on an integral scheme smooth, of finite type and
separated over a field of characteristic zero there is a succession of blow-ups with centres over
a given closed subset Z not containing the generic point, with regular last stage, on which the
reduced preimage of Z has only normal crossings. -/
theorem exists_blowUpSequence_isSncBoundary_preimage_of_smooth (Y : Scheme.{u}) [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    [Smooth (Y ↘ Spec (CommRingCat.of K))] (Z : Closeds Y)
    (hZη : genericPoint Y ∉ (Z : Set Y)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
      IsRegular S.last ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' (Z : Set Y) := by
  obtain ⟨W, hW⟩ : ∃ W : Y.IdealSheafData, W = Scheme.IdealSheafData.vanishingIdeal Z :=
    ⟨_, rfl⟩
  have hWsupp : (W.support : Set Y) = (Z : Set Y) := by
    rw [hW, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hWnd : IsNowhereDense (W.support : Set Y) := by
    rw [hWsupp]
    exact isNowhereDense_of_isClosed_of_genericPoint_notMem Z.isClosed hZη
  let Yk : AlgScheme K := MorphismProperty.Over.mk ⊤ (Y ↘ Spec (CommRingCat.of K))
    ⟨inferInstance, inferInstance⟩
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨S, -, hreg, hcent, -, hsnc⟩ : ∃ S : Scheme.BlowUpSequence Y,
      (∀ i : Fin S.length, IsRegular (S.center i).subscheme) ∧ IsRegular S.last ∧
      (∀ i : Fin S.length, ∀ x ∈ (S.center i).support,
        S.stageMap i.castSucc x ∈ W.support) ∧
      (W.comap S.composite).radical.IsInvertible ∧
      (W.comap S.composite).radical.IsSncBoundary :=
    @exists_blowUpSequence_isInvertible_isSncBoundary_radical_comap K _ _ Yk hsm W hWnd
  refine ⟨S, ?_, hreg, (W.comap S.composite).radical, hsnc, ?_⟩
  · intro i z hz
    have h := hcent i z hz
    change S.stageMap i.castSucc z ∈ (W.support : Set Y) at h
    rwa [hWsupp] at h
  · ext t
    have h : t ∈ (W.comap S.composite).radical.support ↔
        S.composite t ∈ (W.support : Set Y) := by
      rw [Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.support_comap]
      rfl
    change t ∈ (W.comap S.composite).radical.support ↔ S.composite t ∈ (Z : Set Y)
    rw [h, hWsupp]

/-- The same for an integral scheme of finite type and separated over the field whose singular
locus lies in the closed subset: one blow-up with centre on the singular locus (Hironaka's Main
Theorem I) followed by the succession of Corollary 3. -/
theorem exists_blowUpSequence_isSncBoundary_preimage_of_singularLocus_subset (Y : Scheme.{u})
    [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (Z : Closeds Y) (hZη : genericPoint Y ∉ (Z : Set Y))
    (hsing : Y.singularLocus ⊆ (Z : Set Y)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
      IsRegular S.last ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' (Z : Set Y) := by
  have hYN : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  let Yk : AlgScheme K := MorphismProperty.Over.mk ⊤ (Y ↘ Spec (CommRingCat.of K))
    ⟨inferInstance, inferInstance⟩
  have hYi : IsIntegral Yk.left := ‹IsIntegral Y›
  obtain ⟨D, hsupp, hreg⟩ : ∃ D : Y.IdealSheafData,
      (D.support : Set Y) = Y.singularLocus ∧ IsRegular D.blowUp :=
    exists_support_eq_singularLocus_isRegular_blowUp Yk
  have hD : (D.support : Set Y) ⊆ (Z : Set Y) := by
    rw [hsupp]
    exact hsing
  have hηD : genericPoint Y ∉ (D.support : Set Y) := fun h => hZη (hD h)
  have hint : IsIntegral D.blowUp := blowUp_isIntegral_of_genericPoint_notMem_support D hηD
  have hdom : IsDominant D.blowUpπ := blowUp_isDominant_of_genericPoint_notMem_support D hηD
  have hprop : IsProper D.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π D
  have hft : LocallyOfFiniteType (D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
  have hqc : QuasiCompact (D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
  have hsep : IsSeparated (D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
  have hsm : Smooth (D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) :=
    (Scheme.smooth_iff_isRegular (D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K)))).mpr hreg
  have hZ'η : genericPoint D.blowUp ∉ D.blowUpπ ⁻¹' (Z : Set Y) := by
    change D.blowUpπ (genericPoint D.blowUp) ∉ (Z : Set Y)
    rw [dominant_map_genericPoint]
    exact hZη
  obtain ⟨S, hc, hreg', -, E⟩ := exists_blowUpSequence_round_of_blowUp D (Z : Set Y) hD [] (by
    obtain ⟨S', hc', hreg', E'⟩ :=
      @exists_blowUpSequence_isSncBoundary_preimage_of_smooth K _ _ D.blowUp hint
        ⟨D.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))⟩ hft hqc hsep hsm
        ⟨D.blowUpπ ⁻¹' (Z : Set Y), Z.isClosed.preimage D.blowUpπ.continuous⟩ hZ'η
    exact ⟨S', hc', hreg', fun J hJ => (List.not_mem_nil hJ).elim, E'⟩)
  exact ⟨S, hc, hreg', E⟩

/-- Principalization of finitely many ideal sheaves with a boundary, by induction on their
number: on an integral scheme of finite type and separated over a field of characteristic zero,
for a closed subset Z not containing the generic point and containing the singular locus and the
supports of the ideal sheaves of a list, there is a succession of blow-ups with centres over Z,
with regular last stage, on which the inverse image of every ideal sheaf of the list is
invertible and the reduced preimage of Z has only normal crossings. Each step blows up the first
ideal sheaf; the blow-up is integral and its singular locus lies over Z. -/
theorem exists_blowUpSequence_isSncBoundary_isInvertible_comap_of_length (m : ℕ) :
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
      [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
      [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
      (Z : Closeds Y), genericPoint Y ∉ (Z : Set Y) → Y.singularLocus ⊆ (Z : Set Y) →
      ∀ l : List Y.IdealSheafData, l.length = m →
      (∀ 𝔠 ∈ l, (𝔠.support : Set Y) ⊆ (Z : Set Y)) →
      ∃ S : Scheme.BlowUpSequence Y,
        (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
          S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
        IsRegular S.last ∧ (∀ 𝔠 ∈ l, (𝔠.comap S.composite).IsInvertible) ∧
        ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
          (E.support : Set S.last) = S.composite ⁻¹' (Z : Set Y) := by
  induction m with
  | zero =>
    intro Y _ _ _ _ _ Z hZη hsing l hl hsupp
    obtain ⟨S, hc, hreg, E⟩ :=
      exists_blowUpSequence_isSncBoundary_preimage_of_singularLocus_subset (K := K) Y Z hZη hsing
    have hnil : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    exact ⟨S, hc, hreg, fun 𝔠 h𝔠 => (List.not_mem_nil h𝔠).elim, E⟩
  | succ m ih =>
    intro Y _ _ _ _ _ Z hZη hsing l hl hsupp
    obtain ⟨𝔠, l', rfl⟩ : ∃ 𝔠 l', l = 𝔠 :: l' := List.exists_cons_of_length_eq_add_one hl
    have h𝔠 : (𝔠.support : Set Y) ⊆ (Z : Set Y) := hsupp 𝔠 List.mem_cons_self
    have hYN : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
    have hη𝔠 : genericPoint Y ∉ (𝔠.support : Set Y) := fun h => hZη (h𝔠 h)
    have hint : IsIntegral 𝔠.blowUp := blowUp_isIntegral_of_genericPoint_notMem_support 𝔠 hη𝔠
    have hdom : IsDominant 𝔠.blowUpπ := blowUp_isDominant_of_genericPoint_notMem_support 𝔠 hη𝔠
    have hprop : IsProper 𝔠.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π 𝔠
    have hft : LocallyOfFiniteType (𝔠.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
    have hqc : QuasiCompact (𝔠.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
    have hsep : IsSeparated (𝔠.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
    have hZ'η : genericPoint 𝔠.blowUp ∉ 𝔠.blowUpπ ⁻¹' (Z : Set Y) := by
      change 𝔠.blowUpπ (genericPoint 𝔠.blowUp) ∉ (Z : Set Y)
      rw [dominant_map_genericPoint]
      exact hZη
    -- the blow-up is regular off the preimage of Z, where it is isomorphic to the base
    have hsing₁ : (𝔠.blowUp).singularLocus ⊆ 𝔠.blowUpπ ⁻¹' (Z : Set Y) := by
      intro z hz
      by_contra hnot
      apply hz
      have hiso : IsIso (𝔠.blowUpπ.stalkMap z) :=
        blowUp_isIso_stalkMap_of_notMem_support 𝔠 z fun h => hnot (h𝔠 h)
      have hregY : IsRegularLocalRing (Y.presheaf.stalk (𝔠.blowUpπ z)) := by
        by_contra hns
        exact hnot (hsing (show 𝔠.blowUpπ z ∈ Y.singularLocus from hns))
      exact IsRegularLocalRing.of_ringEquiv
        (asIso (𝔠.blowUpπ.stalkMap z)).commRingCatIsoToRingEquiv
    have hlen : (l'.map fun 𝔡 => 𝔡.comap 𝔠.blowUpπ).length = m := by
      rw [List.length_map]
      exact Nat.succ.inj hl
    have hsupp₁ : ∀ 𝔡' ∈ l'.map (fun 𝔡 => 𝔡.comap 𝔠.blowUpπ),
        (𝔡'.support : Set 𝔠.blowUp) ⊆ 𝔠.blowUpπ ⁻¹' (Z : Set Y) := by
      intro 𝔡' h𝔡'
      obtain ⟨𝔡, h𝔡, rfl⟩ := List.mem_map.mp h𝔡'
      intro z hz
      have hz' : z ∈ (𝔡.comap 𝔠.blowUpπ).support := hz
      rw [Scheme.IdealSheafData.support_comap] at hz'
      exact hsupp 𝔡 (List.mem_cons_of_mem _ h𝔡) hz'
    refine exists_blowUpSequence_round_of_blowUp 𝔠 (Z : Set Y) h𝔠 (𝔠 :: l') ?_
    obtain ⟨S, hc, hreg, hinv, E⟩ := @ih 𝔠.blowUp hint
      ⟨𝔠.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))⟩ hft hqc hsep
      ⟨𝔠.blowUpπ ⁻¹' (Z : Set Y), Z.isClosed.preimage 𝔠.blowUpπ.continuous⟩ hZ'η hsing₁
      (l'.map fun 𝔡 => 𝔡.comap 𝔠.blowUpπ) hlen hsupp₁
    refine ⟨S, hc, hreg, fun J hJ => ?_, E⟩
    rcases List.mem_cons.mp hJ with hJ𝔠 | hJ'
    · rw [hJ𝔠]
      exact blowUpSequence_isInvertible_comap_composite S _
        (Scheme.IdealSheafData.blowUp.isInvertible_comap_π 𝔠)
    · exact hinv _ (List.mem_map.mpr ⟨J, hJ', rfl⟩)

/-- Principalization of a finite family of ideal sheaves with a boundary: on an integral regular
scheme of finite type and separated over a field of characteristic zero, for a closed subset Z
not containing the generic point and a finite family of ideal sheaves whose supports lie in Z,
there is a succession of blow-ups with centres over Z, with regular last stage, on which the
inverse image of every ideal sheaf of the family is invertible and the reduced preimage of Z has
only normal crossings. -/
theorem exists_blowUpSequence_isSncBoundary_isInvertible_comap_family {κ : Type*} [Finite κ]
    (Y : Scheme.{u}) [IsIntegral Y] [IsRegular Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (Z : Closeds Y) (hZη : genericPoint Y ∉ (Z : Set Y)) (𝔠 : κ → Y.IdealSheafData)
    (h𝔠 : ∀ k, ((𝔠 k).support : Set Y) ⊆ (Z : Set Y)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
      IsRegular S.last ∧ (∀ k, ((𝔠 k).comap S.composite).IsInvertible) ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' (Z : Set Y) := by
  classical
  have := Fintype.ofFinite κ
  have hsing : Y.singularLocus ⊆ (Z : Set Y) := fun y hy => (hy (IsRegular.isRegularAt y)).elim
  obtain ⟨S, hc, hreg, hinv, E⟩ :=
    exists_blowUpSequence_isSncBoundary_isInvertible_comap_of_length (K := K) _ Y Z hZη hsing
      ((Finset.univ : Finset κ).toList.map 𝔠) rfl (by
        intro 𝔡 h𝔡
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp h𝔡
        exact h𝔠 k)
  exact ⟨S, hc, hreg, fun k => hinv _ (List.mem_map.mpr
    ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), rfl⟩), E⟩

/-- Principalization of one ideal sheaf with a boundary: on an integral regular scheme of finite
type and separated over a field of characteristic zero, for a closed subset Z not containing the
generic point and an ideal sheaf 𝔠 whose support lies in Z, there is a succession of blow-ups
with centres over Z, with regular last stage, on which the inverse image of 𝔠 is invertible and
the reduced preimage of Z has only normal crossings. -/
theorem exists_blowUpSequence_isSncBoundary_isInvertible_comap (Y : Scheme.{u}) [IsIntegral Y]
    [IsRegular Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (Z : Closeds Y) (hZη : genericPoint Y ∉ (Z : Set Y)) (𝔠 : Y.IdealSheafData)
    (h𝔠 : (𝔠.support : Set Y) ⊆ (Z : Set Y)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
      IsRegular S.last ∧ (𝔠.comap S.composite).IsInvertible ∧
      ∃ E : S.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S.last) = S.composite ⁻¹' (Z : Set Y) := by
  obtain ⟨S, hc, hreg, hinv, E⟩ :=
    exists_blowUpSequence_isSncBoundary_isInvertible_comap_family (K := K) Y Z hZη
      (fun _ : Unit => 𝔠) (fun _ => h𝔠)
  exact ⟨S, hc, hreg, hinv (), E⟩

end Rounds

end MixedFujita
