/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierTargetImageIdeal
public import MixedFujita.EffectiveCartierPushforwardUnit

/-! Nonvanishing of the actual image ideal.
The effective-Cartier unit field formula suffices; no generic frame is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem cartierTargetImageIdealSheaf_eq_bot_iff_isZero
    {B : Scheme.{u}} [IsIntegral B] {M : B.Modules} [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) [Mono α] :
    cartierTargetImageIdealSheaf C α = ⊥ ↔ IsZero M := by
  let φ := cartierTargetImageStructureHom C α
  letI := cartierTargetImageStructureHom_mono C α
  constructor
  · intro hI
    have hφ : φ = 0 := by
      apply moduleHom_ext_affine
      intro U
      ext s
      change Scheme.Modules.Hom.app φ U.1 s = 0
      have hm : Scheme.Modules.Hom.app φ U.1 s ∈ (cartierTargetImageIdealSheaf C α).ideal U :=
        (Set.ext_iff.mp (cartierTargetImageIdealSheaf_affine_image C α U) _).mp ⟨s, rfl⟩
      rw [hI, Scheme.IdealSheafData.ideal_bot] at hm
      exact hm
    have hN : IsZero ((cartierTwistFunctor (-C)).obj M) := by
      rw [IsZero.iff_id_eq_zero]
      apply (cancel_mono φ).mp
      simp [hφ]
    exact IsZero.of_full_of_faithful_of_isZero (cartierTwistFunctor (-C)) M hN
  · intro hM
    have hα : α = 0 := hM.eq_of_src _ _
    have hφ : φ = 0 := by simp [φ, cartierTargetImageStructureHom, hα]
    apply Scheme.IdealSheafData.ext
    funext U
    apply SetLike.coe_injective
    rw [← cartierTargetImageIdealSheaf_affine_image C α U]
    change Set.range (Scheme.Modules.Hom.app φ U.1) = ((⊥ : Ideal Γ(B, U.1)) : Set Γ(B, U.1))
    rw [hφ]
    ext a
    change (∃ s : Γ((-C).sheaf ⊗ M, U.1), 0 = a) ↔ a = 0
    simp [eq_comm]

theorem effectiveCartierPushforwardUnitMap_ne_zero
    {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective) :
    effectiveCartierPushforwardUnitMap q E heff ≠ 0 := by
  intro h
  let U : B.Opens := ⊤
  have hz := effectiveCartierPushforwardUnitMap_rational q E heff U (1 : Γ(B, U))
  have hzero : Scheme.Modules.Hom.app (effectiveCartierPushforwardUnitMap q E heff) U
      (1 : Γ(B, U)) = 0 := by rw [h]; rfl
  rw [hzero, map_zero, map_zero] at hz
  exact zero_ne_one (by simpa only [map_one] using hz)

theorem effectiveCartier_direct_image_not_isZero
    {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective) :
    ¬ IsZero ((Scheme.Modules.pushforward q).obj E.sheaf) := by
  intro hM
  exact effectiveCartierPushforwardUnitMap_ne_zero q E heff (hM.eq_of_tgt _ _)

theorem effectiveCartier_direct_image_actual_ideal_ne_bot
    {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective)
    [((Scheme.Modules.pushforward q).obj E.sheaf).IsQuasicoherent]
    (C : CartierDivisor B) (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf)
    [Mono α] : cartierTargetImageIdealSheaf C α ≠ ⊥ := by
  intro hI
  exact effectiveCartier_direct_image_not_isZero q E heff
    ((cartierTargetImageIdealSheaf_eq_bot_iff_isZero C α).mp hI)

theorem integral_genericPoint_notMem_support_of_ideal_ne_bot
    {B : Scheme.{u}} [IsIntegral B] (I : B.IdealSheafData) (hI : I ≠ ⊥) :
    genericPoint B ∉ (I.support : Set B) := by
  intro hgen
  have htop : I.support = ⊤ := by
    apply top_unique
    intro b _
    exact (genericPoint_specializes b).mem_closed I.support.isClosed hgen
  exact hI (Scheme.IdealSheafData.support_eq_top_iff.mp htop)

end MixedFujita

