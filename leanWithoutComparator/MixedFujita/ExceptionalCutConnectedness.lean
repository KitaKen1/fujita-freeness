/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierSupportedUnion
public import MixedFujita.ProperSurjectiveFunctionsConnectedness
public import MixedFujita.ActualCriticalCutUntwisting
public import MixedFujita.CartierPushforwardExactness
public import MixedFujita.QuasicoherentAffineEpi

/-!
On an affine base, a single actual H1 vanishing gives the needed direct-image
exactness. Exceptional-unit descent and disjointness untwist the cut and make its
unit map surjective. Properness then gives preconnected fibres, including for
nonreduced cuts. H1 vanishing itself remains an explicit hypothesis.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
universe u

/-- Over an affine base, global H1 of the kernel suffices for exact direct image.
No higher direct image or vanishing on all base opens is assumed. -/
theorem affine_pushforward_shortExact_of_H1_vanishing
    {X T : Scheme.{u}} [IsAffine X] (p : T ⟶ X)
    {C : ShortComplex T.Modules} (hC : C.ShortExact)
    [((Scheme.Modules.pushforward p).obj C.X₃).IsQuasicoherent]
    (hvan : Subsingleton (Scheme.Modules.Cohomology C.X₁ 1)) :
    (C.map (Scheme.Modules.pushforward p)).ShortExact := by
  let : (Scheme.Modules.pushforward p).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  let := hC.mono_f
  have hf : Mono ((Scheme.Modules.pushforward p).map C.f) :=
    (Scheme.Modules.pushforward p).map_mono C.f
  have hs := modulePushforward_global_sections_surjective_of_source p C.g
    (Scheme.Modules.sections_surjective hC hvan)
  have hg : Epi ((Scheme.Modules.pushforward p).map C.g) :=
    CohomologyAux.epi_of_surjective_app _ _ (fun _ : Unit => ⊤) (by simp)
      (fun _ => isAffineOpen_top X) (fun _ => hs)
  exact ShortComplex.ShortExact.mk'
    (hC.exact.map_of_mono_of_preservesKernel (Scheme.Modules.pushforward p) hC.mono_f inferInstance)
    hf hg

set_option maxHeartbeats 400000 in
/-- Exact direct image makes the unit of the actual untwisted cut epimorphic.
The cut and its closed image need not be reduced or normal. -/
theorem effectiveCartier_cut_unit_epi_of_pushforward_shortExact
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0)
    (hpush : ((ShortComplex.cokernelSequence (cartierEffectiveInclusion E S hS)).map
      (Scheme.Modules.pushforward p)).ShortExact) :
    Epi (schemeUnitToPushforwardUnit ((effectiveCartierIdealSheaf S hS).subschemeι ≫ p)) := by
  let f := (Scheme.Modules.pushforward p).map (effectiveCartierCutToIntrinsicQuotient E S hE hS)
  let : IsIso f := effectiveCartierCutToIntrinsicQuotient_pushforward_isIso p hnorm E S hE hS hES hpush
  let u := schemeUnitToPushforwardUnit p ≫
    (Scheme.Modules.pushforward p).map (schemeUnitToPushforwardUnit (effectiveCartierIdealSheaf S hS).subschemeι)
  have he : u ≫ f = effectiveCartierPushforwardUnitMap p E hE ≫
      (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS)) :=
    effectiveCartierCutToIntrinsicQuotient_pushforward_unit p E S hE hS
  let : Epi ((Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS))) := hpush.epi_g
  have hf : Epi (u ≫ f) := by rw [he]; infer_instance
  have : Epi u := (epi_comp_iff_of_isIso u f).mp hf
  let c := (Scheme.Modules.pushforwardComp (effectiveCartierIdealSheaf S hS).subschemeι p).app
    (CohomologyAux.unitModule (effectiveCartierIdealSheaf S hS).subscheme)
  have hc : u ≫ c.hom =
      schemeUnitToPushforwardUnit ((effectiveCartierIdealSheaf S hS).subschemeι ≫ p) :=
    Scheme.Modules.unitToPushforwardObjUnit_comp (effectiveCartierIdealSheaf S hS).subschemeι p
  rw [← hc]
  infer_instance

/-- A single H1 vanishing gives connectedness of every actual cut fibre over an affine base. -/
theorem effectiveCartier_cut_fibre_preconnected_of_H1
    {X T : Scheme.{u}} [IsIntegral X] [IsAffine X] [IsLocallyNoetherian X]
    [IsIntegral T] [IsNoetherian T] (p : T ⟶ X) [IsProper p]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (E - S).sheaf 1)) (x : X) :
    _root_.IsPreconnected (((effectiveCartierIdealSheaf S hS).subschemeι ≫ p) ⁻¹' {x}) := by
  let : IsAffineHom (pullback.diagonal (terminal.from T)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated p
  let C := ShortComplex.cokernelSequence (cartierEffectiveInclusion E S hS)
  have hC : C.ShortExact := cartierEffectiveInclusion_cokernelSequence_shortExact E S hS
  let := E.isInvertible_sheaf
  let : E.sheaf.IsCoherent := invertible_module_isCoherent _
  let := (E - S).isInvertible_sheaf
  let : (E - S).sheaf.IsCoherent := invertible_module_isCoherent _
  let : C.X₁.IsCoherent := inferInstanceAs (E - S).sheaf.IsCoherent
  let : C.X₁.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : C.X₂.IsCoherent := inferInstanceAs E.sheaf.IsCoherent
  let : C.X₃.IsCoherent := CohomologyAux.isCoherent_X₃_of_shortExact hC
  let : C.X₃.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : ((Scheme.Modules.pushforward p).obj C.X₃).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward_of_quasiCompact p C.X₃
  have hpush := affine_pushforward_shortExact_of_H1_vanishing p hC hvan
  let q := (effectiveCartierIdealSheaf S hS).subschemeι ≫ p
  have : IsProper q := inferInstance
  have : Epi (schemeUnitToPushforwardUnit q) :=
    effectiveCartier_cut_unit_epi_of_pushforward_shortExact p hnorm E S hE hS hES hpush
  let : IsAffineHom (pullback.diagonal (terminal.from (effectiveCartierIdealSheaf S hS).subscheme)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated q
  let : ((Scheme.Modules.pushforward q).obj
      (CohomologyAux.unitModule (effectiveCartierIdealSheaf S hS).subscheme)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward_of_quasiCompact q _
  apply proper_affine_fibre_preconnected_of_function_surjective q _ x
  intro U hU
  exact quasicoherent_epi_app_surjective_on_affine (schemeUnitToPushforwardUnit q) ⟨U, hU⟩

/-- Transfer connectedness of the nonreduced cut to precisely the non-klt union in the model. -/
theorem threshold_member_union_fibre_preconnected_of_H1
    {X T : Scheme.{u}} [IsIntegral X] [IsAffine X] [IsLocallyNoetherian X]
    [IsIntegral T] [IsNoetherian T] (p : T ⟶ X) [IsProper p]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (B E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    (d : ℕ) (hd : 1 ≤ d) {r : ℕ} (ξ : Fin r → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hSc : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) ↔
      (d : ℤ) ≤ cartierCoefficient B (t : T))
    (hES : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) →
      cartierCoefficient E (t : T) = 0)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (E - S).sheaf 1)) (x : X) :
    _root_.IsPreconnected (⋃ i ∈ {i | (d : ℤ) ≤ cartierCoefficient B (ξ i)},
      closure ({ξ i} : Set T) ∩ p ⁻¹' {x}) := by
  have h := (effectiveCartier_cut_fibre_preconnected_iff p S hS x).mp
    (effectiveCartier_cut_fibre_preconnected_of_H1 p hnorm E S hE hS hES hvan x)
  rw [effectiveCartier_support_eq_threshold_member_union hnorm B S hS d hd ξ hξ hsupport hSc] at h
  simpa only [Set.iUnion_inter] using h

end MixedFujita
