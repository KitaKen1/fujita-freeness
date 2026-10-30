/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalRoundupCartierMonomorphism
public import SGA.Foundations.Cohomology.Coherent
public import SGA.Foundations.Cohomology.PushforwardProjective

/-! Use the actual canonical monomorphism and noetherian finite-submodule
closure to establish coherence, without invoking proper cohomological finiteness. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

theorem invertible_module_sheaf_isFiniteType {B : Scheme.{u}}
    (M : B.Modules) [TauCeti.SheafOfModules.IsInvertible (R := B.ringCatSheaf) M] :
    _root_.SheafOfModules.IsFiniteType (R := B.ringCatSheaf) M := by
  obtain ⟨q, hq⟩ :=
    (inferInstance : TauCeti.SheafOfModules.IsInvertible (R := B.ringCatSheaf) M).exists_isInvertible
  have hfin : _root_.SheafOfModules.LocalGeneratorsData.IsFiniteType
      (R := B.ringCatSheaf) (M := M) q := by
    constructor
    intro i
    constructor
    letI := hq.basisSubsingleton i
    exact Finite.of_subsingleton
  exact { exists_localGeneratorsData := ⟨q, hfin⟩ }

theorem quasicoherent_module_isCoherent_of_mono
    {B : Scheme.{u}} [IsLocallyNoetherian B]
    {M N : B.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [SheafOfModules.IsFiniteType.{u} N]
    (α : M ⟶ N) [Mono α] : M.IsCoherent := by
  refine ⟨inferInstance, CohomologyAux.isFiniteType_of_finite_sections M
    (fun U : B.affineOpens => U.1) (iSup_affineOpens_eq_top B) (fun U => U.2) ?_⟩
  intro U
  letI : IsNoetherianRing Γ(B, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : Module.Finite Γ(B, U.1) Γ(N, U.1) :=
    CohomologyAux.finite_sections_of_isFiniteType N U.2
  let f : Γ(M, U.1) →ₗ[Γ(B, U.1)] Γ(N, U.1) := (α.val.app (op U.1)).hom
  exact Module.Finite.of_injective f
    (PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map α) (op U.1))

theorem cartier_direct_image_isCoherent_of_canonical_monomorphism
    {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B] [IsLocallyNoetherian B]
    (q : T ⟶ B) [QuasiCompact q]
    [IsAffineHom (pullback.diagonal (terminal.from T))]
    (E : CartierDivisor T) (C : CartierDivisor B)
    (α : (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf) [Mono α] :
    ((Scheme.Modules.pushforward q).obj E.sheaf).IsCoherent := by
  letI := C.isInvertible_sheaf
  letI := E.isInvertible_sheaf
  letI := invertible_module_sheaf_isFiniteType C.sheaf
  letI := CohomologyAux.isQuasicoherent_pushforward_of_quasiCompact q E.sheaf
  exact quasicoherent_module_isCoherent_of_mono α

end MixedFujita
