/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing
public import SGA.Foundations.Cohomology.SteinFactorization

/-! アフィン対角を持つ始域からの実固有直像の連接性。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Proper direct images of actual coherent modules are coherent over a locally
Noetherian base when the source has affine diagonal. No rank-one premise. -/
theorem proper_module_pushforward_isCoherent
    {T B : Scheme.{u}} [IsLocallyNoetherian B]
    [IsAffineHom (pullback.diagonal (terminal.from T))]
    (q : T ⟶ B) [IsProper q] (M : T.Modules) [M.IsCoherent] :
    ((Scheme.Modules.pushforward q).obj M).IsCoherent := by
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hq := CohomologyAux.isQuasicoherent_pushforward_of_quasiCompact q M
  refine ⟨hq, CohomologyAux.isFiniteType_of_finite_sections _
    (fun U : B.affineOpens => U.1) (iSup_affineOpens_eq_top B) (fun U => U.2) ?_⟩
  intro U
  exact CohomologyAux.finite_sections_preimage_of_isProper q M U.2

end MixedFujita
