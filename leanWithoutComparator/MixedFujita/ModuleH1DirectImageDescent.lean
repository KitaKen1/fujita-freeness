/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SheafCechOneVanishing
public import MixedFujita.SGACohomologyComparison
public import MixedFujita.ProperCoherentPushforward
public import MixedFujita.ActualCartierSerreVanishing
public import SGA.Foundations.Cohomology.LerayTransfer

/-! 任意実順像・proper連接順像のH1消滅降下。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open TopCat.Presheaf TopCat.Sheaf


/-- First-cohomology vanishing descends along ANY actual direct image with
quasi-coherent target. No acyclicity of inverse images of affine opens is assumed. -/
theorem module_pushforward_H1_subsingleton_of_source
    {X Y : Scheme.{u}} [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : Y ⟶ X) (M : Y.Modules)
    [((Scheme.Modules.pushforward p).obj M).IsQuasicoherent]
    (hvan : Subsingleton (Scheme.Modules.Cohomology M 1)) :
    Subsingleton (Scheme.Modules.Cohomology ((Scheme.Modules.pushforward p).obj M) 1) := by
  let N := (Scheme.Modules.pushforward p).obj M
  obtain ⟨n, U, hcov, hU⟩ := CohomologyAux.exists_cechCover X
  have hcovY : (⨆ i, p ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  let : Subsingleton (Scheme.Modules.Cohomology M 1) := hvan
  let : Subsingleton (M.H 1) := (sgaCohomologyLinearEquiv M 1).subsingleton
  have hM : Subsingleton (M.toAbSheaf.H' 1 (⨆ i, p ⁻¹ᵁ U i)) := by
    rw [hcovY]
    infer_instance
  let : Subsingleton ((cechComplex (fun i => p ⁻¹ᵁ U i) M.presheaf).homology 1) :=
    sheaf_cech_homology_one_subsingleton_of_H1_subsingleton M.toAbSheaf _ hM
  let : Subsingleton ((cechComplex U N.presheaf).homology 1) :=
    (CohomologyAux.cechHomologyPushforwardAddEquiv p M U 1).subsingleton
  let : Subsingleton (N.H' 1 (⨆ i, U i)) := (N.cechHomologyLinearEquiv U 1 hU).symm.subsingleton
  let : Subsingleton (N.H 1) := (CohomologyAux.H'CongrOpens N 1 hcov).symm.subsingleton
  exact (sgaCohomologyLinearEquiv N 1).symm.subsingleton


/-- Proper coherent direct images over a proper field source inherit H1
vanishing without local higher-direct-image vanishing. The actual source may
be nonreduced, reducible or empty, with its field structure constructed internally. -/
theorem proper_module_pushforward_H1_subsingleton_of_source
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsProper p] (M : Y.Modules) [M.IsCoherent]
    (hvan : Subsingleton (Scheme.Modules.Cohomology M 1)) :
    Subsingleton (Scheme.Modules.Cohomology ((Scheme.Modules.pushforward p).obj M) 1) := by
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (p ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (X ↘ Spec (CommRingCat.of K))
  let : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (Y ↘ Spec (CommRingCat.of K))
  let : ((Scheme.Modules.pushforward p).obj M).IsCoherent := proper_module_pushforward_isCoherent p M
  let : ((Scheme.Modules.pushforward p).obj M).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  exact module_pushforward_H1_subsingleton_of_source p M hvan


/-- A concrete direct-image isomorphism transfers actual H1 vanishing
from the source, with no higher-direct-image or local vanishing premise. -/
theorem proper_module_H1_subsingleton_of_pushforward_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsProper p] (M : Y.Modules) [M.IsCoherent] (N : X.Modules)
    (a : N ≅ (Scheme.Modules.pushforward p).obj M)
    (hvan : Subsingleton (Scheme.Modules.Cohomology M 1)) :
    Subsingleton (Scheme.Modules.Cohomology N 1) := by
  let := proper_module_pushforward_H1_subsingleton_of_source K p M hvan
  exact (actualCohomologyLinearEquivOfIso a 1).subsingleton

end MixedFujita
