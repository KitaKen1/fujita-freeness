/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Cohomology.ProperFiniteness
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base

/-! The SGA and TauCeti global cohomology groups are canonically linear-equivalent over global functions and over the actual affine base ring. Proper finiteness for actual coherent modules follows from the proved SGA theorem. No vanishing or positivity premise is substituted for Kawamata--Viehweg vanishing. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}}

theorem sga_smulHom_eq_globalSectionsSmul (M : X.Modules) (r : Γ(X, ⊤)) :
    M.smulHom r = (SheafOfModules.toSheaf X.ringCatSheaf).map (M.globalSectionsSmul r) := by
  apply Scheme.Modules.toAbSheaf_hom_ext
  intro U x
  change (M.smulHom r).hom.app (op U) x = (M.globalSectionsSmul r).app U x
  rw [Scheme.Modules.smulHom_app_apply, Scheme.Modules.globalSectionsSmul_app]
  exact (M.smul_apply _ x).symm

noncomputable def sgaCohomologyLinearEquiv (M : X.Modules) (n : ℕ) :
    M.H n ≃ₗ[Γ(X, ⊤)] Scheme.Modules.Cohomology M n where
  toAddEquiv := Scheme.Modules.H.addEquivSheafH M n
  map_smul' r x := by
    simp only [RingHom.id_apply, Scheme.Modules.H'.smul_def,
      Scheme.Modules.cohomology_smul]
    change Sheaf.H'.addEquivH isTerminalTop M.toAbSheaf n
        (Sheaf.H'.map (M.smulHom r) n ⊤ x) = _
    rw [Sheaf.H'.addEquivH_naturality, sga_smulHom_eq_globalSectionsSmul]
    rfl

variable (R : Type u) [CommRing R] [X.Over (Spec (CommRingCat.of R))]

noncomputable def sgaCohomologyBaseLinearEquiv (M : X.Modules) (n : ℕ) :
    letI := M.moduleOver (X ↘ Spec (CommRingCat.of R)) n ⊤
    M.H n ≃ₗ[R] Scheme.Modules.Cohomology M n := by
  letI := M.moduleOver (X ↘ Spec (CommRingCat.of R)) n ⊤
  refine { toAddEquiv := Scheme.Modules.H.addEquivSheafH M n, map_smul' := ?_ }
  intro r x
  change sgaCohomologyLinearEquiv M n
      ((X ↘ Spec (CommRingCat.of R)).specStructureRingHom r • x) =
    Scheme.Modules.baseRingToGlobalSections R X r • sgaCohomologyLinearEquiv M n x
  rw [Scheme.Modules.baseRingToGlobalSections_apply]
  exact (sgaCohomologyLinearEquiv M n).map_smul _ x

theorem proper_coherent_cohomology_finite [IsNoetherianRing R]
    [IsProper (X ↘ Spec (CommRingCat.of R))]
    (M : X.Modules) [M.IsCoherent] (n : ℕ) :
    Module.Finite R (Scheme.Modules.Cohomology M n) := by
  letI := M.moduleOver (X ↘ Spec (CommRingCat.of R)) n ⊤
  letI : Module.Finite R (M.H n) := properFinitenessStatement
    (CommRingCat.of R) X (X ↘ Spec (CommRingCat.of R)) M n
  exact Module.Finite.equiv (sgaCohomologyBaseLinearEquiv R M n)

end MixedFujita

