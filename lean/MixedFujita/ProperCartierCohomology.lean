/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACohomologyComparison
public import MixedFujita.CanonicalRoundupDirectImageCoherence
public import MixedFujita.ProperTwoAffineCurveCohomology
public import MixedFujita.CartierCutCohomologyFiniteness
public import MixedFujita.ModuleCohomologyVanishing

/-! Actual invertible modules are coherent. On schemes proper over a noetherian affine base, all cohomology groups of actual invertible and Cartier sheaves and Cartier pullbacks are finite over that base. No smoothness, projectivity, dimension or divisor positivity is required. The existing Grothendieck dimension bound is transferred to actual TauCeti cohomology. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem invertible_module_isCoherent {X : Scheme.{u}} (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] : M.IsCoherent :=
  ⟨invertibleModule_isQuasicoherent M, invertible_module_sheaf_isFiniteType M⟩

theorem actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt
    {X : Scheme.{u}} [NoetherianSpace X] (M : X.Modules) (n : ℕ)
    (hn : topologicalKrullDim X < n) :
    Subsingleton (Scheme.Modules.Cohomology M n) := by
  letI := moduleCohomology_subsingleton_of_topologicalKrullDim_lt M n hn
  exact (sgaCohomologyLinearEquiv M n).symm.subsingleton

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))]
  [IsProper (X ↘ Spec (CommRingCat.of R))]

theorem proper_invertible_cohomology_finite (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (n : ℕ) :
    Module.Finite R (Scheme.Modules.Cohomology M n) := by
  letI := invertible_module_isCoherent M
  exact proper_coherent_cohomology_finite R M n

theorem proper_cartier_cohomology_finite [IsIntegral X] (D : CartierDivisor X) (n : ℕ) :
    Module.Finite R (Scheme.Modules.Cohomology D.sheaf n) := by
  letI := D.isInvertible_sheaf
  exact proper_invertible_cohomology_finite R D.sheaf n

theorem proper_cartier_sections_finite [IsIntegral X] (D : CartierDivisor X) :
    Module.Finite R Γ(D.sheaf, ⊤) := by
  letI := proper_cartier_cohomology_finite R D 0
  exact Module.Finite.equiv (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X D.sheaf)

theorem proper_cartierPullback_cohomology_finite
    {Y : Scheme.{u}} [IsIntegral Y] (D : CartierDivisor Y) (φ : X ⟶ Y) (n : ℕ) :
    Module.Finite R
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) n) := by
  letI := D.isInvertible_sheaf
  exact proper_invertible_cohomology_finite R _ n

end MixedFujita

