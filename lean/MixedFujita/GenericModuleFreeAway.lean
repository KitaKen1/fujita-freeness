/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.FractionRing
public import SGA.Foundations.QuasiCoherent.Tilde

/-! 分数体上の実階数と非零基本開での有限表示加群の自由化。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
namespace MixedFujita
universe u

/-- A finitely presented module over a domain is free on a nonempty basic
open; the rank equals its actual fraction-field rank. -/
theorem finitePresentation_exists_nonzero_free_away
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization.Away r) (LocalizedModule.Away r M) =
        Module.finrank (FractionRing R) (LocalizedModule (nonZeroDivisors R) M) := by
  obtain ⟨r, hr, hf, hd⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) (FractionRing R)
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hf, hd⟩


/-- The nonempty basic-open freeness statement for the actual affine
extension-of-scalars module used by the scheme pullback dictionary. -/
theorem finitePresentation_exists_nonzero_free_away_extension
    {R : CommRingCat.{u}} [IsDomain R] (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (away r) ((ModuleCat.extendScalars (awayMap r).hom).obj M) := by
  obtain ⟨r, hr, hf, _⟩ := finitePresentation_exists_nonzero_free_away R M
  let : Algebra R (away r) := (awayMap r).hom.toAlgebra
  let := isLocalization_away r
  let := isScalarTower_extendScalars_away M r
  let := isLocalizedModule_toExtendScalars_awayMap M r
  let : Module (away r) (LocalizedModule.Away r M) :=
    inferInstanceAs (Module (Localization.Away r) (LocalizedModule.Away r M))
  let : IsScalarTower R (away r) (LocalizedModule.Away r M) :=
    .of_algebraMap_smul fun a l => algebraMap_smul (Localization.Away r) a l
  let : Module.Free (away r) (LocalizedModule.Away r M) := hf
  let e := (IsLocalizedModule.linearEquiv (.powers r) (toExtendScalars M (awayMap r))
    (LocalizedModule.mkLinearMap (.powers r) M)).extendScalarsOfIsLocalization (.powers r) (away r)
  exact ⟨r, hr, Module.Free.of_equiv e.symm⟩

end MixedFujita
