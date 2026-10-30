/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperCurveDegree
public import MixedFujita.CurveFlagEulerDegree
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris

/-!
Two actual affine opens covering a separated locally Noetherian scheme give
vanishing in every degree at least two for quasi-coherent coefficients.
For a proper scheme over a field, Noetherianity and the affine intersection
are derived. The existence of the two-open cover is still explicit.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry
namespace MixedFujita
universe u

theorem separatedTwoAffine_cohomology_vanish
    {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology M q) :=
  AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen_of_isAffineHom
    M hU hV hUV q hq

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

include K in
theorem properTwoAffine_cohomology_vanish
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology M q) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (X ↘ Spec (CommRingCat.of K))]
    infer_instance⟩
  exact separatedTwoAffine_cohomology_vanish M hU hV hUV q hq

theorem properTwoAffine_eulerCharBelow_eq_two
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n) :
    Scheme.Modules.eulerCharBelow K X M n = Scheme.Modules.eulerCharBelow K X M 2 :=
  eulerCharBelow_eq_of_vanishing_between K M 2 n hn
    (fun q hq _ ↦ properTwoAffine_cohomology_vanish (K := K) M hU hV hUV q hq)

end MixedFujita
