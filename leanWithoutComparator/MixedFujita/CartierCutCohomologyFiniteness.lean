/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierFlagEuler

/-!
Finite-dimensional cohomology passes to the quotient of an actual short
exact sequence using two neighboring degrees. Closed-immersion comparison
then puts the conclusion on the actual Cartier cut. Finiteness of the two
ambient groups remains an explicit input; no proper finiteness is asserted.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

theorem shortExact_cohomology_quotient_finite
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    (hMiddle : FiniteDimensional K (Scheme.Modules.Cohomology S.X₂ q))
    (hLeft : FiniteDimensional K (Scheme.Modules.Cohomology S.X₁ (q + 1))) :
    FiniteDimensional K (Scheme.Modules.Cohomology S.X₃ q) := by
  let := hMiddle
  let := hLeft
  have hex : Function.Exact (Scheme.Modules.cohomologyMapBaseLinear K X S.g q)
      (Scheme.Modules.cohomologyδBaseLinear K X hS q (q + 1) rfl) := by
    have hmap : ⇑(Scheme.Modules.cohomologyMapBaseLinear K X S.g q) =
        ⇑(Scheme.Modules.cohomologyMap S.g q) := by
      funext x
      rw [Scheme.Modules.cohomologyMapBaseLinear_apply, Scheme.Modules.cohomologyFunctor_map]
      rfl
    have hdelta : ⇑(Scheme.Modules.cohomologyδBaseLinear K X hS q (q + 1) rfl) =
        ⇑(Scheme.Modules.cohomologyδ hS q (q + 1) rfl) := by
      funext x
      exact Scheme.Modules.cohomologyδBaseLinear_apply K X hS q (q + 1) rfl x
    rw [hmap, hdelta]
    exact Scheme.Modules.exact_cohomologyMap_cohomologyδ hS q (q + 1) rfl
  exact TauCeti.finiteDimensional_of_exact hex

variable [IsIntegral X] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]

theorem cartierCut_cohomology_finite_of_sheaf_isos
    (D E F : CartierDivisor X) (hE : E.IsEffective)
    (f : Y ⟶ X) [IsClosedImmersion f] [f.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules) (eShift : (D - E).sheaf ≅ F.sheaf)
    (eCut : (cartierCutShortComplex D E hE).X₃ ≅ (Scheme.Modules.pushforward f).obj M)
    (q : ℕ) (hD : FiniteDimensional K (Scheme.Modules.Cohomology D.sheaf q))
    (hF : FiniteDimensional K (Scheme.Modules.Cohomology F.sheaf (q + 1))) :
    FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  have hDE := (Scheme.Modules.finiteDimensional_cohomology_congr K eShift (q + 1)).mpr hF
  have h := shortExact_cohomology_quotient_finite
    (cartierCutShortComplex_shortExact D E hE) q hD hDE
  have hpush := (Scheme.Modules.finiteDimensional_cohomology_congr K eCut q).mp h
  exact (closedImmersion_cohomology_finite_iff f K M q).mp hpush

end MixedFujita
