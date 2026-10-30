/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedImmersionCohomology
public import MixedFujita.CartierCutEuler

/-!
Closed-immersion comparison transports degreewise finiteness, vanishing and
truncated Euler sums between actual scheme-module cohomologies. The Euler
identity for a Cartier cut is consequently expressed on the actual cut scheme.
The finite-cohomology and upper-vanishing inputs on the ambient sheaves remain
explicit; no Bertini flag or geometric finiteness theorem is asserted here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

theorem closedImmersion_cohomology_subsingleton_iff (M : X.Modules) (n : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n) ↔
      Subsingleton (Scheme.Modules.Cohomology M n) := by
  constructor
  · intro h
    let := h
    exact (closedImmersionCohomologyAddEquiv f M n).symm.subsingleton
  · intro h
    let := h
    exact (closedImmersionCohomologyAddEquiv f M n).subsingleton

variable (R : Type u) [CommRing R]
variable [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
variable [f.IsOver (Spec (CommRingCat.of R))]

theorem closedImmersion_cohomology_finite_iff (M : X.Modules) (n : ℕ) :
    Module.Finite R (Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n) ↔
      Module.Finite R (Scheme.Modules.Cohomology M n) := by
  constructor
  · intro h
    let := h
    exact Module.Finite.equiv (closedImmersionCohomologyBaseLinearEquiv R f M n)
  · intro h
    let := h
    exact Module.Finite.equiv (closedImmersionCohomologyBaseLinearEquiv R f M n).symm

variable (K : Type u) [Field K]
variable [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
variable [f.IsOver (Spec (CommRingCat.of K))]

theorem closedImmersion_cohomology_finrank_eq (M : X.Modules) (n : ℕ) :
    Module.finrank K (Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n) =
      Module.finrank K (Scheme.Modules.Cohomology M n) :=
  (closedImmersionCohomologyBaseLinearEquiv K f M n).finrank_eq

theorem closedImmersion_eulerCharBelow_eq (M : X.Modules) (n : ℕ) :
    Scheme.Modules.eulerCharBelow K Y ((Scheme.Modules.pushforward f).obj M) n =
      Scheme.Modules.eulerCharBelow K X M n := by
  induction n with
  | zero => simp only [Scheme.Modules.eulerCharBelow_zero]
  | succ n ih =>
    rw [Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_succ,
      ih, closedImmersion_cohomology_finrank_eq f K M n]

variable {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]

theorem cartierCut_subscheme_eulerCharBelow_eq_sub
    (D E : Scheme.CartierDivisor T) (hE : E.IsEffective)
    [(effectiveCartierIdealSheaf E hE).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf E hE).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (n : ℕ)
    (hDE : ∀ j < n, 0 < j → FiniteDimensional K
      (Scheme.Modules.Cohomology (D - E).sheaf j))
    (hD : ∀ j < n, FiniteDimensional K (Scheme.Modules.Cohomology D.sheaf j))
    (hvan : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf n)) :
    Scheme.Modules.eulerCharBelow K (effectiveCartierIdealSheaf E hE).subscheme
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj D.sheaf) n =
      Scheme.Modules.eulerCharBelow K T D.sheaf n -
        Scheme.Modules.eulerCharBelow K T (D - E).sheaf n := by
  rw [← closedImmersion_eulerCharBelow_eq (effectiveCartierIdealSheaf E hE).subschemeι K]
  exact cartierCut_eulerCharBelow_eq_sub D E hE n hDE hD hvan

end MixedFujita
