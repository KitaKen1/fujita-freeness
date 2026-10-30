/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveClosureSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
Basic properties of the closure of a projective scheme over a coefficient ring (step 10, R4-3).

For `e : Y → ℙ_S` and `c : R → S`, the closure `projectiveClosure c e` of `Y` in `ℙ_R`
(check 507):
* is proper over `R` (`projectiveClosure_toBase_isProper`; a closed subscheme of `ℙ_R`), so its
  diagonal over the terminal scheme is affine
  (`isAffineHom_diagonal_terminal_of_separated_toSpec`), as needed for the comparison of Čech and
  sheaf cohomology (check 500);
* is integral when `Y` is (`projectiveClosure_isIntegral`): its charts embed into those of `Y`
  (check 507), so it is reduced, and `Y` is dense in it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {n : ℕ}

/-- A scheme with a separated morphism to an affine scheme has affine diagonal over the terminal
scheme. -/
theorem isAffineHom_diagonal_terminal_of_separated_toSpec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [IsSeparated f] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have h : terminal.from X = f ≫ terminal.from (Spec R) := terminal.hom_ext _ _
  rw [h]
  infer_instance

section Closure

variable {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S) {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n S)

theorem projectiveClosure_toBase_isProper :
    IsProper (projectiveClosureι c e ≫ polynomialProjectiveToBase n R) := by
  have := polynomialProjectiveToBase_isProper n R
  infer_instance

theorem projectiveClosure_isAffineHom_diagonal :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveClosure c e))) := by
  have := projectiveClosure_toBase_isProper c e
  exact isAffineHom_diagonal_terminal_of_separated_toSpec
    (projectiveClosureι c e ≫ polynomialProjectiveToBase n R)

/-- The closure of an integral scheme is integral. -/
theorem projectiveClosure_isIntegral [IsIntegral Y]
    [QuasiCompact (e ≫ polynomialProjectiveCoefficientMap c)] :
    IsIntegral (projectiveClosure c e) := by
  have hred : IsReduced (projectiveClosure c e) := by
    let 𝒰 := (projectiveClosure c e).openCoverOfIsOpenCover
      (fun k => projectivePullbackCoordinateOpen (projectiveClosureι c e) k)
      (iSup_projectivePullbackCoordinateOpen _)
    have hcomp : ∀ k, IsReduced (𝒰.X k) := by
      intro k
      change IsReduced (projectivePullbackCoordinateOpen (projectiveClosureι c e) k).toScheme
      have : IsAffine (projectivePullbackCoordinateOpen (projectiveClosureι c e) k).toScheme :=
        projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion _ k
      have hinj : Function.Injective ((closureChartMap c e k).comp
          (projectivePullbackCoordinateOpen (projectiveClosureι c e) k).topIso.hom.hom) :=
        (closureChartMap_injective c e k).comp
          (ConcreteCategory.bijective_of_isIso
            (projectivePullbackCoordinateOpen (projectiveClosureι c e) k).topIso.hom).1
      have : _root_.IsReduced
          Γ((projectivePullbackCoordinateOpen (projectiveClosureι c e) k).toScheme, ⊤) :=
        isReduced_of_injective _ hinj
      exact isReduced_of_isAffine_isReduced _
    exact IsReduced.of_openCover _ 𝒰
  have hirr : IrreducibleSpace (projectiveClosure c e) := by
    have hd : DenseRange (projectiveClosureMap c e) :=
      (inferInstance : IsDominant (projectiveClosureMap c e)).denseRange
    have h1 : IsIrreducible (Set.range (projectiveClosureMap c e)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _
        (projectiveClosureMap c e).continuous.continuousOn
    have h2 : IsIrreducible (Set.univ : Set (projectiveClosure c e)) := by
      rw [← hd.closure_range]
      exact h1.closure
    exact { isPreirreducible_univ := h2.2, toNonempty := ⟨h2.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Closure

end MixedFujita
