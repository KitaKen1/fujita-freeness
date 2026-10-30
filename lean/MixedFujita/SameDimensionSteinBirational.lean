/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinAlgebraicFunctionField
public import MixedFujita.BirationalLogPairDescent
public import Mathlib.FieldTheory.FinTrdeg

/-!
Same-dimensional dominant integral schemes of finite type over a field have an
algebraic function-field extension. For a Stein-type map from a normal source,
the actual function-field map is therefore bijective. This uses denominator
clearing and normality, rather than a separate theory of generically finite maps.
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

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

include K f

/-- Equal geometric dimensions force the actual dominant function-field extension
to be algebraic, without a properness or normality assumption. -/
theorem dominant_functionField_isAlgebraic_of_same_dimension
    (hdim : topologicalKrullDim X = topologicalKrullDim Y) :
    letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra;
    Algebra.IsAlgebraic Y.functionField X.functionField := by
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  haveI : IsScalarTower K Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (dominantFunctionFieldAlgHom (K := K) f).commutes a |>.symm
  haveI : Algebra.EssFiniteType K X.functionField := by
    rw [functionFieldBaseAlgebra_eq_scheme (K := K) (X := X)]
    infer_instance
  haveI : Algebra.EssFiniteType K Y.functionField := by
    rw [functionFieldBaseAlgebra_eq_scheme (K := K) (X := Y)]
    infer_instance
  have hfinX := trdeg_lt_aleph0 K X.functionField
  have hfinY := trdeg_lt_aleph0 K Y.functionField
  rw [TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K] at hdim
  rw [← functionFieldBaseAlgebra_eq_scheme (K := K) (X := X),
    ← functionFieldBaseAlgebra_eq_scheme (K := K) (X := Y)] at hdim
  have hnat : (Algebra.trdeg K X.functionField).toNat =
      (Algebra.trdeg K Y.functionField).toNat := by exact_mod_cast hdim
  have htower := trdeg_add_eq K Y.functionField (A := X.functionField)
  have hrel : Algebra.trdeg Y.functionField X.functionField < Cardinal.aleph0 := by
    apply lt_of_le_of_lt ?_ hfinX
    rw [← htower]
    simpa only [zero_add, add_zero, add_comm] using add_le_add_right
      (zero_le : (0 : Cardinal) ≤ Algebra.trdeg K Y.functionField)
      (Algebra.trdeg Y.functionField X.functionField)
  have hsum := congrArg Cardinal.toNat htower
  rw [Cardinal.toNat_add hfinY hrel] at hsum
  have hzNat : (Algebra.trdeg Y.functionField X.functionField).toNat = 0 := by omega
  have hz : Algebra.trdeg Y.functionField X.functionField = 0 := by
    simpa only [hzNat, Nat.cast_zero] using (Cardinal.cast_toNat_of_lt_aleph0 hrel).symm
  exact trdeg_eq_zero_iff.mp hz

/-- A dominant map of integral finite-type schemes does not increase dimension. -/
theorem dominant_topologicalKrullDim_le : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  haveI : Algebra.EssFiniteType K X.functionField := by
    rw [functionFieldBaseAlgebra_eq_scheme (K := K) (X := X)]
    infer_instance
  rw [TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K]
  rw [← functionFieldBaseAlgebra_eq_scheme (K := K) (X := X),
    ← functionFieldBaseAlgebra_eq_scheme (K := K) (X := Y)]
  have htr := trdeg_le_of_injective (dominantFunctionFieldAlgHom (K := K) f)
    (dominantFunctionFieldAlgHom (K := K) f).injective
  exact_mod_cast Cardinal.toNat_le_toNat htr (trdeg_lt_aleph0 K X.functionField)

/-- A same-dimensional Stein-type map from a normal integral source is actually
birational. Only surjectivity on functions on opens is needed. -/
theorem stein_functionFieldAlgHom_bijective_of_same_dimension
    (hdim : topologicalKrullDim X = topologicalKrullDim Y)
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    Function.Bijective (dominantFunctionFieldAlgHom (K := K) f) := by
  exact stein_functionFieldMap_bijective_of_isAlgebraic f happ hnorm
    (dominant_functionField_isAlgebraic_of_same_dimension (K := K) f hdim)

end MixedFujita
