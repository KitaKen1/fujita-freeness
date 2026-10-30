/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupCartierRestriction
public import MixedFujita.EtalePointBlowupCharts
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! A reduced closed-point centre over an algebraically closed field is étale
of relative dimension zero. Adapted étale coordinates for its actual blow-up
therefore exist, without a separate smooth-centre premise. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem pointClosureScheme_subsingleton_of_isClosed {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) : Subsingleton (pointClosureScheme x) := by
  refine ⟨fun a b => (pointClosureHomeomorph x).injective ?_⟩
  apply Subtype.ext
  have ha := ((pointClosureHomeomorph x) a).2
  have hb := ((pointClosureHomeomorph x) b).2
  have ha' : ((pointClosureHomeomorph x) a).1 = x := by
    simpa only [hx.closure_eq, Set.mem_singleton_iff] using ha
  have hb' : ((pointClosureHomeomorph x) b).1 = x := by
    simpa only [hx.closure_eq, Set.mem_singleton_iff] using hb
  exact ha'.trans hb'.symm

theorem integral_subsingleton_scheme_etale_over_algClosed {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} [IsIntegral Y] [Subsingleton Y] (f : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : Etale f := by
  let L := Γ(Y, ⊤)
  let : Field L := (isField_of_isIntegral_of_subsingleton Y).toField
  let : Algebra K L := f.sectionsAlgebra ⊤
  have : Algebra.FiniteType K L := f.finiteType_sectionsAlgebra (isAffineOpen_top Y)
  have : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  have hτ : (sectionsHom f ⊤).Etale :=
    RingHom.Etale.of_bijective (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := L))
  have hΓ : (Scheme.ΓSpecIso (.of K)).hom.hom.Etale :=
    RingHom.Etale.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).hom)
  apply (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mpr
  have h := RingHom.Etale.stableUnderComposition _ _ hΓ hτ
  convert h using 1
  ext a
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  simpa only [sectionsHom, RingHom.comp_apply, happ] using
    (congrArg (fun z => f.appTop z) (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of K)) a)).symm

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]

theorem pointClosure_closedPoint_smoothOfRelativeDimension_zero (x : X)
    (hx : IsClosed ({x} : Set X)) :
    SmoothOfRelativeDimension 0 (pointClosureι x ≫ (X ↘ Spec (.of K))) := by
  have := pointClosureScheme_subsingleton_of_isClosed x hx
  have : Etale (pointClosureι x ≫ (X ↘ Spec (.of K))) :=
    integral_subsingleton_scheme_etale_over_algClosed (pointClosureScheme x ↘ Spec (.of K))
  exact (Etale.iff_smoothOfRelativeDimension_zero _).mp inferInstance

theorem smooth_closedPoint_exists_adaptedPointBlowupCoordinates [IsIntegral X]
    [Smooth (X ↘ Spec (.of K))] (n : ℕ) (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty (EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n (pointClosureIdeal x) x) := by
  have := geometricSmoothScheme_relativeDimension (K := K) n hn
  have := pointClosure_closedPoint_smoothOfRelativeDimension_zero (K := K) x hx
  have hxZ : x ∈ (pointClosureIdeal x).support := by
    change x ∈ ((pointClosureIdeal x).support : Set X)
    rw [pointClosureIdeal_support_closedPoint x hx]
    exact Set.mem_singleton x
  obtain ⟨E, -, -⟩ := exists_etalePointBlowup_adaptedModel
    (f := X ↘ Spec (.of K)) (Z := pointClosureIdeal x) (n := n) hxZ hx
  exact ⟨E⟩

end MixedFujita
