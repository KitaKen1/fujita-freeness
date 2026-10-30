/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension

/-!
The closure of a point as an integral closed subscheme (step 4). For a point η of a scheme X, the
closed subscheme W of X defined by the vanishing ideal sheaf of the closure of η (the reduced
induced structure) has underlying space the closure of η: on every affine open its ring is the
quotient by a radical ideal, so W is reduced, and W is homeomorphic to the irreducible closure of
η, so W is irreducible, hence integral, of the same dimension as the closure of η, with generic
point mapped to η. Over a field, W is a scheme locally of finite type whenever X is. This is the
subvariety W of the numerical hypotheses A^d · W ≥ (n + 1)^d, on which Lemma 4 and the mixed bound
(13) are stated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace MixedFujita

universe u

variable {X : Scheme.{u}}

/-- The vanishing ideal sheaf of the closure of a point. -/
noncomputable def pointClosureIdeal (η : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {η}, isClosed_closure⟩

/-- The closure of a point with its reduced induced closed subscheme structure. -/
noncomputable abbrev pointClosureScheme (η : X) : Scheme.{u} :=
  (pointClosureIdeal η).subscheme

/-- The closed immersion of the closure of a point. -/
noncomputable abbrev pointClosureι (η : X) : pointClosureScheme η ⟶ X :=
  (pointClosureIdeal η).subschemeι

instance pointClosureι_isClosedImmersion (η : X) : IsClosedImmersion (pointClosureι η) :=
  inferInstanceAs (IsClosedImmersion (pointClosureIdeal η).subschemeι)

theorem range_pointClosureι (η : X) : Set.range (pointClosureι η) = closure {η} := by
  rw [pointClosureι, Scheme.IdealSheafData.range_subschemeι, pointClosureIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

instance pointClosureScheme_isReduced (η : X) : IsReduced (pointClosureScheme η) := by
  have H : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U) ⧸ (pointClosureIdeal η).ideal U) := by
    intro U
    rw [← Ideal.isRadical_iff_quotient_reduced, pointClosureIdeal,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  have : ∀ i, IsReduced ((pointClosureIdeal η).subschemeCover.openCover.X i) :=
    fun (U : X.affineOpens) => by
      have := H U
      change IsReduced (Spec (CommRingCat.of (Γ(X, U) ⧸ (pointClosureIdeal η).ideal U)))
      infer_instance
  exact IsReduced.of_openCover _ (pointClosureIdeal η).subschemeCover.openCover

/-- The closure of a point is homeomorphic to its closed subscheme. -/
noncomputable def pointClosureHomeomorph (η : X) :
    pointClosureScheme η ≃ₜ closure ({η} : Set X) :=
  ((pointClosureι η).isClosedEmbedding.isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (range_pointClosureι η))

instance pointClosureScheme_irreducibleSpace (η : X) :
    IrreducibleSpace (pointClosureScheme η) := by
  have hZ : IrreducibleSpace (closure ({η} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  have h := (IrreducibleSpace.isIrreducible_univ (closure ({η} : Set X))).image
    (pointClosureHomeomorph η).symm
    (pointClosureHomeomorph η).symm.continuous.continuousOn
  rw [Set.image_univ, (pointClosureHomeomorph η).symm.surjective.range_eq] at h
  exact (irreducibleSpace_def _).mpr h

instance pointClosureScheme_isIntegral (η : X) : IsIntegral (pointClosureScheme η) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The closed subscheme has the dimension of the closure of the point. -/
theorem pointClosureScheme_topologicalKrullDim (η : X) :
    topologicalKrullDim (pointClosureScheme η) = topologicalKrullDim (closure ({η} : Set X)) :=
  IsHomeomorph.topologicalKrullDim_eq _ (pointClosureHomeomorph η).isHomeomorph

/-- The generic point of the closed subscheme maps to η. -/
theorem pointClosureι_genericPoint (η : X) :
    pointClosureι η (genericPoint (pointClosureScheme η)) = η := by
  have h := (genericPoint_spec (pointClosureScheme η)).image (pointClosureι η).continuous
  rw [Set.image_univ, range_pointClosureι, closure_closure] at h
  exact h.eq isGenericPoint_closure

theorem pointClosureι_specializes (η : X) (y : pointClosureScheme η) : η ⤳ pointClosureι η y := by
  have hy : pointClosureι η y ∈ closure ({η} : Set X) := by
    rw [← range_pointClosureι]
    exact Set.mem_range_self y
  exact specializes_iff_mem_closure.mpr hy

section Over

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]

/-- The closed subscheme is a scheme over K through X. -/
noncomputable instance pointClosureScheme_over (η : X) :
    (pointClosureScheme η).Over (Spec (CommRingCat.of K)) :=
  ⟨pointClosureι η ≫ (X ↘ Spec (CommRingCat.of K))⟩

instance pointClosureι_isOver (η : X) : (pointClosureι η).IsOver (Spec (CommRingCat.of K)) :=
  ⟨rfl⟩

instance pointClosureScheme_locallyOfFiniteType [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (η : X) : LocallyOfFiniteType (pointClosureScheme η ↘ Spec (CommRingCat.of K)) := by
  change LocallyOfFiniteType (pointClosureι η ≫ (X ↘ Spec (CommRingCat.of K)))
  infer_instance

end Over

end MixedFujita
