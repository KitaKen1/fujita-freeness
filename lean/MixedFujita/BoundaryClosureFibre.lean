/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveClosureFibreIntegral
public import MixedFujita.SNCPointDivisorFamily
public import MixedFujita.RadicalIdealSubschemeReduced
public import Hironaka.Scheme.Snc.EraseFamily
public import Hironaka.Scheme.Snc.HasSncWith
public import Hironaka.Scheme.Snc.RelativeDimensionConstant

/-!
The boundary components spread out with integral fibres (step 10, R4-3).

Let `T` be a smooth integral closed subscheme of projective space over an algebraically closed
field `K`, with a simple normal crossing family `ξ`. The boundary component `E_k`, the reduced
closed subscheme on the closure of `ξ_k` (`boundaryComponentIdeal`), is integral
(`boundaryComponent_isIntegral`) and smooth over `K` (Hironaka's `hasSncWith_component` and
`HasSncWith.smooth`). Check 517 applied to `E_k → T → P_K` shows that the fibres of its closure
`E_{k,A}` over the fields avoiding one nonzero element are integral
(`exists_fg_forall_exists_ne_zero_isIntegral_boundaryFibre`).

The closure `E_{k,A}` lies in the closure `T_A` (`boundaryClosureInclusion`: the kernel of
`T → P_A` is contained in that of `E_k → P_A`). Over a fibre `T_κ = T_A ×_A κ`, the base change
`E_{k,A} ×_{T_A} T_κ` (`boundaryFibre`) is the fibre of `E_{k,A}` (`boundaryFibreIso`), so it is
integral when that fibre is. The image of its generic point (`boundaryFibrePoint`) is a point of
`T_κ` whose closure is the preimage of `E_{k,A}` (`closure_boundaryFibrePoint`): the point of the
simple normal crossing family of `T_κ` for check 491.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Component

variable {K : Type u} [Field K] {T : Scheme.{u}} {r : ℕ} (ξ : Fin r → T)

/-- The boundary component `E_k`: the reduced closed subscheme on the closure of `ξ k`. -/
noncomputable abbrev boundaryComponentIdeal (k : Fin r) : T.IdealSheafData :=
  (sncDivisorFamilyOfPoints ξ).component (ULift.up k)

/-- **The boundary components are integral**: reduced (a vanishing ideal) with irreducible
support (the closure of a point). -/
theorem boundaryComponent_isIntegral (k : Fin r) :
    IsIntegral (boundaryComponentIdeal ξ k).subscheme := by
  let J := boundaryComponentIdeal ξ k
  have hsupport : (J.support : Set T) = closure ({ξ k} : Set T) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hred : IsReduced J.subscheme :=
    idealSheaf_subscheme_isReduced_of_affine_radical J
      (fun U => PrimeSpectrum.isRadical_vanishingIdeal _)
  have hrange : IsIrreducible (Set.range J.subschemeι) := by
    rw [J.range_subschemeι, hsupport]
    exact isIrreducible_singleton.closure
  have hirr : IrreducibleSpace J.subscheme :=
    J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
      (isIrreducible_iff_irreducibleSpace.mp hrange)
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, hred⟩

variable [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {d : ℕ}

/-- The boundary components are simple normal crossing strata of the family. -/
theorem boundaryComponent_hasSncWith (hsnc : IsSNCFamily K d ξ) (k : Fin r) :
    (sncDivisorFamilyOfPoints ξ).HasSncWith (boundaryComponentIdeal ξ k) :=
  Scheme.DivisorFamily.hasSncWith_component _ (sncDivisorFamilyOfPoints_isSncAt ξ hsnc) _

/-- **The boundary components are smooth.** -/
theorem boundaryComponent_smooth [PerfectField K] [Smooth (T ↘ Spec (CommRingCat.of K))]
    (hsnc : IsSNCFamily K d ξ) (k : Fin r) :
    Smooth ((boundaryComponentIdeal ξ k).subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) :=
  HasSncWith.smooth (T ↘ Spec (CommRingCat.of K)) (boundaryComponent_hasSncWith ξ hsnc k)

end Component

section Closure

variable {n d r : ℕ} {K : Type u} [Field K] [IsAlgClosed K] {T : Scheme.{u}} [IsIntegral T]
  [T.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension d (T ↘ Spec (CommRingCat.of K))]
  (e : T ⟶ polynomialProjectiveScheme n K) (ξ : Fin r → T)

/-- **The closures of the boundary components have integral fibres away from one element.** -/
theorem exists_fg_forall_exists_ne_zero_isIntegral_boundaryFibre [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K))
    (hsnc : IsSNCFamily K d ξ) (k : Fin r) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ A : Subalgebra ℤ K, A₀ ≤ A → A.FG →
      ∃ f : A, f ≠ 0 ∧ ∀ (κ : Type u) [Field κ] [Algebra A κ], IsUnit (algebraMap A κ f) →
        IsIntegral (pullback
          (projectiveClosureι (algebraMap A K) ((boundaryComponentIdeal ξ k).subschemeι ≫ e) ≫
            polynomialProjectiveToBase n A)
          (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth d _
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (CommRingCat.of K))
  let J := boundaryComponentIdeal ξ k
  have : IsIntegral J.subscheme := boundaryComponent_isIntegral ξ k
  have : Smooth (J.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) :=
    boundaryComponent_smooth ξ hsnc k
  obtain ⟨m, hm⟩ := exists_smoothOfRelativeDimension_of_preconnectedSpace
    (J.subschemeι ≫ (T ↘ Spec (CommRingCat.of K)))
  exact exists_fg_forall_exists_ne_zero_isIntegral_fibre
    (J.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) m (J.subschemeι ≫ e)
    (by rw [Category.assoc, he])

end Closure

section Inclusion

variable {n r : ℕ} {K : Type u} [Field K] {T : Scheme.{u}} (e : T ⟶ polynomialProjectiveScheme n K)
  (ξ : Fin r → T) {A : Type u} [CommRing A] (c : A →+* K)

/-- **The closure of a boundary component lies in the closure of `T`.** -/
noncomputable def boundaryClosureInclusion (k : Fin r) :
    projectiveClosure c ((boundaryComponentIdeal ξ k).subschemeι ≫ e) ⟶ projectiveClosure c e :=
  Scheme.IdealSheafData.inclusion (by
    have h := Scheme.Hom.le_ker_comp (boundaryComponentIdeal ξ k).subschemeι
      (e ≫ polynomialProjectiveCoefficientMap c)
    rwa [← Category.assoc] at h)

theorem boundaryClosureInclusion_ι (k : Fin r) :
    boundaryClosureInclusion e ξ c k ≫ projectiveClosureι c e =
      projectiveClosureι c ((boundaryComponentIdeal ξ k).subschemeι ≫ e) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The inclusion of the closure of a boundary component is a closed immersion. -/
instance boundaryClosureInclusion_isClosedImmersion (k : Fin r) :
    IsClosedImmersion (boundaryClosureInclusion e ξ c k) := by
  have : IsClosedImmersion (boundaryClosureInclusion e ξ c k ≫ projectiveClosureι c e) := by
    rw [boundaryClosureInclusion_ι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (projectiveClosureι c e)

variable (κ : Type u) [Field κ] [Algebra A κ]

/-- The base change `E_{k,A} ×_{T_A} T_κ` of the closure of a boundary component to the fibre. -/
noncomputable abbrev boundaryFibre (k : Fin r) : Scheme.{u} :=
  pullback (boundaryClosureInclusion e ξ c k)
    (pullback.fst (projectiveClosureι c e ≫ polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A κ))))

/-- `E_{k,A} ×_{T_A} T_κ` is the fibre `E_{k,A} ×_A κ`. -/
noncomputable def boundaryFibreIso (k : Fin r) :
    boundaryFibre e ξ c κ k ≅ pullback
      (projectiveClosureι c ((boundaryComponentIdeal ξ k).subschemeι ≫ e) ≫
        polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A κ))) :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom (by rw [← Category.assoc, boundaryClosureInclusion_ι]) rfl

/-- The base change to the fibre is integral if the fibre of the closure is. -/
theorem boundaryFibre_isIntegral (k : Fin r)
    [IsIntegral (pullback
      (projectiveClosureι c ((boundaryComponentIdeal ξ k).subschemeι ≫ e) ≫
        polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A κ))))] :
    IsIntegral (boundaryFibre e ξ c κ k) := by
  have : Nonempty (boundaryFibre e ξ c κ k) :=
    ⟨(boundaryFibreIso e ξ c κ k).inv (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion (boundaryFibreIso e ξ c κ k).hom

/-- **The point of the fibre boundary**: the image in `T_κ` of the generic point of
`E_{k,A} ×_{T_A} T_κ`. -/
noncomputable def boundaryFibrePoint (k : Fin r) [IsIntegral (boundaryFibre e ξ c κ k)] :
    ↥(pullback (projectiveClosureι c e ≫ polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) :=
  pullback.snd (boundaryClosureInclusion e ξ c k)
    (pullback.fst (projectiveClosureι c e ≫ polynomialProjectiveToBase n A)
      (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
    (genericPoint (boundaryFibre e ξ c κ k))

/-- **The closure of the point of the fibre boundary is the preimage of the closure of the
boundary component.** -/
theorem closure_boundaryFibrePoint (k : Fin r) [IsIntegral (boundaryFibre e ξ c κ k)] :
    closure ({boundaryFibrePoint e ξ c κ k} : Set _) =
      (pullback.fst (projectiveClosureι c e ≫ polynomialProjectiveToBase n A)
        (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) ⁻¹'
        Set.range (boundaryClosureInclusion e ξ c k) := by
  rw [← Scheme.Pullback.range_snd]
  apply subset_antisymm
  · exact closure_minimal (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
      (Scheme.Hom.isClosedEmbedding _).isClosed_range
  · rintro _ ⟨z, rfl⟩
    exact specializes_iff_mem_closure.1
      (((genericPoint_spec (boundaryFibre e ξ c κ k)).specializes (Set.mem_univ z)).map
        (Scheme.Hom.continuous _))

end Inclusion

end MixedFujita
