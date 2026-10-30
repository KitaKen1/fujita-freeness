/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentAppend

/-!
The actual smooth zero scheme of a general section has finitely many component generic points.
Their images are distinct, their closures partition the actual zero locus, and they append to
the existing point-indexed SNC family. The component family may be empty. No global or geometric
irreducibility, prescribed-point Bertini statement, or codimension calculation is asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Mapped component closures are disjoint whenever the source stalks are domains. -/
theorem closedImmersion_component_closures_disjoint {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsClosedImmersion f] [∀ y : Y, IsDomain (Y.presheaf.stalk y)] :
    Pairwise fun η ζ : genericPoints Y =>
      Disjoint (closure ({f η} : Set X)) (closure ({f ζ} : Set X)) := by
  intro η ζ hne
  have hCne : closure ({η.1} : Set Y) ≠ closure ({ζ.1} : Set Y) := by
    intro heq
    apply hne
    exact genericPoints.component_injective (Subtype.ext heq)
  have hd := scheme_components_pairwise_disjoint η.2 ζ.2 hCne
  rw [closedImmersion_genericPoint_closure, closedImmersion_genericPoint_closure,
    Set.disjoint_left]
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
  have heq := f.isClosedEmbedding.injective hzy
  subst z
  exact Set.disjoint_left.mp hd hy hz

/-- Enumerate the source component generic points and convert a smooth closed image to SNC. -/
theorem closedSmoothImage_snc_components {K : Type u} [Field K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [NoetherianSpace Y]
    (f : Y ⟶ X) [IsClosedImmersion f]
    [Smooth (f ≫ (X ↘ Spec (CommRingCat.of K)))] {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamilyWith K n ξ (Set.range f)) :
    ∃ (q : ℕ) (η : Fin q → X), Function.Injective η ∧
      Set.range η = f '' genericPoints Y ∧
      Set.range f = ⋃ j, closure ({η j} : Set X) ∧
      (Pairwise fun i j => Disjoint (closure ({η i} : Set X))
        (closure ({η j} : Set X))) ∧ IsSNCFamily K n (Fin.append ξ η) := by
  classical
  let : ∀ y : Y, IsDomain (Y.presheaf.stalk y) :=
    fun y => smoothScheme_stalk_isDomain (f ≫ (X ↘ Spec (CommRingCat.of K))) y
  let : Fintype (genericPoints Y) :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).fintype
  let e : Fin (Fintype.card (genericPoints Y)) ≃ genericPoints Y :=
    (Fintype.equivFin (genericPoints Y)).symm
  let η := fun j => f (e j)
  have hinj : Function.Injective η := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact f.isClosedEmbedding.injective hij
  have hrange : Set.range η = f '' genericPoints Y := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, (e j).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨y, hy⟩
      exact ⟨j, by simp only [η, hj]⟩
  have hcover : Set.range f = ⋃ j, closure ({η j} : Set X) := by
    rw [closedImmersion_image_eq_iUnion_genericPoint_closures f]
    exact (e.surjective.iUnion_comp (fun a : genericPoints Y =>
      closure ({f a} : Set X))).symm
  have hdis : Pairwise fun i j => Disjoint (closure ({η i} : Set X))
      (closure ({η j} : Set X)) := by
    intro i j hne
    exact closedImmersion_component_closures_disjoint f (fun h => hne (e.injective h))
  exact ⟨_, η, hinj, hrange, hcover, hdis,
    isSNCFamily_append_of_disjoint_components η hξ hcover hdis⟩

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- Every member in a nonempty general parameter open supplies an actual finite SNC component
family, through the generic points of its actual smooth closed zero scheme. -/
theorem cartierSections_general_nonzero_smooth_snc_components [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∃ hst : (∑ i, t i • s i) ≠ 0,
          Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
            (X ↘ Spec (CommRingCat.of K))) ∧
          ∃ (q : ℕ) (η : Fin q → X), Function.Injective η ∧
            Set.range η = (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst) ''
              genericPoints (cartierSectionZeroScheme D (∑ i, t i • s i) hst) ∧
            cartierSectionZeroLocus D (∑ i, t i • s i) =
              ⋃ j, closure ({η j} : Set X) ∧
            (Pairwise fun i j => Disjoint (closure ({η i} : Set X))
              (closure ({η j} : Set X))) ∧ IsSNCFamily K n (Fin.append ξ η) := by
  classical
  let : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K)) }
  obtain ⟨p, hp, hpex, hgood⟩ := cartierSections_general_nonzero_smooth_snc D s hs ξ hξ
  refine ⟨p, hp, hpex, fun t ht => ?_⟩
  obtain ⟨hst, hsm, hsnc⟩ := hgood t ht
  let f := cartierSectionZeroSchemeι D (∑ i, t i • s i) hst
  let : IsClosedImmersion f := cartierSectionZeroSchemeι_isClosedImmersion D _ hst
  let : NoetherianSpace (cartierSectionZeroScheme D (∑ i, t i • s i) hst) :=
    f.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : Smooth (f ≫ (X ↘ Spec (CommRingCat.of K))) := hsm
  obtain ⟨q, η, hinj, hrange, hcover, hdis, hfamily⟩ := closedSmoothImage_snc_components f ξ hsnc
  rw [cartierSectionZeroSchemeι_range (K := K)] at hcover
  exact ⟨hst, hsm, q, η, hinj, hrange, hcover, hdis, hfamily⟩

end MixedFujita
