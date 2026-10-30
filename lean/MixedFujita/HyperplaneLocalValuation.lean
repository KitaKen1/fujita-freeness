/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformBirational

/-!
Two inputs of the restriction theorem on a strict transform (step 9).

The local ring of a smooth K-domain A at a nonzero principal prime (x) is a valuation ring
(`valuationRing_localization_span_of_smooth`): the prime has height one by Krull's principal ideal
theorem, so it is a codimension-one point of the smooth scheme Spec A, whose stalk, a localization
of A at (x), is a discrete valuation ring; valuation rings transfer along ring isomorphisms
(`valuationRing_of_ringEquiv`). For the hyperplane x_0 = 0 of étale coordinates this is the
valuation ring hypothesis of the strict transform model (check-329). Formally étale coordinates on
a K-algebra of finite presentation are étale (`etale_of_formallyEtale_of_finitePresentation`), the
étaleness hypothesis of the affine model criterion (check-327) for localized quotients.

In a preconnected finite union of closed sets, a nonempty member meets some other member as soon
as another member is nonempty (`exists_ne_inter_nonempty_of_isPreconnected`): otherwise it and the
union of the others would separate the union. Applied to the non-klt components over a point, this
turns the connectedness lemma into a component meeting the strict transform over the point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Valuation

/-- A valuation ring structure transfers along a ring isomorphism. -/
theorem valuationRing_of_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [ValuationRing R] (e : R ≃+* S) : ValuationRing S where
  cond' a b := by
    obtain ⟨c, hc⟩ := ValuationRing.cond (e.symm a) (e.symm b)
    refine ⟨e c, ?_⟩
    rcases hc with hc | hc
    · left
      rw [← e.apply_symm_apply a, ← map_mul, hc, e.apply_symm_apply]
    · right
      rw [← e.apply_symm_apply b, ← map_mul, hc, e.apply_symm_apply]

variable {K : Type u} [Field K]

attribute [local instance] specAlgebraOver

/-- The localization of a smooth K-domain at a nonzero principal prime is a valuation ring. -/
theorem valuationRing_localization_span_of_smooth (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.Smooth K A] (x : A) (hx : x ≠ 0) [(Ideal.span {x}).IsPrime] :
    ValuationRing (Localization.AtPrime (Ideal.span {x})) := by
  have hsm := specAlgebraOver_smooth (K := K) A
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let P : Ideal A := Ideal.span {x}
  let e : Spec (CommRingCat.of A) := ⟨P, inferInstance⟩
  have hcoh : Order.coheight e = 1 := by
    rw [← idealHeight_eq_coheight]
    change P.height = 1
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
        (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro h
      apply hx
      have hmem : x ∈ P := Ideal.subset_span rfl
      rw [h] at hmem
      exact (Submodule.mem_bot A).mp hmem
  let eC : CodimensionOnePoint (Spec (CommRingCat.of A)) := ⟨e, hcoh⟩
  haveI := smoothScheme_stalk_isDomain (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) e
  haveI : IsDiscreteValuationRing ((Spec (CommRingCat.of A)).presheaf.stalk (eC : _)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eC
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk e) := StructureSheaf.stalkAlgebra A e
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk e) P :=
    StructureSheaf.IsLocalization.to_stalk A e
  exact valuationRing_of_ringEquiv (IsLocalization.algEquiv P.primeCompl
    ((Spec (CommRingCat.of A)).presheaf.stalk e) (Localization.AtPrime P)).toRingEquiv

/-- Formally étale coordinates on a K-algebra of finite presentation are étale. -/
theorem etale_of_formallyEtale_of_finitePresentation {B : Type*} [CommRing B] [Algebra K B]
    [Algebra.FinitePresentation K B] {n : ℕ} (v : MvPolynomial (Fin n) K →ₐ[K] B)
    (hv : v.toRingHom.FormallyEtale) : v.toRingHom.Etale := by
  letI : Algebra (MvPolynomial (Fin n) K) B := v.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) B :=
    IsScalarTower.of_algebraMap_eq fun k => (v.commutes k).symm
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) K) B := hv
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin n) K) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation K
      (MvPolynomial (Fin n) K) B
  exact (Algebra.etale_iff (MvPolynomial (Fin n) K) B).mpr ⟨inferInstance, inferInstance⟩

end Valuation

section Connected

/-- In a preconnected finite union of closed sets, a nonempty member meets another member when
some other member is nonempty. -/
theorem exists_ne_inter_nonempty_of_isPreconnected {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsClosed (Z i)) (hconn : IsPreconnected (⋃ i, Z i))
    (b : ι) (hb : (Z b).Nonempty) (a : ι) (hab : a ≠ b) (ha : (Z a).Nonempty) :
    ∃ i, i ≠ b ∧ (Z i ∩ Z b).Nonempty := by
  classical
  let V : Set X := ⋃ i ∈ {i | i ≠ b}, Z i
  have hV : IsClosed V := by
    have : ({i | i ≠ b} : Set ι).Finite := Set.toFinite _
    exact this.isClosed_biUnion fun i _ => hZ i
  have hcover : (⋃ i, Z i) ⊆ Z b ∪ V := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    by_cases hib : i = b
    · subst hib
      exact Or.inl hi
    · exact Or.inr (Set.mem_biUnion (show i ∈ {i | i ≠ b} from hib) hi)
  obtain ⟨p, -, hpb, hpV⟩ := (isPreconnected_closed_iff.mp hconn) (Z b) V (hZ b) hV hcover
    (by obtain ⟨q, hq⟩ := hb; exact ⟨q, Set.mem_iUnion.mpr ⟨b, hq⟩, hq⟩)
    (by obtain ⟨q, hq⟩ := ha; exact ⟨q, Set.mem_iUnion.mpr ⟨a, hq⟩,
      Set.mem_biUnion (show a ∈ {i | i ≠ b} from hab) hq⟩)
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hpV
  exact ⟨i, hi, p, hpi, hpb⟩

end Connected

end MixedFujita
