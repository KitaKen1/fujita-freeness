/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionZeroComponents
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
The component generic points of a nonzero Cartier section have codimension one. The actual
affine quotient cover puts their primes among the minimal primes of the coefficient principal
ideal. Krull's principal ideal theorem gives the upper height bound, and the nonzero coefficient
on the integral ambient scheme gives the lower bound. Combined with the preceding SNC theorem,
this supplies an actual finite family of prime divisors; no irreducibility of the whole cut is
needed and the family is allowed to be empty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A component generic point is maximal for the specialization order. -/
theorem scheme_component_genericPoint_coheight_zero {Y : Scheme.{u}}
    (η : genericPoints Y) : Order.coheight η.1 = 0 := by
  apply Order.coheight_eq_zero.mpr
  intro z hz
  apply Scheme.le_iff_specializes.mpr
  apply specializes_iff_closure_subset.mpr
  exact η.2.2 isIrreducible_singleton.closure
    (Scheme.le_iff_specializes.mp hz).closure_subset

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

include K in
/-- Every component of the actual zero scheme of a nonzero Cartier section has codimension one. -/
theorem cartierSectionZeroScheme_component_coheight_one [IsLocallyNoetherian X]
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (η : genericPoints (cartierSectionZeroScheme D s hs)) :
    Order.coheight (cartierSectionZeroSchemeι D s hs η) = 1 := by
  let I := cartierSectionZeroIdeal D s hs
  let x := cartierSectionZeroSchemeι D s hs η
  obtain ⟨f, hfx⟩ := D.exists_isLocalEquationAt x
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hfx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  change IsAffineOpen U at hU
  let A : X.affineOpens := ⟨U, hU⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hf := CartierDivisor.rationalUnitClass_eq_of_le hUV hV
  let g := cartierGlobalOpenCoefficient (K := K) D U f hf s
  have hg : g ≠ 0 := cartierGlobalOpenCoefficient_ne_zero (K := K) D U f hf s hs
  have hideal : I.ideal A = Ideal.span ({g} : Set Γ(X, U)) :=
    cartierSectionZeroIdeal_ideal_eq_span (K := K) D s hs A f hf
  have hηU : η.1 ∈ (I.subschemeCover.f A).opensRange := by
    rw [I.opensRange_subschemeCover_map]
    exact hxU
  obtain ⟨z, hzi⟩ := hηU
  have hz0 : Order.coheight z = 0 := by
    rw [← coheight_eq_of_isOpenImmersion (x := z) (I.subschemeCover.f A), hzi]
    exact scheme_component_genericPoint_coheight_zero η
  have hzmin : z.asIdeal ∈ minimalPrimes (Γ(X, U) ⧸ I.ideal A) := by
    apply Ideal.height_eq_zero_iff.mp
    rw [idealHeight_eq_coheight, hz0]
  let q : Spec (CommRingCat.of Γ(X, U)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal A))) z
  have hqmin : q.asIdeal ∈ (I.ideal A).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨z.asIdeal, hzmin, rfl⟩
  rw [hideal] at hqmin
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian A
  have hq1 : q.asIdeal.height = 1 := by
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hqmin
    · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hg)).trans (Ideal.height_mono hqmin.1.2)
  have hpoint : hU.fromSpec q = cartierSectionZeroSchemeι D s hs η := by
    change hU.fromSpec q = I.subschemeι η.1
    have heq := I.subschemeCover_map_subschemeι A
    rw [I.glueDataObjι_ι] at heq
    have heqp := congrArg (fun e => e z) heq
    convert heqp.symm using 1 <;> simp only [Scheme.Hom.comp_apply, hzi, q, A,
      IsAffineOpen.fromSpec] <;> rfl
  calc
    Order.coheight (cartierSectionZeroSchemeι D s hs η) = Order.coheight (hU.fromSpec q) :=
      congrArg Order.coheight hpoint.symm
    _ = Order.coheight q := coheight_eq_of_isOpenImmersion hU.fromSpec
    _ = q.asIdeal.height := (idealHeight_eq_coheight _ q).symm
    _ = 1 := hq1

/-- General nonzero smooth cuts supply distinct codimension-one points in the ordinary SNC
family interface, with closures covering the actual zero locus. -/
theorem cartierSections_general_nonzero_smooth_prime_snc [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∃ (hst : (∑ i, t i • s i) ≠ 0) (q : ℕ) (η : Fin q → X),
          Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
            (X ↘ Spec (CommRingCat.of K))) ∧ Function.Injective η ∧
          (∀ j, Order.coheight (η j) = 1) ∧
          Set.range η = (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst) ''
            genericPoints (cartierSectionZeroScheme D (∑ i, t i • s i) hst) ∧
          cartierSectionZeroLocus D (∑ i, t i • s i) = ⋃ j, closure ({η j} : Set X) ∧
          (Pairwise fun i j => Disjoint (closure ({η i} : Set X))
            (closure ({η j} : Set X))) ∧ IsSNCFamily K n (Fin.append ξ η) := by
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨p, hp, hpex, hgood⟩ :=
    cartierSections_general_nonzero_smooth_snc_components D s hs ξ hξ
  refine ⟨p, hp, hpex, fun t ht => ?_⟩
  obtain ⟨hst, hsm, q, η, hinj, hrange, hcover, hdis, hfamily⟩ := hgood t ht
  refine ⟨hst, q, η, hsm, hinj, ?_, hrange, hcover, hdis, hfamily⟩
  intro j
  have hj : η j ∈ (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst) ''
      genericPoints (cartierSectionZeroScheme D (∑ i, t i • s i) hst) :=
    hrange ▸ Set.mem_range_self j
  obtain ⟨z, hz, hzi⟩ := hj
  rw [← hzi]
  exact cartierSectionZeroScheme_component_coheight_one (K := K) D _ hst ⟨z, hz⟩

end MixedFujita
