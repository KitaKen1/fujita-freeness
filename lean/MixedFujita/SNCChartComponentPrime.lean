/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformUnitCharts

/-!
The coordinate of a member of a simple normal crossing family generates its prime (step 9,
strict transform charts).

On an affine open U, a section lies in the prime of a point of U exactly when the point is in its
zero locus (`mem_primeIdealOf_iff_mem_zeroLocus`). In a simple normal crossing chart c, a member
ξ_i of the family through the chart with coordinate a has closure ξ_i ∩ U = V(y_a) ∩ U, so the
ideal (y_a) of Γ(U) is the prime ideal of the point ξ_i
(`span_coordinate_eq_primeIdealOf_of_isSNCChart`): y_a vanishes at ξ_i, and a function vanishing
at ξ_i vanishes on its closure, hence on V(y_a) ∩ U, hence lies in the radical of (y_a), which
is (y_a) itself (the coordinate hyperplane of étale coordinates is reduced). In particular
Γ(U)/(y_a) is a domain (`span_coordinate_isPrime_of_isSNCChart`): for the strict transform H' of
a hyperplane the ring B = C/(y_0) of the strict transform charts (check-334) needs no localization,
and the kernel of C → B is the prime of the generic point of H'.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Prime

/-- A section of an affine open lies in the prime of a point exactly when the point is in its zero
locus. -/
theorem mem_primeIdealOf_iff_mem_zeroLocus {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (t : X) (ht : t ∈ U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf ⟨t, ht⟩).asIdeal ↔ t ∈ X.zeroLocus {f} := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
    mem_basicOpen_iff_notMem_primeIdealOf hU t ht f, not_not]

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- In a simple normal crossing chart, the coordinate of a member of the family through the chart
generates the prime ideal of the member. -/
theorem span_coordinate_eq_primeIdealOf_of_isSNCChart (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (i : Fin r) (a : Fin n)
    (hσ : σ i = some a) (hξ : ξ i ∈ c.U) :
    Ideal.span {c.coords (MvPolynomial.X a)} = (c.isAffine.primeIdealOf ⟨ξ i, hξ⟩).asIdeal := by
  have hloc : closure ({ξ i} : Set X) ∩ c.U =
      X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U := by
    have h := hc.2 i
    rw [hσ] at h
    exact h
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_primeIdealOf_iff_mem_zeroLocus c.isAffine (ξ i) hξ]
    have h : ξ i ∈ closure ({ξ i} : Set X) ∩ c.U := ⟨subset_closure rfl, hξ⟩
    rw [hloc] at h
    exact h.1
  · intro f hf
    apply (etaleChart_coordinate_span_isRadical c a)
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    -- the prime J is the prime of a point t of the chart
    let p : PrimeSpectrum Γ(X, c.U) := ⟨J, hJ⟩
    let t : c.U := c.isAffine.isoSpec.inv p
    have hpt : c.isAffine.primeIdealOf t = p := by
      change c.isAffine.isoSpec.hom (c.isAffine.isoSpec.inv p) = p
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hJt : J = (c.isAffine.primeIdealOf t).asIdeal := by rw [hpt]
    rw [hJt] at hIJ ⊢
    -- t lies on the closure of ξ i
    have ht0 : (t : X) ∈ X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) :=
      (mem_primeIdealOf_iff_mem_zeroLocus c.isAffine t t.2 _).mp
        (hIJ (Ideal.subset_span rfl))
    have htcl : (t : X) ∈ closure ({ξ i} : Set X) := by
      have h : (t : X) ∈ X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U :=
        ⟨ht0, t.2⟩
      rw [← hloc] at h
      exact h.1
    -- specialization of the primes
    have hsp : (⟨ξ i, hξ⟩ : c.U) ⤳ t :=
      (subtype_specializes_iff _ _).mpr (specializes_iff_mem_closure.mpr htcl)
    have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hsp.map c.isAffine.isoSpec.hom.continuous)
    exact hle hf

/-- In a simple normal crossing chart, the coordinate of a member of the family through the chart
generates a prime ideal. -/
theorem span_coordinate_isPrime_of_isSNCChart (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (i : Fin r) (a : Fin n)
    (hσ : σ i = some a) (hξ : ξ i ∈ c.U) :
    (Ideal.span {c.coords (MvPolynomial.X a)}).IsPrime := by
  rw [span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σ hc i a hσ hξ]
  exact (c.isAffine.primeIdealOf ⟨ξ i, hξ⟩).isPrime

end Prime

end MixedFujita
