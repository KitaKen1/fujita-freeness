/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartComponentPrime

/-!
Pulling back into the coordinate ideal of a member of a simple normal crossing family (step 9,
strict transform charts).

For a point x of Spec R, the prime of x on the affine open ⊤ corresponds to the prime ideal of x
(`mem_primeIdealOf_top_spec_iff`), and for a morphism ρ : T → Spec A and an affine open V of T,
the pullback of a ∈ A lies in the prime of a point t of V exactly when a lies in the prime of ρ(t)
(`appLE_mem_primeIdealOf_iff`, the contraction of primes along ρ). In a simple normal crossing
chart in which a member ξ_i has coordinate y_a, the ideal (y_a) is the prime of ξ_i (check-335),
so a ∈ A pulls back into (y_a) exactly when a vanishes at ρ(ξ_i)
(`appLE_mem_span_coordinate_iff`). For the strict transform H' of the hyperplane x_0 = 0 this
gives both μ(x_0) ∈ (y_0) and the kernel condition of the strict transform charts (check-334): a
pulls back to zero in C/(y_0) exactly when a lies in the prime (x_0) of the generic point of H.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Pullback

/-- The prime of a point of Spec R on the affine open ⊤ is its prime ideal. -/
theorem mem_primeIdealOf_top_spec_iff {R : CommRingCat.{u}} (x : Spec R) (r : R) :
    (Scheme.ΓSpecIso R).inv r ∈ ((isAffineOpen_top (Spec R)).primeIdealOf ⟨x, trivial⟩).asIdeal ↔
      r ∈ x.asIdeal := by
  rw [← not_iff_not, ← mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top _) _ trivial,
    basicOpen_eq_of_affine]
  rfl

/-- The pullback of a function of A lies in the prime of a point t of an affine open of T exactly
when the function lies in the prime of ρ(t). -/
theorem appLE_mem_primeIdealOf_iff {A : Type u} [CommRing A] {T : Scheme.{u}}
    (ρ : T ⟶ Spec (CommRingCat.of A)) {V : T.Opens} (hV : IsAffineOpen V) (t : T) (ht : t ∈ V)
    (a : A) :
    ρ.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) ∈
        (hV.primeIdealOf ⟨t, ht⟩).asIdeal ↔ a ∈ (ρ t).asIdeal := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := ρ) ⊤ (isAffineOpen_top _) V hV le_top ht
  rw [← mem_primeIdealOf_top_spec_iff (ρ t) a, ← h]
  rfl

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- In a simple normal crossing chart in which the member ξ_i has coordinate y_a, a function of A
pulls back into (y_a) exactly when it vanishes at ρ(ξ_i). -/
theorem appLE_mem_span_coordinate_iff {A : Type u} [CommRing A]
    (ρ : T ⟶ Spec (CommRingCat.of A)) (c : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (i : Fin r) (a : Fin n)
    (hσ : σ i = some a) (hξ : ξ i ∈ c.U) (f : A) :
    ρ.appLE ⊤ c.U le_top ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f) ∈
        Ideal.span {c.coords (MvPolynomial.X a)} ↔ f ∈ (ρ (ξ i)).asIdeal := by
  rw [span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σ hc i a hσ hξ]
  exact appLE_mem_primeIdealOf_iff ρ c.isAffine (ξ i) hξ f

end Pullback

end MixedFujita
