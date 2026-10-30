/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionsSteinDescent
public import MixedFujita.SteinCartierGradedDescent

/-!
Connect the full graded Cartier section comparison to the actual normal Stein target already
constructed from ordinary global generation. All targets, maps, ample divisors and actual
linear equivalences are constructed internally. If only sufficiently large multiples of D
are free, one positive q is chosen internally: the same target and ample H identify the full
section spaces in every degree j q D. This does not yet descend D itself by consecutive free
multiples, or identify the target dimension with the Iitaka dimension of D.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseSectionScalarTower

/-- Ordinary global generation constructs one actual normal proper Stein target which
identifies all graded section spaces, global generation and Iitaka growth. -/
theorem cartierGloballyGenerated_exists_normal_stein_full_graded_descent
    (D : CartierDivisor X) (hD : CartierIsGloballyGenerated D)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsProper (Y ↘ Spec (CommRingCat.of K)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      D = cartierPullback g H + principalCartierDivisor X φ ∧
      (∀ q : ℕ, Nonempty (Γ((q • D).sheaf, ⊤) ≃ₗ[K] Γ((q • H).sheaf, ⊤))) ∧
      (∀ q : ℕ, CartierIsGloballyGenerated (q • D) ↔ CartierIsGloballyGenerated (q • H)) ∧
      (∀ k : ℕ, CartierIitakaDimension K D k ↔ CartierIitakaDimension K H k) := by
  obtain ⟨r, hr, Y, hY, hYN, hYO, g, hgd, h, H, φ, hg, hh, hbase, hgbase,
    happ, hconn, hnormY, hp, heff, hgg, hsga, hamp, hdesc⟩ :=
    cartierGloballyGenerated_exists_normal_stein_descended_divisor (K := K) D hD hnorm
  letI := hY
  letI := hYN
  letI := hYO
  letI := hgd
  letI := hg
  letI := hp
  letI : g.IsOver (Spec (CommRingCat.of K)) := ⟨hgbase⟩
  refine ⟨Y, hY, hYN, hYO, inferInstance, g, hgd, inferInstance, H, φ, hg, hp,
    hnormY, happ, hconn, heff, hgg, hamp, hdesc, ?_, ?_, ?_⟩
  · intro q
    exact ⟨steinCartierGradedSectionEquiv K g (fun U => (happ U).2) D H φ hdesc q⟩
  · intro q
    exact stein_globallyGenerated_graded_iff_of_eq_pullback_add_principal K g
      (fun U => (happ U).2) D H φ hdesc (surjective_of_isProper_of_isDominant g) q
  · intro k
    exact stein_cartierIitakaDimension_iff_of_eq_pullback_add_principal K g
      (fun U => (happ U).2) D H φ hdesc k

/-- Eventual freeness supplies one internally chosen positive free multiple whose entire
divisible graded series lives on the same constructed normal proper Stein target. -/
theorem eventuallyGloballyGenerated_exists_normal_stein_divisible_graded_descent
    (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ q : ℕ, 0 < q ∧ ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsProper (Y ↘ Spec (CommRingCat.of K)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      q • D = cartierPullback g H + principalCartierDivisor X φ ∧
      (∀ j : ℕ, Nonempty (Γ((j • (q • D)).sheaf, ⊤) ≃ₗ[K] Γ((j • H).sheaf, ⊤))) ∧
      (∀ j : ℕ, CartierIsGloballyGenerated (j • (q • D)) ↔ CartierIsGloballyGenerated (j • H)) ∧
      (∀ k : ℕ, CartierIitakaDimension K (q • D) k ↔ CartierIitakaDimension K H k) := by
  obtain ⟨q₀, hq₀⟩ := hfree
  let q := max q₀ 1
  obtain ⟨Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ, hprops⟩ :=
    cartierGloballyGenerated_exists_normal_stein_full_graded_descent (K := K) (q • D)
      (hq₀ q (le_max_left _ _)) hnorm
  exact ⟨q, lt_of_lt_of_le one_pos (le_max_right _ _), Y, hY, hYN, hYO, hYft, g, hgd,
    hgo, H, φ, hprops⟩

end MixedFujita
