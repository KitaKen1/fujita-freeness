/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightSpecializationComparison

/-!
The realization sets in the point are stable under specialization (§2.2–2.3; step 9).

For a point y the normalized profiles realized at y (`sncWeightNormalizedProfiles`) come from
weights on proper simple normal crossing models whose support passes through a point of the fibre
of y. If y₁ specializes to y₂, a point of the fibre of y₁ in the intersection of the support has a
specialization in the fibre of y₂, because the model is proper over Y, so its image of the closure
of that point is closed and contains y₁; the specialization stays in the closures of the members
of the support. Hence every profile datum at y₁ is one at y₂ (`sncWeightProfiles_of_specializes`),
and the realization sets R_α = {y | α ∈ Q(y)} are stable under specialization
(`stableUnderSpecialization_realizationSet`).

On a noetherian scheme a set stable under specialization is closed exactly when it contains the
generic point of every irreducible closed subset in which it is dense. So of the closedness of the
sets R_α assumed for (6), the half "stable under specialization" is proved here; what remains is
that density part, which in the manuscript comes from Lemma 3 in families and the properness of
the flag variety.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A profile datum of a tuple at a point is a profile datum at every specialization of the
point. -/
theorem sncWeightProfiles_of_specializes (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) {y₁ y₂ : Y} (h : y₁ ⤳ y₂) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D y₁ s) :
    p ∈ sncWeightProfiles cY fY d D₀ D y₂ s := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y, hy, hwy⟩, hA, hv⟩ := hp
  have hcm : IsClosedMap π := π.isClosedMap
  have hcl : IsClosed (π '' closure ({y} : Set X)) := hcm _ isClosed_closure
  have hy₁ : y₁ ∈ π '' closure ({y} : Set X) := ⟨y, subset_closure rfl, hy⟩
  have hy₂ : y₂ ∈ π '' closure ({y} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hy₁) hcl (specializes_iff_mem_closure.mp h)
  obtain ⟨y', hy'cl, hy'⟩ := hy₂
  refine ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y', hy', fun k hk => ?_⟩, hA, hv⟩
  exact closure_minimal (Set.singleton_subset_iff.mpr (hwy k hk)) isClosed_closure hy'cl

/-- The normalized profiles realized at a point are realized at every specialization of it. -/
theorem sncWeightNormalizedProfiles_of_specializes (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor Y) (N : ℕ) {y₁ y₂ : Y} (h : y₁ ⤳ y₂) {q : Fin N → ℝ}
    (hq : q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y₁) :
    q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y₂ := by
  obtain ⟨B, p, hp, hp1, hqp⟩ := hq
  exact ⟨B, p, sncWeightProfiles_of_specializes cY fY d D₀ D h B hp, hp1, hqp⟩

/-- The realization sets in the point are stable under specialization. -/
theorem stableUnderSpecialization_realizationSet (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor Y) (N : ℕ) (q : Fin N → ℝ) :
    StableUnderSpecialization {y : Y | q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} :=
  fun _ _ h hy => sncWeightNormalizedProfiles_of_specializes cY fY d D₀ D N h hy

end MixedFujita
