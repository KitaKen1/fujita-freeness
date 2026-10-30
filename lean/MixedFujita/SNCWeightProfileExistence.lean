/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightInfimum
public import MixedFujita.HironakaSNCModelExistence

/-!
Nonemptiness of the actual profile spaces, without an assumed resolution or fibre point.
Hironaka supplies a proper dominant SNC model; proper dominance supplies a point over x.
Its zero weight realizes (0,0), so N belongs to the objective values of every N-element basis.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- A zero profile is realized at every point for every tuple of nonzero sections. -/
theorem sncWeightProfiles_zero_of_nonzero_sections (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ}
    (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) :
    ((0 : ℝ), fun _ => (0 : ℝ)) ∈ sncWeightProfiles cY fY d D₀ D x s := by
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc,
    hBsupp, hGsupp⟩ := exists_proper_snc_model_with cY fY d D₀
      (fun i => cartierSectionZeroDivisor D (s i) (hs i))
  obtain ⟨y, hy⟩ := surjective_of_isProper_of_isDominant π x
  refine ⟨hs, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ,
    fun _ => 0, hinj, hξ, hsnc, hBsupp, hGsupp, fun _ => le_rfl,
    ⟨y, hy, fun k hk => absurd rfl hk⟩, ?_, fun i => ?_⟩ <;> simp

/-- The objective values are nonempty for every basis: its zero profile has objective N.
This also covers N = 0 and arbitrary real t and j. -/
theorem sncWeightObjectiveValues_natCast_mem (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ}
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (t j : ℝ) :
    (N : ℝ) ∈ sncWeightObjectiveValues cY fY d D₀ D x N t j := by
  refine ⟨B, (0, fun _ => 0),
    sncWeightProfiles_zero_of_nonzero_sections cY fY d D₀ D x B B.ne_zero, ?_⟩
  simp

end MixedFujita
