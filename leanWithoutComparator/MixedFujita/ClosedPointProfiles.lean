/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedPointLocus
public import MixedFujita.KltVolumeInterior
public import MixedFujita.RealizationSetsPrincipalShift

/-!
Point specialization and all-degree profile transfer from closedness at closed points only.
The generic point is tested in the closed representative of a profile locus, never in the raw
locus defined with K-valued bases. This avoids an unjustified extension of closed-point data to
nonclosed points. Principal shifts preserve this corrected hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
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

/-- The specialization comparison (6) only needs closed representatives agreeing at closed
points. Both the specified point and the comparison points are closed; w need not be closed. -/
theorem sncWeight_specialization_comparison_of_closedPoints (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ D : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : 0 < j) (t : ℝ)
    (hcl : ∀ α : Fin N → ℚ, IsClosedOnClosedPoints {y : Y |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y})
    {w x : Y} (hxc : IsClosed ({x} : Set Y)) (hwx : w ⤳ x) :
    ∃ Z : ℕ → Set Y, (∀ i, IsClosed (Z i)) ∧ (∀ i, w ∉ Z i) ∧
      ∀ y : Y, IsClosed ({y} : Set Y) →
        (sncWeightObjectiveValues cY fY d D₀ D y N t j).Nonempty → (∀ i, y ∉ Z i) →
        sncWeightInfimum cY fY d D₀ D x N t j ≤ sncWeightInfimum cY fY d D₀ D y N t j := by
  classical
  choose R hR hrep using hcl
  obtain ⟨f, hf⟩ := exists_surjective_nat (Fin N → ℚ)
  refine ⟨fun k => if w ∈ R (f k) then ∅ else R (f k), fun k => ?_, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact isClosed_empty
    · exact hR _
  · dsimp only
    split_ifs with h
    · exact Set.notMem_empty w
    · exact h
  · intro y hyc hne hyZ
    refine sncWeightInfimum_le_of_rational cY fY hd D₀ D hklt hN hj t (fun α hα => ?_) hne
    obtain ⟨k, rfl⟩ := hf α
    have hyR : y ∈ R (f k) := (hrep (f k) y hyc).mp hα
    have hwR : w ∈ R (f k) := by
      by_contra h
      exact hyZ k (by simpa only [h, ↓reduceIte] using hyR)
    exact (hrep (f k) x hxc).mpr (hwx.mem_closed (hR _) hwR)

section AllDegrees

variable [IsAlgClosed K] [Uncountable K]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- One boundary-free closed point transfers every rational profile in all large degrees to a
specified closed point. The closed representatives suffice, independently of real t. -/
theorem exists_boundaryFree_closedPoint_all_degree_transfer_of_closedPoints
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ A : CartierDivisor Y)
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ (j • A)
          (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y) (hxc : IsClosed ({x} : Set Y)) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ∈ cY.U ∧ D₀.IsLocalEquationAt y (fY ^ d) ∧
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
          (Module.finrank K Γ((j • A).sheaf, ⊤)) y →
        (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
          (Module.finrank K Γ((j • A).sheaf, ⊤)) x := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcl
  let I := {a : (Σ j : ℕ, Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ) // J ≤ a.1}
  choose Z hZ hrep using fun a : I => hJ a.1.1 a.2 a.1.2
  obtain ⟨V, hV, hVne, -, hVD⟩ := exists_dense_open_localEquation D₀ (fY ^ d) cY.U cY.nonempty
  obtain ⟨y, hycl, hyV, hybad⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K)
    (V : Set Y) V.isOpen (by obtain ⟨y⟩ := hVne; exact ⟨y.1, y.2⟩)
    (fun a : {a : I // Z a ≠ Set.univ} => Z a.1) (fun a => hZ a.1) (fun a => a.2)
  refine ⟨y, hycl, hV hyV, hVD y hyV, ?_⟩
  filter_upwards [eventually_ge_atTop J] with j hj
  intro α hα
  let a : I := ⟨⟨j, α⟩, hj⟩
  have hyZ : y ∈ Z a := (hrep a y hycl).mp hα
  have hEq : Z a = Set.univ := by
    by_contra h
    exact hybad ⟨a, h⟩ hyZ
  exact (hrep a x hxc).mpr (hEq ▸ Set.mem_univ x)

end AllDegrees

/-- Closedness on closed points is preserved by principal shifts, including the finrank change
in the indexing type of rational profiles. -/
theorem normalizedProfiles_closedPoints_principalShift (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (h : ∀ α : Fin (Module.finrank K Γ(D.sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ D (Module.finrank K Γ(D.sheaf, ⊤)) y}) :
    ∀ α : Fin (Module.finrank K Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (D + principalCartierDivisor Y g)
        (Module.finrank K Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) y} := by
  have key : ∀ N₁ N₂ : ℕ, N₁ = N₂ →
      (∀ α : Fin N₂ → ℚ, IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ D N₂ y}) →
      ∀ α : Fin N₁ → ℚ, IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ (D + principalCartierDivisor Y g) N₁ y} := by
    rintro N₁ N₂ rfl hN α
    have hset : {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (D + principalCartierDivisor Y g) N₁ y} =
        {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N₁ y} := by
      ext y
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sncWeightNormalizedProfiles_principalShift]
    rw [hset]
    exact hN α
  exact key _ _ (finrank_add_principal (K := K) D g) h

/-- The corrected closed-point hypothesis passes from (j*l)A to jJ. -/
theorem normalizedProfiles_closedPoints_of_nsmul_eq (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) {A J : CartierDivisor Y} {l : ℕ}
    {φ : Y.functionFieldˣ} (hlA : l • A = J + principalCartierDivisor Y φ) (j : ℕ)
    (h : ∀ α : Fin (Module.finrank K Γ(((j * l) • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        ((j * l) • A) (Module.finrank K Γ(((j * l) • A).sheaf, ⊤)) y}) :
    ∀ α : Fin (Module.finrank K Γ((j • J).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (j • J) (Module.finrank K Γ((j • J).sheaf, ⊤)) y} := by
  rw [nsmul_eq_nsmul_mul_add_principal hlA j]
  exact normalizedProfiles_closedPoints_principalShift cY fY d D₀ _ _ h

end MixedFujita
