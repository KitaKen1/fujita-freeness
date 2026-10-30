/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothSchemeComponents
public import Mathlib.Data.Fin.Tuple.Basic

/-!
Replace a set in SNC position by its finite, pairwise disjoint component closures. Around a
point, shrink away from every component not containing the point. At most one new component
remains, and it uses the already supplied new coordinate. This avoids a global irreducibility
requirement and retains the point-indexed SNC interface used in the discrepancy calculation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- SNC position of an extra set survives restriction to a basic open. -/
theorem isSNCChartWith_basicOpen {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} {Z : Set X} {τ : Option (Fin n)}
    (h : IsSNCChartWith c ξ σ Z τ) (g : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen g)) :
    IsSNCChartWith (etaleChartBasicOpen c g hne) ξ σ Z τ := by
  refine ⟨isSNCChart_basicOpen h.1 g hne, h.2.1, ?_⟩
  have hle : (X.basicOpen g : Set X) ⊆ c.U := X.basicOpen_le g
  have heq : Z ∩ X.basicOpen g = (Z ∩ c.U) ∩ X.basicOpen g := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle]
  change Z ∩ X.basicOpen g = τ.elim ∅ (fun a => X.zeroLocus
    ({sectionBasicOpenRestrict (K := K) g (c.coords (MvPolynomial.X a))} :
      Set Γ(X, X.basicOpen g)) ∩ X.basicOpen g)
  rw [heq, h.2.2]
  cases τ with
  | none => simp
  | some a =>
    simp only [Option.elim_some]
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle,
      Scheme.zeroLocus_singleton, Scheme.zeroLocus_singleton]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hz, hg⟩
      exact ⟨fun hh => hz ((mem_basicOpen_sectionBasicOpenRestrict g _ hg).mp hh), hg⟩
    · rintro ⟨hz, hg⟩
      exact ⟨fun hh => hz ((mem_basicOpen_sectionBasicOpenRestrict g _ hg).mpr hh), hg⟩

/-- Two SNC chart families concatenate when they use distinct coordinates. -/
theorem isSNCChart_append {c : EtaleChart K X n} {r q : ℕ}
    {ξ : Fin r → X} {η : Fin q → X}
    {σ : Fin r → Option (Fin n)} {ρ : Fin q → Option (Fin n)}
    (hξ : IsSNCChart c ξ σ) (hη : IsSNCChart c η ρ)
    (hcross : ∀ i j a, σ i = some a → ρ j ≠ some a) :
    IsSNCChart c (Fin.append ξ η) (Fin.append σ ρ) := by
  refine ⟨?_, ?_⟩
  · intro i j a hi hj
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.append_left] at hi hj
      exact congrArg (Fin.castAdd q) (hξ.1 _ _ a hi hj)
    · simp only [Fin.append_left, Fin.append_right] at hi hj
      exact False.elim (hcross _ _ a hi hj)
    · simp only [Fin.append_left, Fin.append_right] at hi hj
      exact False.elim (hcross _ _ a hj hi)
    · simp only [Fin.append_right] at hi hj
      exact congrArg (Fin.natAdd r) (hη.1 _ _ a hi hj)
  · intro i
    induction i using Fin.addCases
    · simpa only [Fin.append_left] using hξ.2 _
    · simpa only [Fin.append_right] using hη.2 _

/-- A finite disjoint component decomposition converts set-valued SNC to a point-indexed family. -/
theorem isSNCFamily_append_of_disjoint_components {r q : ℕ} {ξ : Fin r → X}
    (η : Fin q → X) {Z : Set X} (hZ : IsSNCFamilyWith K n ξ Z)
    (hcover : Z = ⋃ j, closure ({η j} : Set X))
    (hdis : Pairwise fun i j => Disjoint (closure ({η i} : Set X))
      (closure ({η j} : Set X))) : IsSNCFamily K n (Fin.append ξ η) := by
  classical
  intro x
  obtain ⟨c, σ, τ, hx, hc⟩ := hZ x
  let C : Set X := ⋃ j : Fin q, if x ∈ closure ({η j} : Set X) then ∅
    else closure ({η j} : Set X)
  have hCc : IsClosed C := isClosed_iUnion_of_finite fun j => by
    split_ifs
    · exact isClosed_empty
    · exact isClosed_closure
  have hxC : x ∉ C := by
    intro hh
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
    by_cases hxj : x ∈ closure ({η j} : Set X)
    · simpa only [ite_eq_left hxj, Set.mem_empty_iff_false] using hj
    · exact hxj (by simpa only [ite_eq_right hxj] using hj)
  obtain ⟨g, hle, hxg⟩ := c.isAffine.exists_basicOpen_le (V := ⟨Cᶜ, hCc.isOpen_compl⟩)
    ⟨x, hxC⟩ hx
  let c' := etaleChartBasicOpen c g ⟨⟨x, hxg⟩⟩
  have hc' : IsSNCChartWith c' ξ σ Z τ := isSNCChartWith_basicOpen hc g _
  have hav : ∀ j : Fin q, x ∉ closure ({η j} : Set X) →
      closure ({η j} : Set X) ∩ c'.U = ∅ := by
    intro j hxj
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hzU⟩
    apply hle hzU
    exact Set.mem_iUnion.mpr ⟨j, by simpa only [ite_eq_right hxj] using hz⟩
  have heq : ∀ j : Fin q, x ∈ closure ({η j} : Set X) →
      closure ({η j} : Set X) ∩ c'.U = Z ∩ c'.U := by
    intro j hxj
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      refine ⟨?_, hzU⟩
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨j, hz⟩
    · rintro ⟨hz, hzU⟩
      rw [hcover] at hz
      obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hz
      by_cases hxk : x ∈ closure ({η k} : Set X)
      · have hkj : k = j := by
          by_contra hne
          exact Set.disjoint_left.mp (hdis hne) hxk hxj
        exact ⟨hkj ▸ hzk, hzU⟩
      · have hh : z ∈ (∅ : Set X) := hav k hxk ▸ ⟨hzk, hzU⟩
        exact False.elim hh
  let ρ : Fin q → Option (Fin n) := fun j =>
    if x ∈ closure ({η j} : Set X) then τ else none
  have hη : IsSNCChart c' η ρ := by
    refine ⟨?_, ?_⟩
    · intro i j a hi hj
      have hxi : x ∈ closure ({η i} : Set X) := by
        by_contra hh
        have hbad : (none : Option (Fin n)) = some a := by
          simpa only [ρ, ite_eq_right hh] using hi
        cases hbad
      have hxj : x ∈ closure ({η j} : Set X) := by
        by_contra hh
        have hbad : (none : Option (Fin n)) = some a := by
          simpa only [ρ, ite_eq_right hh] using hj
        cases hbad
      by_contra hne
      exact Set.disjoint_left.mp (hdis hne) hxi hxj
    · intro j
      by_cases hxj : x ∈ closure ({η j} : Set X)
      · simpa only [ρ, ite_eq_left hxj] using (heq j hxj).trans hc'.2.2
      · simpa only [ρ, ite_eq_right hxj, Option.elim_none] using hav j hxj
  refine ⟨c', Fin.append σ ρ, hxg, isSNCChart_append hc'.1 hη ?_⟩
  intro i j a hi
  by_cases hxj : x ∈ closure ({η j} : Set X)
  · simpa only [ρ, ite_eq_left hxj] using hc'.2.1 i a hi
  · intro hh
    have hbad : (none : Option (Fin n)) = some a := by
      simpa only [ρ, ite_eq_right hxj] using hh
    cases hbad

end MixedFujita
