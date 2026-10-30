/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierAmpleDefinition
public import MixedFujita.CartierSectionSNC

/-!
On a quasi-compact integral scheme, a base-point-free family of actual Cartier sections has
a finite base-point-free subfamily. Consequently ordinary global generation supplies a
finite linear system for the existing Bertini theorems. The proof uses the open cover of
nonvanishing loci; it requires neither projectivity nor finite-dimensionality of H⁰.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Any base-point-free family proves ordinary global generation. -/
theorem cartierSectionsBasePointFree_globallyGenerated (D : CartierDivisor X)
    {ι : Type*} (s : ι → Γ(D.sheaf, ⊤)) (hs : CartierSectionsBasePointFree D s) :
    CartierIsGloballyGenerated D := by
  intro x
  obtain ⟨i, hi⟩ := hs x
  exact ⟨s i, hi⟩

/-- Quasi-compactness selects finitely many of the supplied sections, still without base points. -/
theorem cartierSectionsBasePointFree_exists_finite_subfamily [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) :
    ∃ t : Finset ι, CartierSectionsBasePointFree D (fun i : t => s i) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (cartierSectionNonvanishingOpen D (s i) : Set X))
    (fun i => (cartierSectionNonvanishingOpen D (s i)).isOpen) (by
      intro x _
      obtain ⟨i, hi⟩ := hs x
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D (s i) x _ _).mpr hi)
  refine ⟨t, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, hix⟩ := Set.mem_iUnion.mp hi
  exact ⟨⟨i, hit⟩,
    (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D (s i) x _ _).mp hix⟩

/-- Ordinary global generation supplies a finite indexed system by compactness alone. -/
theorem cartierIsGloballyGenerated_exists_fin_basePointFree [CompactSpace X]
    (D : CartierDivisor X) (hD : CartierIsGloballyGenerated D) :
    ∃ (r : ℕ) (s : Fin r → Γ(D.sheaf, ⊤)), CartierSectionsBasePointFree D s := by
  classical
  obtain ⟨t, ht⟩ := cartierSectionsBasePointFree_exists_finite_subfamily D
    (id : Γ(D.sheaf, ⊤) → Γ(D.sheaf, ⊤)) hD
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i => (e.symm i).val, fun x => ?_⟩
  obtain ⟨i, hi⟩ := ht x
  exact ⟨e i, by simpa using hi⟩

/-- On a quasi-compact scheme, the usual predicate is equivalent to a finite system. -/
theorem cartierIsGloballyGenerated_iff_fin_basePointFree [CompactSpace X]
    (D : CartierDivisor X) : CartierIsGloballyGenerated D ↔
    ∃ (r : ℕ) (s : Fin r → Γ(D.sheaf, ⊤)), CartierSectionsBasePointFree D s := by
  constructor
  · exact cartierIsGloballyGenerated_exists_fin_basePointFree D
  · rintro ⟨r, s, hs⟩
    exact cartierSectionsBasePointFree_globallyGenerated D s hs

end MixedFujita
