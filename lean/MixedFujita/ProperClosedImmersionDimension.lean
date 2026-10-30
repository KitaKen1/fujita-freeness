/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperCartierCohomology

/-! 真の閉部分源の普通のKrull次元の厳密降下。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A proper closed immersion into an irreducible finite-dimensional scheme
lowers the ordinary geometric dimension by at least one. Append the ambient
irreducible closed set to every actual chain from the source. -/
theorem properClosedImmersion_topologicalKrullDim_le_predecessor
    {Y Z : Scheme.{u}} [IrreducibleSpace Y] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hproper : Set.range i ≠ Set.univ) (n : ℕ)
    (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) :
    topologicalKrullDim Z ≤ n := by
  let m := IrreducibleCloseds.map (fun z : Z => i z) i.continuous
  have hm : StrictMono m :=
    IrreducibleCloseds.map_strictMono_of_isInducing i.isClosedEmbedding.isInducing
  let whole : IrreducibleCloseds Y :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hlt (T : IrreducibleCloseds Z) : m T < whole := by
    have hle : (m T : Set Y) ⊆ Set.range i := by
      change closure (i '' (T : Set Z)) ⊆ _
      rw [(i.isClosedMap _ T.isClosed).closure_eq]
      exact Set.image_subset_range _ _
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro heq
    apply hproper
    apply Set.eq_univ_of_forall
    intro y
    apply hle
    rw [heq]
    trivial
  change Order.krullDim (IrreducibleCloseds Z) ≤ (n : WithBot ℕ∞)
  rw [Order.krullDim, iSup_le_iff]
  intro t
  let q : LTSeries (IrreducibleCloseds Y) := t.map m hm
  let s : LTSeries (IrreducibleCloseds Y) :=
    q.snoc whole (by change m t.last < whole; exact hlt t.last)
  have hb : (s.length : WithBot ℕ∞) ≤ (n + 1 : ℕ) :=
    (Order.LTSeries.length_le_krullDim s).trans hdim
  have hb' : t.length + 1 ≤ n + 1 := by exact_mod_cast hb
  exact_mod_cast Nat.le_of_succ_le_succ hb'

end MixedFujita
