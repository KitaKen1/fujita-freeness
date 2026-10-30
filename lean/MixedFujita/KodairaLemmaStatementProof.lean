/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessAmple
public import MixedFujita.GenericSmoothCharts

/-!
`KodairaLemmaStatement` is a theorem (step 17).

An integral scheme locally of finite type over a field of characteristic zero of dimension n has
an étale chart with n coordinates (`nonempty_etaleChart_of_charZero`): the generic point lies in
the smooth locus (Mathlib's `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`), a point of
the smooth locus lies in an étale chart (`exists_etaleChart_of_mem_smoothLocus`), and a chart of
an irreducible scheme has as many coordinates as its dimension (`etaleChart_topologicalKrullDim`).
With Kodaira's lemma for normal projective varieties with an étale chart
(`exists_section_nsmul_sub_of_isBig_of_isAmpleProj`), the statement `KodairaLemmaStatement`
assumed earlier for F2 holds (`kodairaLemmaStatement_holds`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

/-- An integral scheme locally of finite type over a field of characteristic zero, of dimension n,
has an étale chart with n coordinates. -/
theorem nonempty_etaleChart_of_charZero {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (hdim : topologicalKrullDim X = n) : Nonempty (EtaleChart K X n) := by
  have hgen := (X ↘ Spec (CommRingCat.of K)).genericPoint_mem_smoothLocus_of_perfectField
  obtain ⟨m, c, -⟩ := exists_etaleChart_of_mem_smoothLocus hgen
  have hm : ((m : ℕ) : WithBot ℕ∞) = n := (etaleChart_topologicalKrullDim c).symm.trans hdim
  have hmn : m = n := by exact_mod_cast hm
  subst hmn
  exact ⟨c⟩

/-- Kodaira's lemma as assumed earlier for F2: on a normal projective variety, for a big T and an
ample H some m T − H with m ≥ 1 has a nonzero section. -/
theorem kodairaLemmaStatement_holds : KodairaLemmaStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm _ T H hT hH
  obtain ⟨c₀⟩ := nonempty_etaleChart_of_charZero (K := K) hdim
  exact exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdim hn hnorm c₀ T H hT hH

end MixedFujita
