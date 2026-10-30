/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpProjectiveEmbedding
public import MixedFujita.VeryAmpleNumericalBound

/-! The same integral blow-up sequence base model carries an actual ample divisor
from the original base's projectivity. The divisor is auxiliary and is constructed
independently of the specified original Cartier presentation. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Lift an actual projective embedding through the existing sequence and construct
an auxiliary ample Cartier divisor on that same model. -/
theorem blowUpSequence_exists_ample_cartier
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))]
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (S : Scheme.BlowUpSequence Y) [IsIntegral S.last]
    [S.last.Over (Spec (CommRingCat.of K))]
    [S.composite.IsOver (Spec (CommRingCat.of K))] :
    ∃ A : CartierDivisor S.last, CartierIsAmpleProj K A := by
  obtain ⟨A, hA⟩ := hProj
  obtain ⟨_, _, N, e, he, hover, _, _, _, _, _⟩ := hA
  obtain ⟨M, eB, heB, hBover⟩ := blowUpSequence_exists_closedImmersion e hover S
  have hbase : eB ≫ polynomialProjectiveToBase M K = S.last ↘ Spec (CommRingCat.of K) :=
    hBover.trans (HomIsOver.comp_over (f := S.composite) (S := Spec (CommRingCat.of K)))
  obtain ⟨J, hJ⟩ := exists_cartierIsVeryAmpleProj_of_closedImmersion eB hbase
  exact ⟨J, cartierIsAmpleProj_of_veryAmple hJ⟩

end MixedFujita
