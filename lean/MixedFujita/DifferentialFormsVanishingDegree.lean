/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedFormsTensor

/-!
`Ω^b_X(D) = 0` above the dimension (step 10).

An étale chart in `n` coordinates gives a basis of the rational `b`-forms indexed by the
`b`-element subsets of the coordinates (check-415), which is empty for `b > n`
(`isEmpty_powersetCard_fin_of_lt`). So for `b > n` the rational `b`-forms vanish
(`rationalForms_subsingleton_of_lt`), every section of `Ω^b_X(D)` vanishes
(`twistedFormsSheaf_sections_subsingleton_of_lt`), `Ω^b_X(D)` is a zero object
(`twistedFormsSheaf_isZero_of_lt`) and its cohomology vanishes
(`twistedFormsSheaf_cohomology_subsingleton_of_lt`): the Čech–de Rham double complex has its rows in
degrees `≤ n` only.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

theorem isEmpty_powersetCard_fin_of_lt {n b : ℕ} (h : n < b) :
    IsEmpty (Set.powersetCard (Fin n) b) := by
  constructor
  rintro ⟨s, hs⟩
  have hcard : s.card = b := hs
  have hle := s.card_le_univ
  rw [Fintype.card_fin] at hle
  omega

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- **There are no rational `b`-forms above the dimension.** -/
theorem rationalForms_subsingleton_of_lt (c : EtaleChart K X n) {b : ℕ} (hb : n < b) :
    Subsingleton (RationalForms K X b) := by
  have := isEmpty_powersetCard_fin_of_lt hb
  exact (chartFormsBasis c b).repr.toEquiv.subsingleton

theorem rationalFormsSheaf_sections_subsingleton_of_lt (c : EtaleChart K X n) {b : ℕ} (hb : n < b)
    (U : X.Opens) : Subsingleton Γ(rationalFormsSheaf K X b, U) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact rationalFormsSheaf_sections_subsingleton b hU
  · have := rationalForms_subsingleton_of_lt c hb
    exact (rationalFormsSectionsEquiv K b U).toEquiv.subsingleton

/-- **Every section of `Ω^b_X(D)` vanishes above the dimension.** -/
theorem twistedFormsSheaf_sections_subsingleton_of_lt (c : EtaleChart K X n) (D : CartierDivisor X)
    {b : ℕ} (hb : n < b) (U : X.Opens) : Subsingleton Γ(twistedFormsSheaf K D b, U) := by
  have := rationalFormsSheaf_sections_subsingleton_of_lt c hb U
  exact inferInstanceAs (Subsingleton ↥(twistedFormsSections K D b U))

/-- **`Ω^b_X(D)` is a zero object above the dimension.** -/
theorem twistedFormsSheaf_isZero_of_lt (c : EtaleChart K X n) (D : CartierDivisor X) {b : ℕ}
    (hb : n < b) : IsZero (twistedFormsSheaf K D b) := by
  rw [IsZero.iff_id_eq_zero]
  ext U s
  exact @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton_of_lt c D hb U) _ _

/-- **The cohomology of `Ω^b_X(D)` vanishes above the dimension.** -/
theorem twistedFormsSheaf_cohomology_subsingleton_of_lt (c : EtaleChart K X n)
    (D : CartierDivisor X) {b : ℕ} (hb : n < b) (q : ℕ) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K D b) q) := by
  have h := Functor.map_isZero (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X q)
    (twistedFormsSheaf_isZero_of_lt c D hb)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp h

end MixedFujita
