/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieRestriction
public import MixedFujita.CechCartierCondition

/-!
Restriction of differential forms between open subsets (step 10).

For open subsets `V ≤ U` of `X`, the restriction `Γ(X, U) → Γ(X, V)` (check 420) makes `Γ(X, V)` an
algebra over `Γ(X, U)` (`openRestrictAlgebra`), with scalar towers over `K` and below the function
field. Kähler differentials are functorial along `Γ(X, U) → Γ(X, V) → K(X)`
(`kaehlerDifferential_map_map`), so the map of `b`-forms to the rational `b`-forms commutes with
restriction (`sectionFormsMap_restrict`), and the chart identification of the sections of `Ω^b_X`
(check 415) commutes with restricting both a section and the chart
(`chartFormsEquiv_regularFormsRestrict`). This is the comparison of the Deligne–Illusie maps of
check 459 with the restriction maps of the Čech complexes.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

universe u

section KaehlerTower

variable {K : Type*} [Field K] {A' A B : Type*} [CommRing A'] [CommRing A] [CommRing B]
  [Algebra K A'] [Algebra K A] [Algebra K B] [Algebra A' A] [Algebra A B] [Algebra A' B]
  [IsScalarTower K A' A] [IsScalarTower K A B] [IsScalarTower K A' B] [IsScalarTower A' A B]

/-- **Kähler differentials are functorial**: `Ω[A'] → Ω[A] → Ω[B]` is `Ω[A'] → Ω[B]`. -/
theorem kaehlerDifferential_map_map (ω : Ω[A'⁄K]) :
    KaehlerDifferential.map K K A B (KaehlerDifferential.map K K A' A ω) =
      KaehlerDifferential.map K K A' B ω := by
  have hω : ω ∈ Submodule.span A' (Set.range (KaehlerDifferential.D K A')) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_apply]
  | zero => simp only [map_zero]
  | add x z _ _ hx hz => rw [map_add, map_add, map_add, hx, hz]
  | smul c x _ hx =>
    rw [LinearMap.map_smul (KaehlerDifferential.map K K A' A) c x,
      ← algebraMap_smul A c (KaehlerDifferential.map K K A' A x),
      LinearMap.map_smul (KaehlerDifferential.map K K A B), hx,
      LinearMap.map_smul (KaehlerDifferential.map K K A' B) c x, algebraMap_smul]

end KaehlerTower

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Opens

variable (K) in
/-- **The restriction to a smaller open subset as an algebra structure.** -/
@[instance_reducible]
noncomputable def openRestrictAlgebra {U V : X.Opens} (e : V ≤ U) : Algebra Γ(X, U) Γ(X, V) :=
  (sectionRestrict K e).toRingHom.toAlgebra

omit [IsIntegral X] in
theorem openRestrict_algebraMap {U V : X.Opens} (e : V ≤ U) (f : Γ(X, U)) :
    letI := openRestrictAlgebra K e
    algebraMap Γ(X, U) Γ(X, V) f = (X.presheaf.map (homOfLE e).op).hom f := rfl

omit [IsIntegral X] in
theorem openRestrict_isScalarTower {U V : X.Opens} (e : V ≤ U) :
    letI := openRestrictAlgebra K e
    IsScalarTower K Γ(X, U) Γ(X, V) :=
  let _ := openRestrictAlgebra K e
  IsScalarTower.of_algebraMap_eq fun k => ((sectionRestrict K e).commutes k).symm

theorem openRestrict_functionField_isScalarTower {U V : X.Opens} (e : V ≤ U) [Nonempty U]
    [Nonempty V] :
    letI := openRestrictAlgebra K e
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField :=
  let _ := openRestrictAlgebra K e
  IsScalarTower.of_algebraMap_eq fun f => by
    change (X.germToFunctionField U).hom f =
      (X.germToFunctionField V).hom ((X.presheaf.map (homOfLE e).op).hom f)
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

theorem restrict_mem_regularFormsSections (b : ℕ) {U V : X.Opens} (e : V ≤ U)
    {s : Γ(rationalFormsSheaf K X b, U)} (hs : s ∈ regularFormsSections K b U) :
    (rationalFormsSheaf K X b).presheaf.map (homOfLE e).op s ∈ regularFormsSections K b V := by
  rw [mem_regularFormsSections]
  intro x hx
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : Nonempty U := ⟨⟨x, e hx⟩⟩
  rw [rationalFormsSectionsEquiv_map K b (homOfLE e) s]
  exact hs x (e hx)

/-- The restriction of regular `b`-forms to a smaller open subset. -/
noncomputable def regularFormsRestrict (b : ℕ) {U V : X.Opens} (e : V ≤ U) :
    regularFormsSections K b U →+ regularFormsSections K b V where
  toFun s := ⟨(rationalFormsSheaf K X b).presheaf.map (homOfLE e).op s.1,
    restrict_mem_regularFormsSections b e s.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ s.1 t.1)

theorem regularFormsValue_regularFormsRestrict (b : ℕ) {U V : X.Opens} (e : V ≤ U) [Nonempty U]
    [Nonempty V] (s : regularFormsSections K b U) :
    regularFormsValue K b V (regularFormsRestrict b e s) = regularFormsValue K b U s :=
  rationalFormsSectionsEquiv_map K b (homOfLE e) s.1

/-- **The map to rational forms commutes with restriction.** -/
theorem sectionFormsMap_restrict {U V : X.Opens} (e : V ≤ U) [Nonempty U] [Nonempty V] (b : ℕ)
    (x : ⋀[Γ(X, U)]^b Ω[Γ(X, U)⁄K]) :
    letI := openRestrictAlgebra K e
    haveI := openRestrict_isScalarTower (K := K) e
    sectionFormsMap (K := K) V b (kaehlerExteriorPowerMap b x) = sectionFormsMap (K := K) U b x := by
  let _ := openRestrictAlgebra K e
  have := openRestrict_isScalarTower (K := K) e
  have := openRestrict_functionField_isScalarTower (K := K) e
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [kaehlerExteriorPowerMap_ιMulti]
    simp only [sectionFormsMap, OAI.ReverseLogKodaira.DifferentialBaseChange.exteriorDifferentialMap,
      OAI.ReverseLogKodaira.DifferentialBaseChange.exteriorScalarMap_wedge]
    congr 1
    funext i
    exact kaehlerDifferential_map_map (ω i)
  | zero => rw [kaehlerExteriorPowerMap_zero, map_zero, map_zero]
  | add x z _ _ hx hz => rw [kaehlerExteriorPowerMap_add, map_add, map_add, hx, hz]
  | smul f x _ hx =>
    rw [kaehlerExteriorPowerMap_smul, LinearMap.map_smul, LinearMap.map_smul, hx,
      algebraMap_smul]

/-- **The chart identification commutes with restriction**: for a chart `c'` on `V ≤ c.U`, the
form of the restriction of a section is the restriction of its form. -/
theorem chartFormsEquiv_regularFormsRestrict {n : ℕ} (c c' : EtaleChart K X n) (e : c'.U ≤ c.U)
    (b : ℕ) (s : regularFormsSections K b c.U) :
    letI := openRestrictAlgebra K e
    haveI := openRestrict_isScalarTower (K := K) e
    chartFormsEquiv c' b (regularFormsRestrict b e s) =
      kaehlerExteriorPowerMap b (chartFormsEquiv c b s) := by
  let _ := openRestrictAlgebra K e
  have := openRestrict_isScalarTower (K := K) e
  have := c.nonempty
  have := c'.nonempty
  apply sectionFormsMap_injective c' b
  rw [sectionFormsMap_chartFormsEquiv, sectionFormsMap_restrict e b, sectionFormsMap_chartFormsEquiv,
    regularFormsValue_regularFormsRestrict]

end Opens

end MixedFujita
