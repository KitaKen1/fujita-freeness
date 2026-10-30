/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedFormsTensor
public import SGA.Foundations.Cohomology.CechComparison
public import MixedFujita.JacobianCriterionCharts

/-!
The twisted de Rham complex on Čech cochains (step 10).

In characteristic `p`, the de Rham differential of `Ω^•_X(p • D)` (check-418) is defined on the
sections over nonempty open subsets. Extending it by zero over the empty open subset, where all
sections vanish, gives a morphism of presheaves of abelian groups
`Ω^b_X(p • D) ⟶ Ω^{b+1}_X(p • D)` (`twistedFormsDiffPresheaf`; it commutes with restriction because
it is computed on the rational values), with `d ∘ d = 0` (`twistedFormsDiffPresheaf_comp`).
Applied to the Čech complexes of SGA for a finite family of open subsets, it gives the de Rham
differential between the Čech complexes (`twistedFormsCechDiff`), again with `d ∘ d = 0`
(`twistedFormsCechDiff_comp`): the rows of the Čech–de Rham double complex.

The intersections in a Čech complex of étale charts are again charts: the restriction of sections
between affine open subsets is formally étale, since an open immersion is étale
(`restrict_formallyEtale_of_isAffineOpen`), so an étale chart restricts to every nonempty affine
open subset of it (`etaleChartRestrict`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

theorem twistedFormsSheaf_sections_subsingleton (D : CartierDivisor X) (b : ℕ) {U : X.Opens}
    (hU : IsEmpty U) : Subsingleton Γ(twistedFormsSheaf K D b, U) :=
  modules_sections_subsingleton_of_eq_bot _ (Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU))

open Classical in
/-- The de Rham differential of `Ω^•_X(p • D)` on every open subset (zero on the empty one). -/
noncomputable def twistedFormsDiffApp (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) :
    Γ(twistedFormsSheaf K (p • D) b, U) →+ Γ(twistedFormsSheaf K (p • D) (b + 1), U) :=
  if _h : Nonempty U then twistedFormsDiff p c₀ hcover D b U else 0

theorem rationalFormsSectionsEquiv_twistedFormsDiffApp (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (D : CartierDivisor X) (b : ℕ) (U : X.Opens) [h : Nonempty U]
    (s : Γ(twistedFormsSheaf K (p • D) b, U)) :
    rationalFormsSectionsEquiv K (b + 1) U (twistedFormsDiffApp p c₀ hcover D b U s).1 =
      rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s.1) := by
  unfold twistedFormsDiffApp
  split
  · exact rationalFormsSectionsEquiv_twistedFormsDiff p c₀ hcover D b U s
  · exact absurd h ‹_›

/-- **The de Rham differential of `Ω^•_X(p • D)` as a morphism of presheaves of abelian groups.** -/
noncomputable def twistedFormsDiffPresheaf (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) :
    (twistedFormsSheaf K (p • D) b).presheaf ⟶ (twistedFormsSheaf K (p • D) (b + 1)).presheaf where
  app U := AddCommGrpCat.ofHom (twistedFormsDiffApp p c₀ hcover D b U.unop)
  naturality {U V} i := by
    ext s
    change twistedFormsDiffApp p c₀ hcover D b V.unop
        ((twistedFormsSheaf K (p • D) b).presheaf.map i s) =
      (twistedFormsSheaf K (p • D) (b + 1)).presheaf.map i
        (twistedFormsDiffApp p c₀ hcover D b U.unop s)
    rcases isEmpty_or_nonempty V.unop with hV | hV
    · exact @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton (p • D) (b + 1) hV) _ _
    · have : Nonempty U.unop := ⟨⟨hV.some.1, i.unop.le hV.some.2⟩⟩
      apply Subtype.ext
      apply (rationalFormsSectionsEquiv K (b + 1) V.unop).injective
      rw [rationalFormsSectionsEquiv_twistedFormsDiffApp]
      change rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b V.unop
          ((rationalFormsSheaf K X b).presheaf.map i.unop.op s.1)) =
        rationalFormsSectionsEquiv K (b + 1) V.unop
          ((rationalFormsSheaf K X (b + 1)).presheaf.map i.unop.op
            (twistedFormsDiffApp p c₀ hcover D b U.unop s).1)
      rw [rationalFormsSectionsEquiv_map K b i.unop, rationalFormsSectionsEquiv_map K (b + 1) i.unop,
        rationalFormsSectionsEquiv_twistedFormsDiffApp]

theorem twistedFormsDiffPresheaf_app_apply (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) (s : Γ(twistedFormsSheaf K (p • D) b, U)) :
    (twistedFormsDiffPresheaf p c₀ hcover D b).app (op U) s =
      twistedFormsDiffApp p c₀ hcover D b U s :=
  rfl

/-- `d ∘ d = 0` as morphisms of presheaves. -/
theorem twistedFormsDiffPresheaf_comp (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) :
    twistedFormsDiffPresheaf p c₀ hcover D b ≫ twistedFormsDiffPresheaf p c₀ hcover D (b + 1) =
      0 := by
  ext U s
  change twistedFormsDiffApp p c₀ hcover D (b + 1) U (twistedFormsDiffApp p c₀ hcover D b U s) = 0
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton (p • D) (b + 1 + 1) hU) _ _
  · apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (b + 2) U).injective
    rw [rationalFormsSectionsEquiv_twistedFormsDiffApp, rationalFormsSectionsEquiv_twistedFormsDiffApp,
      rationalFormsDiff_comp]
    exact ((rationalFormsSectionsEquiv K (b + 2) U).map_zero).symm

/-- **The de Rham differential between the Čech complexes** of `Ω^b_X(p • D)` and
`Ω^{b+1}_X(p • D)` for a finite family of open subsets. -/
noncomputable def twistedFormsCechDiff (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K (p • D) b).presheaf ⟶
      TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K (p • D) (b + 1)).presheaf :=
  TopCat.Presheaf.cechComplexMap 𝒰 (twistedFormsDiffPresheaf p c₀ hcover D b)

/-- `d ∘ d = 0` between the Čech complexes. -/
theorem twistedFormsCechDiff_comp (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    twistedFormsCechDiff p c₀ hcover D b 𝒰 ≫ twistedFormsCechDiff p c₀ hcover D (b + 1) 𝒰 = 0 := by
  rw [twistedFormsCechDiff, twistedFormsCechDiff, TopCat.Presheaf.cechComplexMap,
    TopCat.Presheaf.cechComplexMap, ← Functor.map_comp, twistedFormsDiffPresheaf_comp]
  exact Scheme.Modules.cechComplexMap_zero 𝒰

section Restriction

omit [IsIntegral X] in
/-- **The restriction of sections between affine open subsets is formally étale** (an open
immersion is étale). -/
theorem restrict_formallyEtale_of_isAffineOpen {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : V ≤ U) : (X.presheaf.map (homOfLE e).op).hom.FormallyEtale := by
  have h := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at h
  exact @Algebra.Etale.formallyEtale _ _ _ _ _ h

omit [IsIntegral X] in
variable (K) in
/-- The restriction of sections to a smaller open subset, as a `K`-algebra map. -/
noncomputable def sectionRestrict {U V : X.Opens} (e : V ≤ U) : Γ(X, U) →ₐ[K] Γ(X, V) where
  toRingHom := (X.presheaf.map (homOfLE e).op).hom
  commutes' k := by
    change (X.presheaf.map (homOfLE e : V ⟶ U).op).hom
        (((X.baseRingToStructurePresheaf K).app (op U)).hom k) =
      ((X.baseRingToStructurePresheaf K).app (op V)).hom k
    rw [← CommRingCat.comp_apply, ← (X.baseRingToStructurePresheaf K).naturality]
    rfl

/-- **An étale chart restricts to every nonempty affine open subset of it**: the coordinates stay
formally étale. -/
noncomputable def etaleChartRestrict (c : EtaleChart K X n) (V : X.Opens) (hV : IsAffineOpen V)
    (hne : Nonempty V) (e : V ≤ c.U) : EtaleChart K X n where
  U := V
  isAffine := hV
  nonempty := hne
  coords := (sectionRestrict K e).comp c.coords
  formallyEtale := formallyEtale_comp _ (restrict_formallyEtale_of_isAffineOpen c.isAffine hV e) _
    c.formallyEtale

omit [IsIntegral X] in
theorem etaleChartRestrict_U (c : EtaleChart K X n) (V : X.Opens) (hV : IsAffineOpen V)
    (hne : Nonempty V) (e : V ≤ c.U) : (etaleChartRestrict c V hV hne e).U = V :=
  rfl

end Restriction

end MixedFujita
