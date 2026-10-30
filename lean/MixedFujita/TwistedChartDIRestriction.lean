/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedChartDIComponent

/-!
The twisted Deligne–Illusie components commute with restriction (step 10).

Let `c'` be an étale chart on an open subset `V ≤ c.U` of an étale chart `c`, with lifts modulo
`p²` related by a map `ρ` compatible with the restriction and with families of Frobenius lifts
`ρ ∘ F_j = F'_{e j} ∘ ρ`, and equations `g`, `g'` of `D` on `c.U` and on `V`. Then
* the ratio `g'/g` is a regular function on `V` (`exists_ratio_of_isLocalEquationAt`);
* the components of the Deligne–Illusie map are Frobenius-semilinear (`diSeqAltComponent_smul`)
  and commute with restriction along `e` (`diSeqAltComponent_restrict`, from checks 458 and 459);
* the form of the restriction of a section is `g'/g` times the restriction of its form
  (`twistedChartForm_restrict`);
* hence the twisted components commute with restriction:
  `Θ^{c', F', g'}_{e ∘ s}(ω|_V) = Θ^{c, F, g}_s(ω)|_V` (`twistedChartDIComponent_restrict`).
On a Čech face the chart, the family of lifts and the equation of `D` change; this lemma compares
the components on a simplex and on its faces.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u w w'

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The restriction of a section of `Ω^b(D)` has the same rational form. -/
theorem rationalFormsSectionsEquiv_twistedFormsSheaf_map (D : CartierDivisor X) (b : ℕ)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (e : V ≤ U) (s : Γ(twistedFormsSheaf K D b, U)) :
    rationalFormsSectionsEquiv K b V ((twistedFormsSheaf K D b).presheaf.map (homOfLE e).op s).1 =
      rationalFormsSectionsEquiv K b U s.1 := by
  change rationalFormsSectionsEquiv K b V ((rationalFormsSheaf K X b).presheaf.map (homOfLE e).op s.1) =
    _
  exact rationalFormsSectionsEquiv_map K b (homOfLE e) s.1

/-- **The ratio of two equations of `D` on `V` is a regular function on `V`.** -/
theorem exists_ratio_of_isLocalEquationAt {D : CartierDivisor X} {V : X.Opens} [Nonempty V]
    {g g' : X.functionFieldˣ} (hg : ∀ x ∈ V, D.IsLocalEquationAt x g)
    (hg' : ∀ x ∈ V, D.IsLocalEquationAt x g') :
    ∃ r : Γ(X, V), X.germToFunctionField V r = (g' : X.functionField) * (g : X.functionField)⁻¹ := by
  apply exists_germToFunctionField_eq_of_forall_mem_range
  intro y hy
  obtain ⟨r, hr⟩ := (hg' y hy).exists_unit_mul_eq (hg y hy)
  refine ⟨r, ?_⟩
  rw [← hr, mul_assoc, mul_inv_cancel₀ g.ne_zero, mul_one]

section Chart

variable (c : EtaleChart K X n) {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U))
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] [CharP K p] {J : Type*}
  (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

omit [IsIntegral X] in
/-- **The components are Frobenius-semilinear.** -/
theorem diSeqAltComponent_smul (b i a : ℕ) (h : i + a = b) (s : ℕ → J) (r : Γ(X, c.U))
    (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    diSeqAltComponent c π hπ p F hF hker b i a h s (r • z) =
      r ^ p • diSeqAltComponent c π hπ p F hF hker b i a h s z := by
  apply Subtype.ext
  rw [diSeqAltComponent_coe, map_smul, twistedPiHom_smul, Submodule.coe_smul,
    diSeqAltComponent_coe]

end Chart

section Restrict

variable (c c' : EtaleChart K X n) (hle : c'.U ≤ c.U)
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U)) (hπ : Function.Surjective π)
  {L' : Type w'} [CommRing L'] (π' : L' →+* Γ(X, c'.U)) (hπ' : Function.Surjective π')
  (p : ℕ) [Fact p.Prime] [CharP K p] {J J' : Type*}
  (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (F' : J' → (L' →+* L')) (hF' : ∀ j x, π' (F' j x) = π' x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hann' : ∀ z, (p : L') * z = 0 → π' z = 0) (hp2' : (p : L') * p = 0)
  (hK : ∀ k : K, ∃ k' : L, π k' = algebraMap K Γ(X, c.U) k ∧ ∀ j, F j k' = k' ^ p)
  (hK' : ∀ k : K, ∃ k' : L', π' k' = algebraMap K Γ(X, c'.U) k ∧ ∀ j, F' j k' = k' ^ p)
  (ρ : L →+* L') (hρ : ∀ x, π' (ρ x) = (X.presheaf.map (homOfLE hle).op).hom (π x))
  (e : J → J') (hρF : ∀ j x, ρ (F j x) = F' (e j) (ρ x))

omit [IsIntegral X] in
include hann hp2 hann' hp2' hK hK' hρ hρF in
/-- **The components commute with restriction along `e`.** -/
theorem diSeqAltComponent_restrict [Algebra.FiniteType K Γ(X, c.U)]
    [Algebra.FiniteType K Γ(X, c'.U)] (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    letI := openRestrictAlgebra K hle
    haveI := openRestrict_isScalarTower (K := K) hle
    kaehlerExteriorPowerMap i (diSeqAltComponent c π hπ p F hF hker b i a h s z) =
      diSeqAltComponent c' π' hπ' p F' hF' hker' b i a h (e ∘ s) (kaehlerExteriorPowerMap b z) := by
  let _ := openRestrictAlgebra K hle
  have := openRestrict_isScalarTower (K := K) hle
  apply Subtype.ext
  have hmap := congrFun (congrFun (diSeqAlt_map c.coords c.formallyEtale c'.coords c'.formallyEtale
    π hπ p hker hann hp2 π' hπ' hker' hann' hp2' ρ hρ F hF (fun j => F' (e j))
    (fun j => hF' (e j)) hρF hK (fun k => (hK' k).imp fun k' hk => ⟨hk.1, fun j => hk.2 (e j)⟩)
    b z) a) s
  rw [diSeqAlt_reindex c'.coords c'.formallyEtale π' hπ' p F' hF' hker' e b] at hmap
  exact hmap

variable {D : CartierDivisor X} {g g' : X.functionFieldˣ}

/-- **The form of the restriction of a section is `g'/g` times the restriction of its form.** -/
theorem twistedChartForm_restrict (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (hg' : ∀ x ∈ c'.U, D.IsLocalEquationAt x g') (r : Γ(X, c'.U))
    (hr : haveI := c'.nonempty
      X.germToFunctionField c'.U r = (g' : X.functionField) * (g : X.functionField)⁻¹) (b : ℕ)
    (ω : twistedFormsSections K D b c.U) :
    letI := openRestrictAlgebra K hle
    haveI := openRestrict_isScalarTower (K := K) hle
    twistedChartForm c' hg' ((twistedFormsSheaf K D b).presheaf.map (homOfLE hle).op ω) =
      r • kaehlerExteriorPowerMap b (twistedChartForm c hg ω) := by
  let _ := openRestrictAlgebra K hle
  have := openRestrict_isScalarTower (K := K) hle
  have := c.nonempty
  have := c'.nonempty
  apply sectionFormsMap_injective c' b
  rw [twistedChartForm, sectionFormsMap_chartFormsEquiv, regularFormsValue_apply, twistToRegularForms_val,
    rationalFormsSectionsEquiv_twistedFormsSheaf_map, LinearMap.map_smul, sectionFormsMap_restrict,
    twistedChartForm, sectionFormsMap_chartFormsEquiv, regularFormsValue_apply, twistToRegularForms_val,
    ← algebraMap_smul X.functionField r, smul_smul]
  congr 1
  change (g' : X.functionField) = X.germToFunctionField c'.U r * g
  rw [hr, mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]

include hann hp2 hann' hp2' hK hK' hρ hρF in
/-- **The twisted components commute with restriction**:
`Θ^{c', F', g'}_{e ∘ s}(ω|_V) = Θ^{c, F, g}_s(ω)|_V`. -/
theorem twistedChartDIComponent_restrict [Algebra.FiniteType K Γ(X, c.U)]
    [Algebra.FiniteType K Γ(X, c'.U)] (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (hg' : ∀ x ∈ c'.U, D.IsLocalEquationAt x g') (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (ω : twistedFormsSections K D b c.U) :
    (twistedFormsSheaf K (p • D) i).presheaf.map (homOfLE hle).op
        (twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω) =
      twistedChartDIComponent c' π' hπ' p F' hF' hker' hg' b i a h (e ∘ s)
        ((twistedFormsSheaf K D b).presheaf.map (homOfLE hle).op ω) := by
  let _ := openRestrictAlgebra K hle
  have := openRestrict_isScalarTower (K := K) hle
  have := c.nonempty
  have := c'.nonempty
  obtain ⟨r, hr⟩ := exists_ratio_of_isLocalEquationAt (V := c'.U) (fun x hx => hg x (hle hx)) hg'
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K i c'.U).injective
  rw [rationalFormsSectionsEquiv_twistedFormsSheaf_map, twistedChartDIComponent_eq,
    twistedChartDIComponent_eq, twistBackForms_val, twistBackForms_val,
    twistedChartForm_restrict c c' hle hg hg' r hr b ω, diSeqAltComponent_smul,
    ← diSeqAltComponent_restrict c c' hle π hπ π' hπ' p F hF F' hF' hker hker' hann hp2 hann' hp2'
      hK hK' ρ hρ e hρF b i a h s, LinearMap.map_smul, sectionFormsMap_restrict,
    ← algebraMap_smul X.functionField (r ^ p), smul_smul, map_pow]
  congr 1
  change ((g : X.functionField)⁻¹) ^ p = ((g' : X.functionField)⁻¹) ^ p *
    (X.germToFunctionField c'.U r) ^ p
  rw [hr, ← mul_pow, ← mul_assoc, inv_mul_cancel₀ g'.ne_zero, one_mul]

end Restrict

end MixedFujita
