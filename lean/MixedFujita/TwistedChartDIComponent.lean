/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.OpenRestrictionForms

/-!
The twisted Deligne–Illusie components on the sections over an étale chart (step 10).

On an étale chart `c` with a lift `L` modulo `p²`, a family of Frobenius lifts `F_j` and an
equation `g` of `D`, a section `ω` of `Ω^b(D)` gives the form `g ω` of the chart
(`twistedChartForm`). The Deligne–Illusie map on `b`-forms of check 455 sends it to a total index
cochain whose component of Čech degree `a` at a vertex sequence `s` is an `i`-form, `i + a = b`
(check 456). Dividing by `g^p` gives a section of `Ω^i(p • D)`: the **twisted Deligne–Illusie
component** `Θ^{b,a}_s(ω)` (`twistedChartDIComponent`). It is additive, its component of degree
`a = 0` is `b! · Φ_{D, F_{s 0}}` (check 437, `twistedChartDIComponent_zero`), and the cocycle
relation of check 456 becomes
`Σ_{k ≤ a+1} (-1)^k Θ^{b,a}_{s ∘ skip k}(ω) = (-1)^a d Θ^{b,a+1}_s(ω)`
(`twistedChartDIComponent_cocycle`); in degree `0` the values are closed
(`twistedFormsDiff_twistedChartDIComponent_zero`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u w

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

variable (c : EtaleChart K X n) {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U))
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] [CharP K p] {J : Type*}
  (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  {D : CartierDivisor X} {g : X.functionFieldˣ}

/-- The form `g ω` of the chart of a section `ω` of `Ω^b(D)`. -/
noncomputable def twistedChartForm (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (ω : twistedFormsSections K D b c.U) : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K] :=
  chartFormsEquiv c b (twistToRegularForms c hg ω)

theorem twistedChartForm_add (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (ω ω' : twistedFormsSections K D b c.U) :
    twistedChartForm c hg (ω + ω') = twistedChartForm c hg ω + twistedChartForm c hg ω' := by
  unfold twistedChartForm
  rw [twistToRegularForms_add, (chartFormsEquiv c b).map_add]

omit [IsIntegral X] in
/-- The component of Čech degree `a` of the Deligne–Illusie map on `b`-forms is an `i`-form. -/
theorem diSeqAlt_component_mem (b i a : ℕ) (h : i + a = b) (x : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K])
    (s : ℕ → J) :
    twistedPiHom K Γ(X, c.U) p J (diSeqAlt c.coords c.formallyEtale π hπ p F hF hker b x) a s ∈
      ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K] := by
  have hmem := (seqTotalHomogeneous_diSeqAlt c.coords c.formallyEtale π hπ p F hF hker b x a s).1
  rwa [show b - a = i by omega] at hmem

/-- The component of Čech degree `a` at the vertex sequence `s`, as an element of `⋀^i`. -/
noncomputable def diSeqAltComponent (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (x : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) : ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K] :=
  ⟨_, diSeqAlt_component_mem c π hπ p F hF hker b i a h x s⟩

omit [IsIntegral X] in
theorem diSeqAltComponent_coe (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (x : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    (diSeqAltComponent c π hπ p F hF hker b i a h s x : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) =
      twistedPiHom K Γ(X, c.U) p J (diSeqAlt c.coords c.formallyEtale π hπ p F hF hker b x) a s :=
  rfl

omit [IsIntegral X] in
theorem diSeqAltComponent_add (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (x x' : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    diSeqAltComponent c π hπ p F hF hker b i a h s (x + x') =
      diSeqAltComponent c π hπ p F hF hker b i a h s x +
        diSeqAltComponent c π hπ p F hF hker b i a h s x' := by
  apply Subtype.ext
  rw [Submodule.coe_add, diSeqAltComponent_coe, diSeqAltComponent_coe, diSeqAltComponent_coe,
    map_add, map_add]
  rfl

/-- **The twisted Deligne–Illusie component** `Θ^{b,a}_s(ω) = g^{-p} · (component of degree `a`
at `s` of the Deligne–Illusie map of `g ω`)`, a section of `Ω^i(p • D)` with `i + a = b`. -/
noncomputable def twistedChartDIComponent (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (b i a : ℕ) (h : i + a = b) (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    twistedFormsSections K (p • D) i c.U :=
  ⟨_, inv_pow_smul_mem_twisted c p hg ((chartFormsEquiv c i).symm
    (diSeqAltComponent c π hπ p F hF hker b i a h s (twistedChartForm c hg ω)))⟩

theorem twistedChartDIComponent_val (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b i a : ℕ)
    (h : i + a = b) (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    rationalFormsSectionsEquiv K i c.U (twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω).1 =
      ((g : X.functionField)⁻¹) ^ p • rationalFormsSectionsEquiv K i c.U
        ((chartFormsEquiv c i).symm
          (diSeqAltComponent c π hπ p F hF hker b i a h s (twistedChartForm c hg ω))).1 :=
  AddEquiv.apply_symm_apply _ _

theorem twistedChartDIComponent_add (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b i a : ℕ)
    (h : i + a = b) (s : ℕ → J) (ω ω' : twistedFormsSections K D b c.U) :
    twistedChartDIComponent c π hπ p F hF hker hg b i a h s (ω + ω') =
      twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω +
        twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω' := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K i c.U).injective
  rw [Submodule.coe_add, (rationalFormsSectionsEquiv K i c.U).map_add, twistedChartDIComponent_val,
    twistedChartDIComponent_val, twistedChartDIComponent_val, twistedChartForm_add,
    diSeqAltComponent_add, (chartFormsEquiv c i).symm.map_add, Submodule.coe_add,
    (rationalFormsSectionsEquiv K i c.U).map_add, smul_add]

omit [Fact p.Prime] [CharP K p] in
theorem rationalFormsSectionsEquiv_chartFormsEquiv_symm (b : ℕ) (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    haveI := c.nonempty
    rationalFormsSectionsEquiv K b c.U ((chartFormsEquiv c b).symm z).1 =
      sectionFormsMap (K := K) c.U b z := by
  have := c.nonempty
  have h := sectionFormsMap_chartFormsEquiv c b ((chartFormsEquiv c b).symm z)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h, regularFormsValue_apply]

omit [Fact p.Prime] [CharP K p] in
/-- On a chart, the de Rham differential of rational forms is the de Rham differential of the
chart. -/
theorem rationalFormsDiff_sectionFormsMap (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ)
    (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    haveI := c.nonempty
    rationalFormsDiff c₀ b (sectionFormsMap (K := K) c.U b z) =
      sectionFormsMap (K := K) c.U (b + 1) ⟨kaehlerDeRhamDiff c.coords c.formallyEtale z,
        kaehlerDeRhamDiff_mem_exteriorPower _ _ z.2⟩ := by
  have := c.nonempty
  have h := chartFormsEquiv_regularFormsDiff c₀ c hcover b ((chartFormsEquiv c b).symm z)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← rationalFormsSectionsEquiv_chartFormsEquiv_symm c b z, ← regularFormsValue_apply,
    ← regularFormsValue_regularFormsDiff c₀ hcover, ← sectionFormsMap_chartFormsEquiv, h]

/-- **In Čech degree `0`, the twisted component is `b! · Φ_{D, F_{s 0}}`** (check 437). -/
theorem twistedChartDIComponent_zero (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b : ℕ)
    (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    twistedChartDIComponent c π hπ p F hF hker hg b b 0 (add_zero b) s ω =
      (b.factorial : ℤ) • twistedChartFrobeniusLiftForms c π hπ p (F (s 0)) (hF (s 0)) hker hg b ω := by
  have hcomp : diSeqAltComponent c π hπ p F hF hker b b 0 (add_zero b) s (twistedChartForm c hg ω) =
      (b.factorial : ℤ) • (⟨frobeniusLiftExterior c.coords c.formallyEtale π hπ p (F (s 0)) (hF (s 0))
        hker (twistedChartForm c hg ω), frobeniusLiftExterior_mem_exteriorPower _ _ π hπ p (F (s 0))
          (hF (s 0)) hker (twistedChartForm c hg ω).2⟩ : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) := by
    apply Subtype.ext
    rw [diSeqAltComponent_coe, diSeqAlt_zero, Submodule.coe_smul_of_tower]
  have e1 : ∀ (k : ℤ) (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]),
      (chartFormsEquiv c b).symm (k • z) = k • (chartFormsEquiv c b).symm z :=
    fun k z => (chartFormsEquiv c b).symm.toAddMonoidHom.map_zsmul k z
  have e2 : ∀ (k : ℤ) (w : Γ(rationalFormsSheaf K X b, c.U)),
      rationalFormsSectionsEquiv K b c.U (k • w) = k • rationalFormsSectionsEquiv K b c.U w :=
    fun k w => (rationalFormsSectionsEquiv K b c.U).toAddMonoidHom.map_zsmul k w
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b c.U).injective
  rw [twistedChartDIComponent_val, hcomp, e1, Submodule.coe_smul_of_tower, e2,
    Submodule.coe_smul_of_tower, e2, twistedChartFrobeniusLiftForms_val, smul_comm]
  rfl

/-- Dividing a form of the chart by `g ^ p`, as a section of `Ω^i(p • D)`. -/
noncomputable def twistBackForms (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (i : ℕ)
    (z : ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K]) : twistedFormsSections K (p • D) i c.U :=
  ⟨_, inv_pow_smul_mem_twisted c p hg ((chartFormsEquiv c i).symm z)⟩

omit [Fact p.Prime] [CharP K p] in
theorem twistBackForms_val (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (i : ℕ)
    (z : ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K]) :
    haveI := c.nonempty
    rationalFormsSectionsEquiv K i c.U (twistBackForms c p hg i z).1 =
      ((g : X.functionField)⁻¹) ^ p • sectionFormsMap (K := K) c.U i z := by
  have := c.nonempty
  change rationalFormsSectionsEquiv K i c.U ((rationalFormsSectionsEquiv K i c.U).symm _) = _
  rw [AddEquiv.apply_symm_apply, rationalFormsSectionsEquiv_chartFormsEquiv_symm]

omit [Fact p.Prime] [CharP K p] in
theorem twistBackForms_add (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (i : ℕ)
    (z z' : ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K]) :
    twistBackForms c p hg i (z + z') = twistBackForms c p hg i z + twistBackForms c p hg i z' := by
  have := c.nonempty
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K i c.U).injective
  rw [Submodule.coe_add, (rationalFormsSectionsEquiv K i c.U).map_add, twistBackForms_val,
    twistBackForms_val, twistBackForms_val, map_add, smul_add]

omit [Fact p.Prime] [CharP K p] in
theorem twistBackForms_zero (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (i : ℕ) :
    twistBackForms c p hg i 0 = 0 := by
  have h := twistBackForms_add c p hg i 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- `twistBackForms` as an additive map. -/
noncomputable def twistBackFormsHom (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (i : ℕ) :
    ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K] →+ twistedFormsSections K (p • D) i c.U where
  toFun := twistBackForms c p hg i
  map_zero' := twistBackForms_zero c p hg i
  map_add' := twistBackForms_add c p hg i

theorem twistedChartDIComponent_eq (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b i a : ℕ)
    (h : i + a = b) (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω =
      twistBackForms c p hg i (diSeqAltComponent c π hπ p F hF hker b i a h s (twistedChartForm c hg ω)) :=
  rfl

omit [Fact p.Prime] in
/-- **`d` commutes with dividing by `g ^ p`.** -/
theorem twistedFormsDiff_twistBackForms (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (i : ℕ)
    (z : ⋀[Γ(X, c.U)]^i Ω[Γ(X, c.U)⁄K]) :
    haveI := c.nonempty
    twistedFormsDiff p c₀ hcover D i c.U (twistBackForms c p hg i z) =
      twistBackForms c p hg (i + 1) ⟨kaehlerDeRhamDiff c.coords c.formallyEtale z,
        kaehlerDeRhamDiff_mem_exteriorPower _ _ z.2⟩ := by
  have := c.nonempty
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (i + 1) c.U).injective
  rw [rationalFormsSectionsEquiv_twistedFormsDiff, twistBackForms_val, twistBackForms_val,
    rationalFormsDiff_smul_pow_char p c₀ i, rationalFormsDiff_sectionFormsMap c c₀ hcover i z]

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hK : ∀ k : K, ∃ k' : L, π k' = algebraMap K Γ(X, c.U) k ∧ ∀ j, F j k' = k' ^ p)

omit [IsIntegral X] in
include hann hp2 hK in
/-- The cocycle relation of the Deligne–Illusie map on the forms of the chart, componentwise. -/
theorem diSeqAltComponent_cocycle [Algebra.FiniteType K Γ(X, c.U)] (b i a : ℕ)
    (h : i + (a + 1) = b) (s : ℕ → J) (x : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    ∑ k ∈ Finset.range (a + 2), (-1 : ℤ) ^ k •
        diSeqAltComponent c π hπ p F hF hker b (i + 1) a (by omega) (s ∘ seqSkip k) x =
      (-1 : ℤ) ^ a • ⟨kaehlerDeRhamDiff c.coords c.formallyEtale
        (diSeqAltComponent c π hπ p F hF hker b i (a + 1) h s x),
          kaehlerDeRhamDiff_mem_exteriorPower _ _ (diSeqAltComponent c π hπ p F hF hker b i (a + 1) h s x).2⟩ := by
  have hD := congrFun (congrFun (seqTotalD_diSeqAlt c.coords c.formallyEtale π hπ p F hF hker hann
    hp2 hK b x) (a + 1)) s
  simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, Pi.zero_apply,
    LinearMap.toAddMonoidHom_coe] at hD
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  simp only [Submodule.coe_smul_of_tower, diSeqAltComponent_coe]
  have hsum : ∀ (k : ℕ) (y : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]),
      (-1 : ℤ) ^ k • y = (-1 : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) ^ k * y := fun k y => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  simp only [hsum]
  rw [eq_neg_of_add_eq_zero_left hD, pow_succ]
  noncomm_ring

include hann hp2 hK in
/-- **The cocycle relation of the twisted components**:
`Σ_{k ≤ a+1} (-1)^k Θ^{b,a}_{s ∘ skip k}(ω) = (-1)^a d Θ^{b,a+1}_s(ω)`. -/
theorem twistedChartDIComponent_cocycle [Algebra.FiniteType K Γ(X, c.U)]
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b i a : ℕ) (h : i + (a + 1) = b)
    (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    haveI := c.nonempty
    ∑ k ∈ Finset.range (a + 2), (-1 : ℤ) ^ k •
        twistedChartDIComponent c π hπ p F hF hker hg b (i + 1) a (by omega) (s ∘ seqSkip k) ω =
      (-1 : ℤ) ^ a • twistedFormsDiff p c₀ hcover D i c.U
        (twistedChartDIComponent c π hπ p F hF hker hg b i (a + 1) h s ω) := by
  have := c.nonempty
  simp only [twistedChartDIComponent_eq]
  rw [twistedFormsDiff_twistBackForms c p hg c₀ hcover i]
  have e : ∀ (j : ℕ) (z : ⋀[Γ(X, c.U)]^j Ω[Γ(X, c.U)⁄K]),
      twistBackForms c p hg j z = twistBackFormsHom c p hg j z := fun _ _ => rfl
  simp only [e, ← map_zsmul, ← map_sum]
  rw [diSeqAltComponent_cocycle c π hπ p F hF hker hann hp2 hK b i a h s]

include hann hp2 hK in
/-- **In Čech degree `0` the twisted components are closed.** -/
theorem twistedFormsDiff_twistedChartDIComponent_zero [Algebra.FiniteType K Γ(X, c.U)]
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) (s : ℕ → J)
    (ω : twistedFormsSections K D b c.U) :
    haveI := c.nonempty
    twistedFormsDiff p c₀ hcover D b c.U
      (twistedChartDIComponent c π hπ p F hF hker hg b b 0 (add_zero b) s ω) = 0 := by
  have := c.nonempty
  rw [twistedChartDIComponent_zero, map_zsmul,
    twistedFormsDiff_twistedChartFrobeniusLiftForms c π hπ p (F (s 0)) (hF (s 0)) hker hann hp2
      (fun k => (hK k).imp fun k' h => ⟨h.1, h.2 (s 0)⟩) hg c₀ hcover b, smul_zero]

end MixedFujita
