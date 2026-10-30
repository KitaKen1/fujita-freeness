/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieVanishingReduction
public import MixedFujita.CanonicalCartierTopForms

/-!
`𝒪_X(K_X + D) ≅ Ω^n_X(D)` (step 10).

Let `ω₀ = dx₁ ∧ ⋯ ∧ dxₙ` be the top form of a reference étale chart `c₀`, so that the canonical
divisor `K_X` (CanonicalDivisor) has the local equation `g_c` with `ω₀ = g_c · dx^{(c)}` on each
chart `c`. A rational top form `h ω₀` is regular at a point of `c` iff `g_c h` is regular there
(`smul_referenceTopForm_mem_range_iff`, check-281). Hence `ω₀` is a nowhere vanishing section of
`Ω^n_X(-K_X)`, and multiplication by `ω₀` is an isomorphism `𝒪_X ≅ Ω^n_X(-K_X)`
(`unitIsoTwistedTopForms`, as for the chart lattices of check-417). With
`𝒪_X(E) ⊗ Ω^n_X(F) ≅ Ω^n_X(E + F)` (check-419) this gives
**`𝒪_X(K_X + D) ≅ Ω^n_X(D)`** (`canonicalTwistIso`).

So the vanishing of check-422 takes the form used by the Kawamata–Viehweg statements:
`H^j(𝒪_X(K_X + D)) = 0` for `j ≥ 1` and `D` ample, from the Deligne–Illusie inequality
(`canonical_vanishing_of_deligneIllusie`, Kodaira vanishing).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The top form `dx₁ ∧ ⋯ ∧ dxₙ` of the reference chart, as a rational form. -/
noncomputable abbrev referenceTopForm (c₀ : EtaleChart K X n) : RationalForms K X n :=
  exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀)

/-- **`h ω₀` is regular at a point of a chart `c` iff `g_c h` is regular there.** -/
theorem smul_referenceTopForm_mem_range_iff (c₀ c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (h : X.functionField) :
    h • referenceTopForm c₀ ∈ LinearMap.range (stalkFormsMap K n x) ↔
      (etaleChartCanonicalEquation c₀ c : X.functionField) * h ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have hcoord : determinantCoordinate (etaleChartBasis c) (h • referenceTopForm c₀) =
      (etaleChartCanonicalEquation c₀ c : X.functionField) * h := by
    rw [referenceTopForm, ← etaleChartCanonicalEquation_top_wedge c₀ c, smul_smul, map_smul,
      determinantCoordinate_wedge, Module.Basis.det_self, smul_eq_mul, mul_one, mul_comm]
  rw [← hcoord]
  exact top_differential_mem_stalk_range_iff c x hx (h • referenceTopForm c₀)

omit [IsIntegral X] in
theorem exists_etaleChart_mem (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (x : X) :
    ∃ c : EtaleChart K X n, x ∈ c.U := by
  have hmem : x ∈ iSup (fun c : EtaleChart K X n => c.U) := hcover.symm ▸ Opens.mem_top x
  simpa only [Opens.mem_iSup] using hmem

/-- **`h ω₀` has poles bounded by `-K_X` at `x` iff `h` is regular at `x`.** -/
theorem smul_referenceTopForm_mem_negCanonical_iff (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (x : X) (h : X.functionField)
    (f : X.functionFieldˣ) (hf : (-canonicalDivisor n c₀ hcover).IsLocalEquationAt x f) :
    (f : X.functionField) • (h • referenceTopForm c₀) ∈ LinearMap.range (stalkFormsMap K n x) ↔
      h ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨c, hxc⟩ := exists_etaleChart_mem hcover x
  have hg := (canonicalDivisor_isLocalEquationAt c₀ hcover c hxc).inv
  rw [smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf hg, smul_smul,
    smul_referenceTopForm_mem_range_iff c₀ c x hxc, ← mul_assoc, Units.mul_inv, one_mul]

/-- The reference top form as a global section of the rational top forms. -/
noncomputable def referenceTopFormSection (c₀ : EtaleChart K X n) : Γ(rationalFormsSheaf K X n, ⊤) :=
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  (rationalFormsSectionsEquiv K n ⊤).symm (referenceTopForm c₀)

/-- Multiplication by the reference top form, `𝒪_X → (rational top forms)`. -/
noncomputable def referenceTopFormMap (c₀ : EtaleChart K X n) :
    CohomologyAux.unitModule X ⟶ rationalFormsSheaf K X n :=
  CohomologyAux.homOfSection _ (referenceTopFormSection c₀)

theorem rationalFormsSectionsEquiv_referenceTopFormMap (c₀ : EtaleChart K X n) (W : X.Opens)
    [Nonempty W] (r : Γ(X, W)) :
    rationalFormsSectionsEquiv K n W ((referenceTopFormMap c₀).app W r) =
      X.germToFunctionField W r • referenceTopForm c₀ := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  rw [referenceTopFormMap, CohomologyAux.homOfSection_app, rationalFormsSectionsEquiv_smul,
    rationalFormsSectionsEquiv_map K n (homOfLE le_top : W ⟶ ⊤), referenceTopFormSection,
    AddEquiv.apply_symm_apply]

theorem referenceTopFormMap_mem (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (W : (X.Opens)ᵒᵖ)
    (r : (CohomologyAux.unitModule X).val.obj W) :
    (referenceTopFormMap c₀).val.app W r ∈
      (twistedFormsSubmodule K (-canonicalDivisor n c₀ hcover) n).obj W := by
  induction W using Opposite.rec with | op W => ?_
  intro x hx f hf
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  change (f : X.functionField) • rationalFormsSectionsEquiv K n W
    ((referenceTopFormMap c₀).app W r) ∈ _
  rw [rationalFormsSectionsEquiv_referenceTopFormMap,
    smul_referenceTopForm_mem_negCanonical_iff c₀ hcover x _ f hf,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := W) hx]
  exact ⟨_, rfl⟩

theorem referenceTopForm_coordinate (c₀ : EtaleChart K X n) :
    determinantCoordinate (etaleChartBasis c₀) (referenceTopForm c₀) = 1 := by
  rw [referenceTopForm, determinantCoordinate_wedge, Module.Basis.det_self]

theorem referenceTopFormMap_injective (c₀ : EtaleChart K X n) (W : (X.Opens)ᵒᵖ) :
    Function.Injective ((referenceTopFormMap c₀).val.app W) := by
  induction W using Opposite.rec with | op W => ?_
  intro r r' h
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (CohomologyAux.unitModule X) hbot) _ _
  · have h' : rationalFormsSectionsEquiv K n W ((referenceTopFormMap c₀).app W r) =
        rationalFormsSectionsEquiv K n W ((referenceTopFormMap c₀).app W r') := congrArg _ h
    rw [rationalFormsSectionsEquiv_referenceTopFormMap,
      rationalFormsSectionsEquiv_referenceTopFormMap] at h'
    have h'' := congrArg (determinantCoordinate (etaleChartBasis c₀)) h'
    rw [map_smul, map_smul, referenceTopForm_coordinate, smul_eq_mul, smul_eq_mul, mul_one,
      mul_one] at h''
    exact Scheme.germToFunctionField_injective X W h''

theorem referenceTopFormMap_surjective (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (W : (X.Opens)ᵒᵖ)
    (s : (rationalFormsSheaf K X n).val.obj W)
    (hs : s ∈ (twistedFormsSubmodule K (-canonicalDivisor n c₀ hcover) n).obj W) :
    ∃ t, (referenceTopFormMap c₀).val.app W t = s := by
  induction W using Opposite.rec with | op W => ?_
  rcases isEmpty_or_nonempty W with hW | hW
  · have hbot : W = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    exact ⟨0, @Subsingleton.elim _ (modules_sections_subsingleton_of_eq_bot
      (rationalFormsSheaf K X n) hbot) _ _⟩
  · set h := determinantCoordinate (etaleChartBasis c₀) (rationalFormsSectionsEquiv K n W s)
    have hω : h • referenceTopForm c₀ = rationalFormsSectionsEquiv K n W s :=
      topExterior_coordinate_smul_wedge (etaleChartBasis c₀) _
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range (U := W) (f := h)
      fun y hy => by
        obtain ⟨f, hf⟩ := (-canonicalDivisor n c₀ hcover).exists_isLocalEquationAt y
        have hsy := hs y hy f hf
        rw [← hω] at hsy
        exact (smul_referenceTopForm_mem_negCanonical_iff c₀ hcover y h f hf).mp hsy
    refine ⟨a, (rationalFormsSectionsEquiv K n W).injective ?_⟩
    change rationalFormsSectionsEquiv K n W ((referenceTopFormMap c₀).app W a) = _
    rw [rationalFormsSectionsEquiv_referenceTopFormMap, ha, hω]

/-- **`𝒪_X ≅ Ω^n_X(-K_X)`**, multiplication by the reference top form. -/
noncomputable def unitIsoTwistedTopForms (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) :
    CohomologyAux.unitModule X ≅ twistedFormsSheaf K (-canonicalDivisor n c₀ hcover) n :=
  haveI := TauCeti.SheafOfModules.isIso_liftToSubmodule
    (twistedFormsSubmodule K (-canonicalDivisor n c₀ hcover) n) (referenceTopFormMap c₀)
    (referenceTopFormMap_mem c₀ hcover) (referenceTopFormMap_injective c₀)
    (referenceTopFormMap_surjective c₀ hcover)
  asIso (TauCeti.SheafOfModules.liftToSubmodule
    (twistedFormsSubmodule K (-canonicalDivisor n c₀ hcover) n) (referenceTopFormMap c₀)
    (referenceTopFormMap_mem c₀ hcover))

/-- **`𝒪_X(K_X + D) ≅ Ω^n_X(D)`.** -/
noncomputable def canonicalTwistIso (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) :
    (canonicalDivisor n c₀ hcover + D).sheaf ≅ twistedFormsSheaf K D n :=
  (ρ_ (canonicalDivisor n c₀ hcover + D).sheaf).symm ≪≫
    whiskerLeftIso (canonicalDivisor n c₀ hcover + D).sheaf (unitIsoTwistedTopForms c₀ hcover) ≪≫
    twistedTensorSheafIso K (canonicalDivisor n c₀ hcover + D) (-canonicalDivisor n c₀ hcover) n ≪≫
    eqToIso (congrArg (fun E => twistedFormsSheaf K E n) (by abel))

/-- **Kodaira vanishing from the Deligne–Illusie inequality**: `H^j(𝒪_X(K_X + D)) = 0` for
`j ≥ 1` and `D` ample on a proper integral scheme covered by étale charts, if the Deligne–Illusie
inequality holds for the multiples `p^k D` in every total degree `m > n`. -/
theorem canonical_vanishing_of_deligneIllusie [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (p : ℕ)
    (hp : 2 ≤ p) (D : CartierDivisor X) (hD : CartierIsAmpleProj K D)
    (hDI : ∀ k m, n < m → DeligneIllusieInequality K ((p ^ k) • D) p n m) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + D).sheaf j) := by
  have h := twistedFormsSheaf_vanishing_of_deligneIllusie hcover p hp D hD hDI (b := n) (j := j)
    le_rfl (by omega)
  let e := ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X j).mapIso
    (canonicalTwistIso c₀ hcover D)).addCommGroupIsoToAddEquiv
  exact @Equiv.subsingleton _ _ e.toEquiv h

end MixedFujita
