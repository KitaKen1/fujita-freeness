/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedCechDeRhamTotal
public import MixedFujita.TwistedDeRhamLinearity

/-!
The `K`-linear Čech–de Rham double complex (step 10).

To count dimensions over `K`, the Čech complexes of SGA (complexes of abelian groups) are rebuilt as
complexes of `K`-modules. The sections of an `𝒪_X`-module are `K`-modules through
`K → Γ(X, V)` (`sectionsBaseModule`), restrictions are `K`-linear
(`presheaf_map_homOfLE_base_smul`), hence so is the Čech differential (`cechD_base_smul`): the
`K`-linear Čech complex (`cechComplexLinear`, with the same underlying groups and differential as
SGA's). In characteristic `p`, the de Rham differential of `Ω^•_X(p • D)` is `K`-linear (check-426),
so it gives `K`-linear maps of Čech complexes (`twistedFormsCechDiffLinearMap`) with `d ∘ d = 0`, the
`K`-linear Čech–de Rham double complex (`twistedCechDeRhamBicomplexLinear`) and its total complex
(`twistedCechDeRhamTotalLinear`), whose homology is the hypercohomology of `Ω^•_X(p • D)` as a
`K`-vector space (`twistedHypercohomologyLinear`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra

variable (K) in
/-- The `K`-module structure on the sections of an `𝒪_X`-module, through `K → Γ(X, V)`. -/
noncomputable abbrev sectionsBaseModule (M : X.Modules) (V : X.Opens) : Module K Γ(M, V) :=
  Module.compHom Γ(M, V) (algebraMap K Γ(X, V))

attribute [local instance] sectionsBaseModule

theorem sectionsBase_smul_def (M : X.Modules) (V : X.Opens) (c : K) (s : Γ(M, V)) :
    c • s = algebraMap K Γ(X, V) c • s := rfl

/-- Restrictions are `K`-linear. -/
theorem presheaf_map_homOfLE_base_smul (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (c : K)
    (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (c • s) = c • M.presheaf.map (homOfLE h).op s := by
  rw [sectionsBase_smul_def, sectionsBase_smul_def, Scheme.Modules.map_smul]
  congr 1
  exact (sectionRestrict K h).commutes c

/-- **The Čech differential is `K`-linear.** -/
theorem cechD_base_smul (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) (m : ℕ) (c : K)
    (f : TopCat.Presheaf.CechCochain 𝒰 M.presheaf m) :
    TopCat.Presheaf.cechD 𝒰 M.presheaf m (c • f) =
      c • TopCat.Presheaf.cechD 𝒰 M.presheaf m f := by
  funext x
  rw [TopCat.Presheaf.cechD_apply, Pi.smul_apply, TopCat.Presheaf.cechD_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, presheaf_map_homOfLE_base_smul, smul_comm]

variable (K) in
/-- The Čech differential as a `K`-linear map. -/
noncomputable def cechDLinear (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) (m : ℕ) :
    TopCat.Presheaf.CechCochain 𝒰 M.presheaf m →ₗ[K]
      TopCat.Presheaf.CechCochain 𝒰 M.presheaf (m + 1) where
  toFun := TopCat.Presheaf.cechD 𝒰 M.presheaf m
  map_add' := map_add _
  map_smul' := cechD_base_smul M 𝒰 m

variable (K) in
/-- **The `K`-linear Čech complex** of an `𝒪_X`-module. -/
noncomputable def cechComplexLinear (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) :
    CochainComplex (ModuleCat.{u} K) ℕ :=
  CochainComplex.of (fun m => ModuleCat.of K (TopCat.Presheaf.CechCochain 𝒰 M.presheaf m))
    (fun m => ModuleCat.ofHom (cechDLinear K M 𝒰 m))
    (fun m => ModuleCat.hom_ext
      (LinearMap.ext fun f => TopCat.Presheaf.cechD_cechD 𝒰 M.presheaf m f))

theorem cechComplexLinear_d (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) (m : ℕ) :
    (cechComplexLinear K M 𝒰).d m (m + 1) = ModuleCat.ofHom (cechDLinear K M 𝒰 m) := by
  unfold cechComplexLinear
  exact CochainComplex.of_d
    (fun m => ModuleCat.of K (TopCat.Presheaf.CechCochain 𝒰 M.presheaf m))
    (fun m => ModuleCat.ofHom (cechDLinear K M 𝒰 m)) m

section DeRham

variable [IsIntegral X] {n : ℕ}

attribute [local instance] cartierGlobalStalkFunctionFieldTower cartierBaseLocalScalarTower
  functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The de Rham differential of `Ω^•_X(p • D)` on Čech cochains, `K`-linearly. -/
noncomputable def twistedFormsCechDiffLinear (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (m : ℕ) :
    TopCat.Presheaf.CechCochain 𝒰 (twistedFormsSheaf K (p • D) b).presheaf m →ₗ[K]
      TopCat.Presheaf.CechCochain 𝒰 (twistedFormsSheaf K (p • D) (b + 1)).presheaf m where
  toFun := TopCat.Presheaf.cechCochainMap 𝒰 (twistedFormsDiffPresheaf p c₀ hcover D b) m
  map_add' := map_add _
  map_smul' c f := by
    funext x
    rw [TopCat.Presheaf.cechCochainMap_apply, Pi.smul_apply, Pi.smul_apply,
      TopCat.Presheaf.cechCochainMap_apply]
    exact twistedFormsDiffApp_algebraMap_smul p c₀ hcover D b _ c (f x)

/-- The de Rham differential as a `K`-linear map of Čech complexes. -/
noncomputable def twistedFormsCechDiffLinearMap (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰 ⟶
      cechComplexLinear K (twistedFormsSheaf K (p • D) (b + 1)) 𝒰 :=
  CochainComplex.ofHom
    (fun m => ModuleCat.ofHom (twistedFormsCechDiffLinear p c₀ hcover D b 𝒰 m))
    (fun m => by
      rw [cechComplexLinear_d, cechComplexLinear_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun f =>
        TopCat.Presheaf.cechD_cechCochainMap 𝒰 (twistedFormsDiffPresheaf p c₀ hcover D b) f))

theorem twistedFormsCechDiffLinearMap_comp (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰 ≫
      twistedFormsCechDiffLinearMap p c₀ hcover D (b + 1) 𝒰 = 0 := by
  ext m : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
  change (twistedFormsDiffPresheaf p c₀ hcover D (b + 1)).app _
      ((twistedFormsDiffPresheaf p c₀ hcover D b).app _ (f x)) = 0
  have h := congrArg (fun φ => φ.app (op (TopCat.Presheaf.cechOpen 𝒰 x)) (f x))
    (twistedFormsDiffPresheaf_comp p c₀ hcover D b)
  simpa using h

/-- **The `K`-linear Čech–de Rham double complex** of `Ω^•_X(p • D)`. -/
noncomputable def twistedCechDeRhamBicomplexLinear (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    HomologicalComplex₂ (ModuleCat.{u} K) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
    (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
    (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰)

/-- The total complex of the `K`-linear Čech–de Rham double complex. -/
noncomputable def twistedCechDeRhamTotalLinear (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) : CochainComplex (ModuleCat.{u} K) ℕ :=
  (twistedCechDeRhamBicomplexLinear p c₀ hcover D 𝒰).total (ComplexShape.up ℕ)

/-- **The hypercohomology of `Ω^•_X(p • D)` as a `K`-vector space.** -/
noncomputable def twistedHypercohomologyLinear (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (m : ℕ) : ModuleCat.{u} K :=
  (twistedCechDeRhamTotalLinear p c₀ hcover D 𝒰).homology m

end DeRham

end MixedFujita
