/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedDeRhamCech

/-!
Linearity of the twisted de Rham differential (step 10).

The de Rham differential is not `𝒪_X`-linear, but it is linear for the functions whose differential
vanishes: the constants of `K` (`rationalFormsDiff_algebraMap_smul`) and, in characteristic `p`,
the `p`-th powers (check-418). On the sections of `Ω^•_X(p • D)` over every open subset it commutes
with multiplication by the image of a constant (`twistedFormsDiffApp_algebraMap_smul`, so it is
`K`-linear) and with multiplication by the `p`-th power of a function (`twistedFormsDiffApp_pow_smul`:
it is `𝒪_{X'}`-linear for the Frobenius twist). These are the linear structures of the
Čech–de Rham complexes needed for the dimension count.
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

/-- **The de Rham differential commutes with constants.** -/
theorem rationalFormsDiff_algebraMap_smul (c₀ : EtaleChart K X n) (b : ℕ) (c : K)
    (ω : RationalForms K X b) :
    rationalFormsDiff c₀ b (algebraMap K X.functionField c • ω) =
      algebraMap K X.functionField c • rationalFormsDiff c₀ b ω := by
  apply Subtype.ext
  rw [rationalFormsDiff_coe, Submodule.coe_smul, Submodule.coe_smul, rationalFormsDiff_coe,
    rationalDeRhamDiff, kaehlerDeRhamDiff_smul, Derivation.map_algebraMap, map_zero,
    zero_mul, zero_add]

/-- The germ of a `p`-th power is the `p`-th power of the germ; with check-418, `d(f^p ω) = f^p dω`
on sections. -/
theorem twistedFormsDiffApp_pow_smul (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) (f : Γ(X, U)) (s : Γ(twistedFormsSheaf K (p • D) b, U)) :
    twistedFormsDiffApp p c₀ hcover D b U ((f ^ p) • s) =
      (f ^ p) • twistedFormsDiffApp p c₀ hcover D b U s := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton (p • D) (b + 1) hU) _ _
  · apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (b + 1) U).injective
    rw [rationalFormsSectionsEquiv_twistedFormsDiffApp]
    change rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U ((f ^ p) • s.1)) =
      rationalFormsSectionsEquiv K (b + 1) U ((f ^ p) • (twistedFormsDiffApp p c₀ hcover D b U s).1)
    rw [rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_smul, map_pow,
      rationalFormsDiff_smul_pow_char p c₀ b, rationalFormsSectionsEquiv_twistedFormsDiffApp]

/-- **The twisted de Rham differential is `K`-linear on sections.** -/
theorem twistedFormsDiffApp_algebraMap_smul (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) (c : K) (s : Γ(twistedFormsSheaf K (p • D) b, U)) :
    twistedFormsDiffApp p c₀ hcover D b U (algebraMap K Γ(X, U) c • s) =
      algebraMap K Γ(X, U) c • twistedFormsDiffApp p c₀ hcover D b U s := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton (p • D) (b + 1) hU) _ _
  · apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (b + 1) U).injective
    rw [rationalFormsSectionsEquiv_twistedFormsDiffApp]
    change rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U
        (algebraMap K Γ(X, U) c • s.1)) =
      rationalFormsSectionsEquiv K (b + 1) U
        (algebraMap K Γ(X, U) c • (twistedFormsDiffApp p c₀ hcover D b U s).1)
    have hc : X.germToFunctionField U (algebraMap K Γ(X, U) c) = algebraMap K X.functionField c :=
      (sectionGermAlgHom (K := K) U).commutes c
    rw [rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_smul, hc,
      rationalFormsDiff_algebraMap_smul, rationalFormsSectionsEquiv_twistedFormsDiffApp]

end MixedFujita
