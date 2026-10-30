/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANaturalSectionModuleDictionary

/-! 任意の非被約源で自然次数SGA切断と実大域加群切断の全単射。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Inverse of the actual natural-degree SGA-to-module global section
map. Top-intersection restrictions are constructed on every component. -/
noncomputable def sgaModuleGlobalSectionToNatural {X : Scheme.{u}} (L : X.LineBundle)
    (n : ℕ) (t : Γ(L.toModules (n : ℤ), ⊤)) : L.sections n := by
  refine ⟨fun i => X.presheaf.map (homOfLE (le_inf le_top le_rfl : L.U i ≤ ⊤ ⊓ L.U i)).op (t.val i), ?_⟩
  intro i j
  have h := congrArg (X.presheaf.map (homOfLE
    (le_inf le_top le_rfl : L.U i ⊓ L.U j ≤ ⊤ ⊓ (L.U i ⊓ L.U j))).op) (t.property i j)
  simpa only [Scheme.LineBundle.trans, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_pow_eq_pow_val,
    map_mul, map_pow, CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_self] using h


/-- Every actual global section is retained by the natural-degree SGA dictionary. -/
theorem sgaNaturalSectionToModule_bijective {X : Scheme.{u}} (L : X.LineBundle) (n : ℕ) :
    Function.Bijective (sgaNaturalSectionToModule L n) := by
  refine ⟨?_, ?_⟩
  · intro s t h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : Γ(L.toModules (n : ℤ), ⊤) =>
      (sgaModuleGlobalSectionToNatural L n z).val i) h
    simpa only [sgaModuleGlobalSectionToNatural, sgaNaturalSectionToModule,
      CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_self] using hi
  · intro t
    refine ⟨sgaModuleGlobalSectionToNatural L n t, ?_⟩
    apply Subtype.ext
    funext i
    simp only [sgaModuleGlobalSectionToNatural, sgaNaturalSectionToModule,
      CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_self]

end MixedFujita
