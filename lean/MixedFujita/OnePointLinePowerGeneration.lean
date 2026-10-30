/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANaturalSectionModuleDictionary

/-! 一点スキーム上の実直線束全整数冪の大域生成。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Every integer line-bundle power on a one-point scheme has an actual
generating global section; its trivializing open is already the whole scheme. -/
theorem sga_moduleIsGloballyGenerated_of_subsingleton
    {X : Scheme.{u}} [Subsingleton X] (L : X.LineBundle) (n : ℤ) :
    moduleIsGloballyGenerated (L.toModules n) := by
  intro x
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [L.iSup_eq_top]; trivial)
  have htop : (⊤ : X.Opens) ≤ L.U k := fun y _ => Subsingleton.elim x y ▸ hk
  let s : Γ(L.toModules n, ⊤) := L.ofUnit n k htop (1 : Γ(X, ⊤))
  refine ⟨L.U k, hk, sgaLineBundleOverFrameIso L n k, s, ?_⟩
  unfold moduleOverFrameGlobalCoefficientGerm
  change IsUnit (X.presheaf.germ (L.U k) x hk
    (L.toUnit k le_rfl (L.resHom n le_top s)))
  have hs : L.toUnit k htop s = 1 := L.toUnit_ofUnit k htop _
  rw [L.toUnit_resHom k htop le_top s, hs, map_one, map_one]
  exact isUnit_one

end MixedFujita
