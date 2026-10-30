/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleGlobalGeneration
public import SGA.Foundations.Cohomology.InvertibleSheaf

/-! 自然次数SGA切断と実加群切断・局所係数・生成の辞書。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The natural-degree section of an SGA line bundle is an actual global
section of its integer-power module, including on nonreduced schemes. -/
noncomputable def sgaNaturalSectionToModule {X : Scheme.{u}} (L : X.LineBundle)
    (n : ℕ) (s : L.sections n) : Γ(L.toModules (n : ℤ), ⊤) := by
  refine ⟨fun i => X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ L.U i ≤ L.U i)).op (s.val i), ?_⟩
  intro i j
  have h := congrArg (X.presheaf.map (homOfLE
    (inf_le_right : ⊤ ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op) (s.property i j)
  simpa only [Scheme.LineBundle.trans, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_pow_eq_pow_val,
    map_mul, map_pow, CohomologyAux.presheaf_map_map] using h


/-- The actual rank-one frame of an SGA power on its defining open. -/
noncomputable def sgaLineBundleOverFrameIso {X : Scheme.{u}} (L : X.LineBundle)
    (n : ℤ) (k : L.ι) :
    (L.toModules n).over (L.U k) ≅ SheafOfModules.unit (X.ringCatSheaf.over (L.U k)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun W => (L.unitEquiv (n := n) k W.unop.hom.le).toModuleIso)
      (fun W W' f => by
        ext s
        exact L.toUnit_resHom k W.unop.hom.le f.unop.left.le s)


/-- The actual module coefficient of the actual section is the original
SGA coordinate; all top-open and trivialization transports are internal. -/
theorem sgaNaturalSectionToModule_frame_coefficient {X : Scheme.{u}}
    (L : X.LineBundle) (n : ℕ) (s : L.sections n) (k : L.ι) :
    moduleOverFrameCoefficient (L.toModules (n : ℤ)) (L.U k)
      (sgaLineBundleOverFrameIso L n k) (L.U k) le_rfl
        ((L.toModules (n : ℤ)).presheaf.map (homOfLE le_top : L.U k ⟶ ⊤).op
          (sgaNaturalSectionToModule L n s)) = s.val k := by
  change L.toUnit k le_rfl (L.resHom (n : ℤ) le_top (sgaNaturalSectionToModule L n s)) = s.val k
  rw [Scheme.LineBundle.toUnit_apply, Scheme.LineBundle.resHom_apply]
  simp only [sgaNaturalSectionToModule, CohomologyAux.presheaf_map_map]
  exact CohomologyAux.presheaf_map_self _ _


/-- Nonvanishing SGA sections give actual module generators, with no
integral or reduced hypothesis on the scheme. -/
theorem moduleIsGloballyGenerated_sga_of_nonvanishing_cover {X : Scheme.{u}}
    (L : X.LineBundle) (n : ℕ)
    (h : ∀ x : X, ∃ s : L.sections n, x ∈ L.nonvanishingLocus s) :
    moduleIsGloballyGenerated (L.toModules (n : ℤ)) := by
  intro x
  obtain ⟨s, hs⟩ := h x
  obtain ⟨k, hk⟩ := (L.mem_nonvanishingLocus s).mp hs
  have hx : x ∈ L.U k := (X.basicOpen_le (s.val k)) hk
  refine ⟨L.U k, hx, sgaLineBundleOverFrameIso L n k, sgaNaturalSectionToModule L n s, ?_⟩
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [sgaNaturalSectionToModule_frame_coefficient]
  exact (X.mem_basicOpen (s.val k) x hx).mp hk

end MixedFujita
