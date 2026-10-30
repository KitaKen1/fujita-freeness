/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePushforwardFrameCoefficients
public import MixedFujita.ModulePullbackFrameGenerators

/-! 実順像大域切断の辞書と像上の生成元の源への持ち上げ。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Actual global sections of a pushforward identify with actual source
sections; the only transport is the inverse image of the top open. -/
noncomputable def modulePushforwardGlobalSectionsAddEquiv {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (N : Y.Modules) :
    Γ((Scheme.Modules.pushforward φ).obj N, ⊤) ≃+ Γ(N, ⊤) :=
  (N.presheaf.mapIso (eqToIso φ.preimage_top.symm).op).addCommGroupIsoToAddEquiv


/-- The actual global pushforward dictionary commutes with restriction to
inverse images of every source open. -/
theorem modulePushforwardGlobalSectionsAddEquiv_restrict {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (N : Y.Modules) (U : X.Opens)
    (s : Γ((Scheme.Modules.pushforward φ).obj N, ⊤)) :
    N.presheaf.map (homOfLE le_top : φ ⁻¹ᵁ U ⟶ ⊤).op
      (modulePushforwardGlobalSectionsAddEquiv φ N s) =
        ((Scheme.Modules.pushforward φ).obj N).presheaf.map (homOfLE le_top : U ⟶ ⊤).op s := by
  change N.presheaf.map _ (N.presheaf.map _ s) = N.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl


/-- The image of an actual global section under a map to a pushforward,
viewed on the original source, has the expected local restriction. -/
theorem moduleHomToPushforward_global_restrict {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N) (U : X.Opens) (s : Γ(M, ⊤)) :
    N.presheaf.map (homOfLE le_top : φ ⁻¹ᵁ U ⟶ ⊤).op
      (modulePushforwardGlobalSectionsAddEquiv φ N (Scheme.Modules.Hom.app f ⊤ s)) =
        Scheme.Modules.Hom.app f U (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) := by
  rw [modulePushforwardGlobalSectionsAddEquiv_restrict]
  exact (ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE le_top : U ⟶ ⊤).op) s).symm


/-- Global section surjectivity into a generated pulled line bundle gives
an actual generating source section at every point in the morphism's image.
No compatibility between the map and the pullback adjunction is assumed. -/
theorem module_generating_section_at_image_of_surjective_pushforward {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (M : X.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj M))
    (hf : Function.Surjective (Scheme.Modules.Hom.app f ⊤))
    (hN : moduleIsGloballyGenerated ((Scheme.Modules.pullback φ).obj M))
    (y : Y) (U : X.Opens) (hy : φ y ∈ U)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    ∃ s : Γ(M, ⊤), IsUnit (moduleOverFrameGlobalCoefficientGerm M U
      (moduleRestrictFrameOverIso M U e) (φ y) hy s) := by
  let N := (Scheme.Modules.pullback φ).obj M
  let d := modulePulledOpenFrame φ M U e
  obtain ⟨t, ht⟩ := moduleIsGloballyGenerated_at_frame hN y (φ ⁻¹ᵁ U) hy d
  obtain ⟨s, hs⟩ := hf ((modulePushforwardGlobalSectionsAddEquiv φ N).symm t)
  have hst : modulePushforwardGlobalSectionsAddEquiv φ N (Scheme.Modules.Hom.app f ⊤ s) = t := by
    rw [hs, AddEquiv.apply_symm_apply]
  refine ⟨s, ?_⟩
  apply moduleHomToPushforward_unit_coefficient_reflects φ M N f U
    (moduleRestrictFrameOverIso M U e) d y hy
  rw [← moduleHomToPushforward_global_restrict φ M N f U s, hst]
  exact ht

end MixedFujita
