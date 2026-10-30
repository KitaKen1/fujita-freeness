/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleOpenFrameGerms
public import MixedFujita.CartierSGALineBundle
public import MixedFujita.CartierGlobalGenerationOperations

/-! 非被約源にも使える実加群大域生成と元Cartier大域生成の同値。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Global generation of an actual module on an arbitrary scheme, witnessed
by a local frame and an actual global section with unit coefficient. -/
def moduleIsGloballyGenerated {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (hx : x ∈ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (s : Γ(M, ⊤)),
      IsUnit (moduleOverFrameGlobalCoefficientGerm M U e x hx s)


/-- The local frame in the usual generation condition can be chosen arbitrarily. -/
theorem moduleIsGloballyGenerated_at_frame {X : Scheme.{u}} {M : X.Modules}
    (hM : moduleIsGloballyGenerated M) (x : X) (U : X.Opens) (hx : x ∈ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ s : Γ(M, ⊤), IsUnit (moduleOverFrameGlobalCoefficientGerm M U e x hx s) := by
  obtain ⟨V, hxV, d, s, hs⟩ := hM x
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  let eW := moduleOverFrameRestrictIso M U e W inf_le_left
  let dW := moduleOverFrameRestrictIso M V d W inf_le_right
  have hdW : IsUnit (moduleOverFrameGlobalCoefficientGerm M W dW x hxW s) := by
    simpa only [dW, moduleOverFrameGlobalCoefficientGerm_restrict] using hs
  obtain ⟨v, hv⟩ := moduleOverFrameGlobalCoefficientGerm_change_frame M W eW dW x hxW
  have heW : IsUnit (moduleOverFrameGlobalCoefficientGerm M W eW x hxW s) := by
    rw [hv s]
    exact v.isUnit.mul hdW
  exact ⟨s, by simpa only [eW, moduleOverFrameGlobalCoefficientGerm_restrict] using heW⟩


/-- Actual module isomorphisms transport actual generating global sections. -/
theorem moduleIsGloballyGenerated_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (a : M ≅ N) (hM : moduleIsGloballyGenerated M) : moduleIsGloballyGenerated N := by
  intro x
  obtain ⟨U, hx, e, s, hs⟩ := hM x
  refine ⟨U, hx, moduleOverFrameViaIso U a e, Scheme.Modules.Hom.app a.hom ⊤ s, ?_⟩
  rwa [moduleOverFrameGlobalCoefficientGerm_viaIso]


/-- For genuine Cartier sheaves the arbitrary-scheme module condition is
exactly the original manuscript's global generation condition. -/
theorem cartierIsGloballyGenerated_iff_module {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) : CartierIsGloballyGenerated D ↔ moduleIsGloballyGenerated D.sheaf := by
  constructor
  · intro h x
    let C := cartierEquationOpenCover D
    let : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
    obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp h x
      (C.equation x) (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (C.equation_eq x) (C.mem x))
    refine ⟨C.U x, C.mem x, cartierOpenFrameIso D (C.U x) (C.equation x) (C.equation_eq x), s, ?_⟩
    rwa [moduleOverFrameGlobalCoefficientGerm_cartier]
  · intro h x
    let C := cartierEquationOpenCover D
    let : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
    obtain ⟨s, hs⟩ := moduleIsGloballyGenerated_at_frame h x (C.U x) (C.mem x)
      (cartierOpenFrameIso D (C.U x) (C.equation x) (C.equation_eq x))
    rw [moduleOverFrameGlobalCoefficientGerm_cartier] at hs
    obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x
      (Classical.choose (D.exists_isLocalEquationAt x)) (C.equation x)
      (Classical.choose_spec (D.exists_isLocalEquationAt x))
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (C.equation_eq x) (C.mem x))
    exact ⟨s, by rw [hv s]; exact v.isUnit.mul hs⟩

end MixedFujita
