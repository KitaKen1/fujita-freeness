/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleGlobalGeneration

/-! 任意の実順像写像の局所係数公式と局所単元の反映。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Every map into an actual pushforward is, in local rank-one frames,
multiplication by the pulled source coefficient and one fixed image. -/
theorem moduleHomToPushforward_frame_coefficient {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over (φ ⁻¹ᵁ U) ≅ SheafOfModules.unit (Y.ringCatSheaf.over (φ ⁻¹ᵁ U)))
    (s : Γ(M, U)) :
    moduleOverFrameCoefficient N (φ ⁻¹ᵁ U) d (φ ⁻¹ᵁ U) le_rfl (Scheme.Modules.Hom.app f U s) =
      φ.app U (moduleOverFrameCoefficient M U e U le_rfl s) *
        moduleOverFrameCoefficient N (φ ⁻¹ᵁ U) d (φ ⁻¹ᵁ U) le_rfl
          (Scheme.Modules.Hom.app f U ((moduleOverFrameCoefficient M U e U le_rfl).symm 1)) := by
  let c := moduleOverFrameCoefficient M U e U le_rfl
  have hs : s = c s • c.symm 1 := by
    apply c.injective
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [hs, Scheme.Modules.Hom.app_smul]
  change moduleOverFrameCoefficient N (φ ⁻¹ᵁ U) d (φ ⁻¹ᵁ U) le_rfl
      (φ.app U (c s) • (show Γ(N, φ ⁻¹ᵁ U) from Scheme.Modules.Hom.app f U (c.symm 1))) = _
  rw [LinearEquiv.map_smul, smul_eq_mul]


/-- A unit coefficient in the image under any actual pushforward map
forces a unit source coefficient, by localness of the actual stalk map. -/
theorem moduleHomToPushforward_unit_coefficient_reflects {X Y : Scheme.{u}}
    (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over (φ ⁻¹ᵁ U) ≅ SheafOfModules.unit (Y.ringCatSheaf.over (φ ⁻¹ᵁ U)))
    (y : Y) (hy : φ y ∈ U) (s : Γ(M, U))
    (hs : IsUnit (Y.presheaf.germ (φ ⁻¹ᵁ U) y hy
      (moduleOverFrameCoefficient N (φ ⁻¹ᵁ U) d (φ ⁻¹ᵁ U) le_rfl (Scheme.Modules.Hom.app f U s)))) :
    IsUnit (X.presheaf.germ U (φ y) hy (moduleOverFrameCoefficient M U e U le_rfl s)) := by
  rw [moduleHomToPushforward_frame_coefficient φ M N f U e d s, map_mul] at hs
  apply isUnit_of_map_unit (φ.stalkMap y).hom
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact isUnit_of_mul_isUnit_left hs

end MixedFujita
