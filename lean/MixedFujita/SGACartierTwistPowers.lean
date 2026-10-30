/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGATwistTensorComparison
public import MixedFujita.CartierGradedPullback
public import MixedFujita.CartierSGAModuleDictionary

/-! The actual SGA powers respect addition of integer exponents. A single actual Cartier representation of degree one yields representations by all natural multiples of that same divisor and identifies every actual Cartier twist D+jH. Applied to the canonical Cartier SGA presentation, this requires no supplied comparison. No ampleness dictionary is asserted here. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
namespace MixedFujita
open TauCeti.AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} (L : X.LineBundle)

noncomputable def sgaLineBundleTensorPowerIso (a b : ℤ) :
    L.toModules a ⊗ L.toModules b ≅ L.toModules (a + b) :=
  sgaTwistTensorIso L (L.toModules b) a ≪≫
    (Scheme.LineBundle.twistFunctor X L a).mapIso (sgaTwistUnitIso L b).symm ≪≫
    L.twistTwistIso (SheafOfModules.unit X.ringCatSheaf) b a ≪≫
    sgaTwistUnitIso L (b + a) ≪≫ eqToIso (congrArg L.toModules (add_comm b a))

noncomputable def sgaLineBundleZeroPowerIso :
    L.toModules 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (sgaTwistUnitIso L 0).symm ≪≫ (L.twistZeroIso (SheafOfModules.unit X.ringCatSheaf)).symm

variable [IsIntegral X]

noncomputable def sgaLineBundleNatPowerCartierIso (H : CartierDivisor X)
    (e : L.toModules 1 ≅ H.sheaf) :
    ∀ j : ℕ, L.toModules (j : ℤ) ≅ (j • H).sheaf
  | 0 => sgaLineBundleZeroPowerIso L ≪≫ (cartierZeroSheafIso X).symm ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (zero_nsmul H).symm)
  | j + 1 =>
    eqToIso (congrArg L.toModules (show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega)) ≪≫
      (sgaLineBundleTensorPowerIso L j 1).symm ≪≫
      tensorIso (sgaLineBundleNatPowerCartierIso H e j) e ≪≫
      (cartierSuccessorTensorSheafIso H j).symm

noncomputable def sgaLineBundleCartierTwistIso (H : CartierDivisor X)
    (e : L.toModules 1 ≅ H.sheaf) (D : CartierDivisor X) (j : ℕ) :
    L.twist D.sheaf (j : ℤ) ≅ (D + j • H).sheaf :=
  (sgaTwistTensorIso L D.sheaf j).symm ≪≫
    tensorIso (sgaLineBundleNatPowerCartierIso L H e j) (Iso.refl D.sheaf) ≪≫
    cartierTensorSheafIso (j • H) D ≪≫
    eqToIso (congrArg CartierDivisor.sheaf (add_comm (j • H) D))

noncomputable def cartierSGANatPowerIso (H : CartierDivisor X) (j : ℕ) :
    (cartierSGALineBundle H).toModules (j : ℤ) ≅ (j • H).sheaf :=
  sgaLineBundleNatPowerCartierIso (cartierSGALineBundle H) H (cartierSGAModuleIso H).symm j

noncomputable def cartierSGATwistIso (H D : CartierDivisor X) (j : ℕ) :
    (cartierSGALineBundle H).twist D.sheaf (j : ℤ) ≅ (D + j • H).sheaf :=
  sgaLineBundleCartierTwistIso (cartierSGALineBundle H) H (cartierSGAModuleIso H).symm D j

end MixedFujita
