/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACartierTwistPowers
public import MixedFujita.SGATwistPullbackIso

/-! 非被約源上の次数1同型から全直線束冪と実固定捻り同型。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Actual degree-one line-bundle isomorphisms determine EVERY natural
power, even on a nonreduced scheme. No Cartier representative is needed there. -/
noncomputable def sgaLineBundleNatPowerIsoOfIso
    {Y : Scheme.{u}} (L M : Y.LineBundle) (a : L.toModules 1 ≅ M.toModules 1) :
    ∀ j : ℕ, L.toModules (j : ℤ) ≅ M.toModules (j : ℤ)
  | 0 => sgaLineBundleZeroPowerIso L ≪≫ (sgaLineBundleZeroPowerIso M).symm
  | j + 1 =>
    eqToIso (congrArg L.toModules (show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega)) ≪≫
      (sgaLineBundleTensorPowerIso L j 1).symm ≪≫
      tensorIso (sgaLineBundleNatPowerIsoOfIso L M a j) a ≪≫
      sgaLineBundleTensorPowerIso M j 1 ≪≫
      eqToIso (congrArg M.toModules (show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega))


/-- One actual hyperplane isomorphism for a pulled Cartier bundle gives
all pulled affine powers, with an arbitrary fixed Cartier twist. -/
noncomputable def cartierPulledSGAAffinePowerIso
    {X Y : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X)
    (H E : CartierDivisor X) (M : Y.LineBundle)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ M.toModules 1) (j : ℕ) :
    (Scheme.Modules.pullback p).obj (E + j • H).sheaf ≅
      M.twist ((Scheme.Modules.pullback p).obj E.sheaf) (j : ℤ) := by
  let L := (cartierSGALineBundle H).pullback p
  let b : L.toModules 1 ≅ M.toModules 1 :=
    (sgaLineBundlePullbackPowerIso (cartierSGALineBundle H) p 1).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (cartierSGAModuleIso H).symm ≪≫ a
  let c : (Scheme.Modules.pullback p).obj (j • H).sheaf ≅ M.toModules (j : ℤ) :=
    (Scheme.Modules.pullback p).mapIso (cartierSGANatPowerIso H j).symm ≪≫
      sgaLineBundlePullbackPowerIso (cartierSGALineBundle H) p j ≪≫
      sgaLineBundleNatPowerIsoOfIso L M b j
  exact (Scheme.Modules.pullback p).mapIso
      (eqToIso (congrArg CartierDivisor.sheaf (add_comm E (j • H))) ≪≫
        (cartierTensorSheafIso (j • H) E).symm) ≪≫
    cartierPullbackTensorIso (j • H) p E.sheaf ≪≫ tensorIso c (Iso.refl _) ≪≫
      sgaTwistTensorIso M ((Scheme.Modules.pullback p).obj E.sheaf) j

end MixedFujita
