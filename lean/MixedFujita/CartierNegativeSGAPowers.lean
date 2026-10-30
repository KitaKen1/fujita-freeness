/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACartierTwistPowers
public import MixedFujita.CartierPulledCoherentTwist
public import MixedFujita.SGATwistPullbackIso

/-! 同じ元Cartier負冪と非被約引き戻しの実SGA辞書。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Actual negative SGA powers are represented by the negative multiple
of the SAME original Cartier divisor, via two actual tensor cancellations. -/
noncomputable def cartierSGANegativeNatPowerIso
    {X : Scheme.{u}} [IsIntegral X] (H : CartierDivisor X) (j : ℕ) :
    (cartierSGALineBundle H).toModules (-(j : ℤ)) ≅ (-(j • H)).sheaf := by
  let L := cartierSGALineBundle H
  let A := L.toModules (-(j : ℤ))
  let B := L.toModules (j : ℤ)
  let C := (-(j • H)).sheaf
  let a : A ⊗ B ≅ CohomologyAux.unitModule X :=
    sgaLineBundleTensorPowerIso L (-(j : ℤ)) j ≪≫
      eqToIso (congrArg L.toModules (neg_add_cancel (j : ℤ))) ≪≫ sgaLineBundleZeroPowerIso L
  let b : B ⊗ C ≅ CohomologyAux.unitModule X :=
    tensorIso (cartierSGANatPowerIso H j) (Iso.refl C) ≪≫
      cartierTensorSheafIso (j • H) (-(j • H)) ≪≫
        eqToIso (congrArg CartierDivisor.sheaf (add_neg_cancel (j • H))) ≪≫ cartierZeroSheafIso X
  exact (ρ_ A).symm ≪≫ tensorIso (Iso.refl A) b.symm ≪≫ (α_ A B C).symm ≪≫
    tensorIso a (Iso.refl C) ≪≫ λ_ C


/-- The original pulled Cartier difference is the actual negative SGA
twist on any source, including a nonreduced Cartier cut. -/
noncomputable def cartierPulledNegativeSGATwistIso
    {X Y : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) (E H : CartierDivisor X) (j : ℕ) :
    (Scheme.Modules.pullback p).obj (E - j • H).sheaf ≅
      ((cartierSGALineBundle H).pullback p).twist
        (((cartierSGALineBundle E).pullback p).toModules 1) (-(j : ℤ)) := by
  let L := (cartierSGALineBundle H).pullback p
  let F := (cartierSGALineBundle E).pullback p
  let b : (Scheme.Modules.pullback p).obj (-(j • H)).sheaf ≅ L.toModules (-(j : ℤ)) :=
    (Scheme.Modules.pullback p).mapIso (cartierSGANegativeNatPowerIso H j).symm ≪≫
      sgaLineBundlePullbackPowerIso (cartierSGALineBundle H) p (-(j : ℤ))
  exact (Scheme.Modules.pullback p).mapIso
      (eqToIso (congrArg CartierDivisor.sheaf (sub_eq_add_neg E (j • H))) ≪≫
        (cartierTensorSheafIso E (-(j • H))).symm) ≪≫
    cartierPullbackTensorIso E p (-(j • H)).sheaf ≪≫
      tensorIso (cartierPulledSheafSGAPowerOneIso E p).symm b ≪≫
        β_ (F.toModules 1) (L.toModules (-(j : ℤ))) ≪≫ sgaTwistTensorIso L (F.toModules 1) (-(j : ℤ))

end MixedFujita
