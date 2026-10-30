/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupLocalBaseChange
public import MixedFujita.SNCWeightLowSubspace

/-! An exact order of a section germ, with the source point identified
by an equality, is the actual coefficient of the pulled-back zero divisor
at a DVR prime. This transports the constructed point-blow-up order data
to the coefficient interface used by section-base principalization. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]

theorem cartierPullback_sectionZeroDivisor_coefficient_of_mappedPoint_order
    (π : Y ⟶ X) [IsDominant π] (q : CodimensionOnePoint Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk (q : Y))]
    (x : X) (hqx : π (q : Y) = x) (D : CartierDivisor X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (m : ℕ)
    (horder : localAdicOrder (Y.presheaf.stalk (q : Y))
      (stalkMapAtEq π (q : Y) x hqx (cartierLocalCoefficient D x f hf s)) = (m : ℕ∞)) :
    cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (q : Y) = (m : ℤ) := by
  subst x
  obtain ⟨k, hk, hcoef⟩ := cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder
    π D s hs q
  have hm : cartierStalkPullbackOrder D π (q : Y) s = (m : ℕ∞) := by
    rw [cartierStalkPullbackOrder_eq_localCoefficient D π (q : Y) f hf]
    exact horder
  have hkm : k = m := ENat.natCast_inj.mp (hk.symm.trans hm)
  simpa only [hkm] using hcoef

end MixedFujita
