/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltPairs

/-! The actual relative canonical divisor is effective: its local
equation on every pair of etale charts is the image of the determinant
of the actual stalk Jacobian, hence is regular. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem relativeCanonicalDivisor_isEffective (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (cT₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ cT₀)) :
    (relativeCanonicalDivisor n ρ c₀ hX cT₀ hT hR).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro t
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K X n, ρ t ∈ c.U :=
    Opens.mem_iSup.mp (hX.symm ▸ Opens.mem_top (ρ t))
  obtain ⟨cT, hcT⟩ : ∃ cT : EtaleChart K T n, t ∈ cT.U :=
    Opens.mem_iSup.mp (hT.symm ▸ Opens.mem_top t)
  exact ⟨(isUnit_chartRelativeJacobianDet ρ c₀ cT₀ hR c cT).unit,
    relativeCanonicalDivisor_isLocalEquationAt ρ c₀ hX cT₀ hT hR t c hc cT hcT,
    relativeCanonicalDivisor_localEquation_mem_stalk ρ c₀ cT₀ hR t c hc cT hcT⟩

theorem birationalRelativeCanonicalDivisor_isEffective
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (cT₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    (birationalRelativeCanonicalDivisor n ρ hρ c₀ hX cT₀ hT).IsEffective :=
  relativeCanonicalDivisor_isEffective ρ c₀ hX cT₀ hT
    (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ cT₀)

end MixedFujita
