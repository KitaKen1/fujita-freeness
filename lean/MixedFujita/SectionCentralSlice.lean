/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StratumCentralSlice
public import MixedFujita.StrongNumericalFreenessStatement
public import MixedFujita.RealWeightedValuation
public import MixedFujita.PointClosureTaylor

/-!
The central slices of the sections of a divisor at a general closed point of the centre of a
weight (section 5.2 of the manuscript: #G_0(h) ≥ I_W(h), here with equality of dimensions).

Let η be the generic point of a component of the stratum of the members of positive weight, z a
point of the chart in the closure of η with Taylor coordinates given by the chart, π a morphism to
Y over K and D a Cartier divisor on Y. The central slice of a section s of D is the Taylor
expansion at z of the pullback of s with the variables of the members of positive weight set to
zero.

* The central slice of s vanishes if and only if s vanishes at π(η).
* Hence the central slices of the sections of D form a space whose dimension is the dimension of
  the sections of D restricted to the closure of π(η).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]

omit [π.IsOver (Spec (CommRingCat.of K))] in
/-- The central slice of a section vanishes if and only if the section vanishes at π(η). -/
theorem cartierPullbackTaylor_central_slice_eq_zero_iff {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) :
    MvPowerSeries.rescale (stratumScale K {a | ∃ k, w k ≠ 0 ∧ σc k = some a})
        (cartierPullbackTaylor D π z ez s) = 0 ↔
      s ∈ cartierSectionsVanishingAt K D (π η) := by
  have hspecY : π η ⤳ π z := π.base.hom.map_specializes hηz
  obtain ⟨f, hf, hT⟩ : ∃ (f : Y.functionFieldˣ) (hf : D.IsLocalEquationAt (π z) f),
      cartierPullbackTaylor D π z ez s =
        stalkTaylorExpansion z ez (π.stalkMap z (cartierLocalCoefficient D (π z) f hf s)) :=
    ⟨_, Classical.choose_spec (D.exists_isLocalEquationAt (π z)), rfl⟩
  have hfη : D.IsLocalEquationAt (π η) f := by
    obtain ⟨V, hzV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    have : Nonempty V := ⟨⟨_, hzV⟩⟩
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV
      (hspecY.mem_open V.isOpen hzV)
  have hcη : Y.presheaf.stalkSpecializes hspecY (cartierLocalCoefficient D (π z) f hf s) =
      cartierLocalCoefficient D (π η) f hfη s := by
    apply IsFractionRing.injective (Y.presheaf.stalk (π η)) Y.functionField
    rw [stalkSpecializes_algebraMap_functionField, cartierLocalCoefficient_image,
      cartierLocalCoefficient_image]
  rw [hT]
  refine (rescale_stratumScale_eq_zero_iff _ _).trans
    ((central_slice_eq_zero_iff π ξ c σc hc w η hη hwη hmax z hz hηz ez hez _).trans ?_)
  rw [hcη]
  exact (mem_cartierSectionsVanishingAt_iff D (π η) f hfη s).symm

/-- The central slices of the sections of D, as a K-linear map. -/
noncomputable def cartierCentralSlice (S : Set (Fin n)) (D : CartierDivisor Y) (z : X)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    Γ(D.sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin n) K :=
  (MvPowerSeries.rescaleAlgHom (stratumScale K S)).toLinearMap.comp
    (cartierPullbackTaylorLinear D π z ez)

/-- The dimension of the central slices of the sections of D is the dimension of the sections of
D restricted to the closure of π(η). -/
theorem finrank_range_cartierCentralSlice {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) :
    Module.finrank K (LinearMap.range
        (cartierCentralSlice π {a | ∃ k, w k ≠ 0 ∧ σc k = some a} D z ez)) =
      cartierRestrictedDim K D (π η) := by
  have hker : LinearMap.ker (cartierCentralSlice π {a | ∃ k, w k ≠ 0 ∧ σc k = some a} D z ez) =
      cartierSectionsVanishingAt K D (π η) := by
    ext s
    rw [LinearMap.mem_ker]
    change MvPowerSeries.rescaleAlgHom (stratumScale K {a | ∃ k, w k ≠ 0 ∧ σc k = some a})
      (cartierPullbackTaylor D π z ez s) = 0 ↔ _
    rw [MvPowerSeries.rescaleAlgHom_apply]
    exact cartierPullbackTaylor_central_slice_eq_zero_iff π ξ c σc hc w η hη hwη hmax z hz hηz
      ez hez D s
  rw [← (LinearMap.quotKerEquivRange
    (cartierCentralSlice π {a | ∃ k, w k ≠ 0 ∧ σc k = some a} D z ez)).finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end MixedFujita
