/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltNonproperBirationalTests
public import MixedFujita.EtalePolynomialDifferentials

/-!
Construct an actual reference etale chart on an integral open subscheme from
one on the original scheme. First restrict the original chart to a basic open
inside the immersion's range, then transport its coordinates through the actual
isomorphism on regular functions. No chart on the restriction is an input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]

/-- The actual map on regular functions over a dominant K-morphism is K-linear. -/
noncomputable def dominantSectionsAlgHom (W : X.Opens) [Nonempty W]
    [Nonempty (j ⁻¹ᵁ W)] : Γ(X, W) →ₐ[K] Γ(Z, j ⁻¹ᵁ W) where
  toRingHom := (j.app W).hom
  commutes' k := by
    apply Z.germToFunctionField_injective (j ⁻¹ᵁ W)
    have hg := dominantFunctionFieldMap_germ j W (j ⁻¹ᵁ W) le_rfl
      (algebraMap K Γ(X, W) k)
    rw [Scheme.Hom.appLE_eq_app] at hg
    refine hg.symm.trans ?_
    change dominantFunctionFieldAlgHom (K := K) j
      (sectionGermAlgHom (K := K) W (algebraMap K Γ(X, W) k)) =
        sectionGermAlgHom (K := K) (j ⁻¹ᵁ W) (algebraMap K Γ(Z, j ⁻¹ᵁ W) k)
    simp only [AlgHom.commutes]

variable [IsOpenImmersion j]

/-- Transport a chart wholly inside the range of an open immersion. -/
noncomputable def etaleChartPullbackToOpenImmersion (c : EtaleChart K X n)
    (hc : c.U ≤ j.opensRange) : EtaleChart K Z n := by
  letI : Nonempty (j ⁻¹ᵁ c.U) := dominant_preimage_nonempty j c.U
  have himage : j ''ᵁ (j ⁻¹ᵁ c.U) = c.U :=
    Opens.ext (Set.image_preimage_eq_of_subset hc)
  have hAff : IsAffineOpen (j ⁻¹ᵁ c.U) :=
    (j.isAffineOpen_iff_of_isOpenImmersion).mp (himage.symm ▸ c.isAffine)
  letI : IsIso (j.app c.U) := j.isIso_app c.U hc
  refine ⟨j ⁻¹ᵁ c.U, hAff, inferInstance,
    (dominantSectionsAlgHom j c.U).comp c.coords, ?_⟩
  exact RingHom.FormallyEtale.comp c.formallyEtale
    (ringHom_formallyEtale_of_etale (j.app c.U).hom
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (j.app c.U))))

include j

/-- A chart through an image point gives an actual chart through the original point. -/
theorem exists_etaleChart_mem_on_open_immersion (z : Z) (c : EtaleChart K X n)
    (hz : j z ∈ c.U) : ∃ cZ : EtaleChart K Z n, z ∈ cZ.U := by
  have hzj : j z ∈ j.opensRange := ⟨z, rfl⟩
  obtain ⟨a, ha, hza⟩ := c.isAffine.exists_basicOpen_le ⟨j z, hzj⟩ hz
  exact ⟨etaleChartPullbackToOpenImmersion j
    (etaleChartBasicOpen c a ⟨⟨j z, hza⟩⟩) ha, hza⟩

/-- Every integral open subscheme inherits an actual reference chart of the same dimension. -/
theorem exists_etaleChart_on_integral_open_immersion (c : EtaleChart K X n) :
    Nonempty (EtaleChart K Z n) := by
  have hηc : genericPoint X ∈ c.U :=
    ((genericPoint_spec X).mem_open_set_iff c.U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty c.U))
  have hηj : genericPoint X ∈ j.opensRange :=
    ⟨genericPoint Z, dominant_map_genericPoint j⟩
  obtain ⟨a, ha, hηa⟩ := c.isAffine.exists_basicOpen_le ⟨genericPoint X, hηj⟩ hηc
  exact ⟨etaleChartPullbackToOpenImmersion j
    (etaleChartBasicOpen c a ⟨⟨genericPoint X, hηa⟩⟩) ha⟩

end MixedFujita
