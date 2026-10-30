/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RestrictedDimUpperBounds
public import MixedFujita.ProperBirationalSections
public import MixedFujita.NormalCartierSectionLifting

/-!
Division of sections by a reduced section, on a normal scheme (a piece of Kodaira's lemma;
step 17).

Let X be a normal locally Noetherian integral scheme. A nonzero section f of O(D) vanishing at a
codimension-one point z has ord_z(f) + D_z ≥ 1 (`one_le_ord_add_coefficient_of_mem_vanishingAt`:
the local coefficient is a nonzero element of the maximal ideal of the discrete valuation ring at
z, so its order is not zero). Let s be a nonzero section of O(J) whose zero divisor has coefficient
at most one at the points η_i and at most zero at the other codimension-one points. If f vanishes at
every η_i, the rational function f / s has order at least minus the coefficient of D − J at every
codimension-one point, so it is a section of O(D − J) by Hartogs. Hence the sections of O(D)
vanishing at all η_i have at most the dimension of the sections of O(D − J)
(`finrank_iInf_vanishingAt_le_finrank_sub`). With the codimension count of
`RestrictedDimUpperBounds` this gives h⁰(D − J) ≥ h⁰(D) − Σ_i (dimension of the sections of D
restricted at η_i) (`finrank_le_finrank_sub_add_sum_cartierRestrictedDim`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra functionFieldBaseScalarTower

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [X.Over (Spec (CommRingCat.of K))]

/-- A nonzero section of O(D) vanishing at a codimension-one point z of a normal scheme has
ord_z(f) + D_z ≥ 1. -/
theorem one_le_ord_add_coefficient_of_mem_vanishingAt
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D : CartierDivisor X)
    (z : CodimensionOnePoint X) (f : Γ(D.sheaf, ⊤)) (hf0 : f ≠ 0)
    (hf : f ∈ cartierSectionsVanishingAt K D (z : X)) :
    1 ≤ X.ord (cartierSectionRational D f) (z : X) + cartierCoefficient D (z : X) := by
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt (z : X)
  have hmem := (mem_cartierSectionsVanishingAt_iff D (z : X) g hg f).mp hf
  have hc0 : cartierLocalCoefficient D (z : X) g hg f ≠ 0 :=
    (cartierLocalCoefficient_ne_zero_iff D (z : X) g hg f).mpr hf0
  have hrat0 : cartierSectionRational D f ≠ 0 := fun h =>
    hf0 (cartierSectionRational_injective D (h.trans (map_zero _).symm))
  have hord : X.ord (algebraMap (X.presheaf.stalk (z : X)) X.functionField
      (cartierLocalCoefficient D (z : X) g hg f)) (z : X) =
        cartierCoefficient D (z : X) + X.ord (cartierSectionRational D f) (z : X) := by
    rw [cartierLocalCoefficient_image, X.ord_mul (Units.ne_zero g) hrat0,
      ← cartierCoefficient_eq_ord hg]
  have hnn : 0 ≤ X.ord (algebraMap (X.presheaf.stalk (z : X)) X.functionField
      (cartierLocalCoefficient D (z : X) g hg f)) (z : X) :=
    scheme_ord_nonneg_of_mem_stalk _ _ ⟨_, rfl⟩
  have hne : X.ord (algebraMap (X.presheaf.stalk (z : X)) X.functionField
      (cartierLocalCoefficient D (z : X) g hg f)) (z : X) ≠ 0 := by
    intro h0
    have := hnorm (z : X)
    have : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := normal_codimensionOne_stalk_DVR z
    have hcK : algebraMap (X.presheaf.stalk (z : X)) X.functionField
        (cartierLocalCoefficient D (z : X) g hg f) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hc0
    obtain ⟨v, hv⟩ := scheme_ord_zero_exists_stalk_unit z (Units.mk0 _ hcK) h0
    have hveq : (v : X.presheaf.stalk (z : X)) = cartierLocalCoefficient D (z : X) g hg f :=
      IsFractionRing.injective _ X.functionField hv
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) (hveq ▸ v.isUnit)
  omega

/-- Division by a section whose zero divisor has coefficient at most one at the points η_i and
zero at the other codimension-one points: on a normal scheme the sections of O(D) vanishing at
every η_i have at most the dimension of the sections of O(D − J). -/
theorem finrank_iInf_vanishingAt_le_finrank_sub
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D J : CartierDivisor X)
    (s : Γ(J.sheaf, ⊤)) (hs : s ≠ 0) {ι : Type*} (η : ι → CodimensionOnePoint X)
    (hcoef₁ : ∀ i, cartierCoefficient (cartierSectionZeroDivisor J s hs) (η i : X) ≤ 1)
    (hcoef₀ : ∀ z : CodimensionOnePoint X, z ∉ Set.range η →
      cartierCoefficient (cartierSectionZeroDivisor J s hs) (z : X) ≤ 0)
    [FiniteDimensional K Γ((D - J).sheaf, ⊤)] :
    Module.finrank K (⨅ i, cartierSectionsVanishingAt K D (η i : X) :
      Submodule K Γ(D.sheaf, ⊤)) ≤ Module.finrank K Γ((D - J).sheaf, ⊤) := by
  classical
  set S := (⨅ i, cartierSectionsVanishingAt K D (η i : X) : Submodule K Γ(D.sheaf, ⊤)) with hS
  have hu0 : cartierSectionRational J s ≠ 0 := Units.ne_zero (cartierSectionUnit J s hs)
  let ψ : Γ(D.sheaf, ⊤) →ₗ[K] X.functionField :=
    LinearMap.mulRight K (cartierSectionRational J s)⁻¹ ∘ₗ
      (cartierSectionRational D).restrictScalars K
  have hψ : ∀ f : Γ(D.sheaf, ⊤),
      ψ f = cartierSectionRational D f * (cartierSectionRational J s)⁻¹ :=
    fun f => rfl
  have hmem : ∀ f ∈ S, ψ f ∈ cartierSectionSpace K (D - J) := by
    intro f hfS
    rw [hψ, mem_cartierSectionSpace_iff]
    by_cases hf0 : f = 0
    · rw [hf0, map_zero, zero_mul, map_zero]
      exact zero_mem _
    have hrat0 : cartierSectionRational D f ≠ 0 := fun h =>
      hf0 (cartierSectionRational_injective D (h.trans (map_zero _).symm))
    apply cartier_mem_sections_of_forall_ord hnorm (D - J) ⊤
    intro z _
    have hD : 0 ≤ X.ord (cartierSectionRational D f) (z : X) + cartierCoefficient D (z : X) :=
      cartier_ord_add_coefficient_nonneg_of_mem_sections D ⊤ _
        ((mem_cartierSectionSpace_iff (K := K) D _).mp ⟨f, rfl⟩) hrat0 (z : X) trivial
    have hZ : cartierCoefficient (cartierSectionZeroDivisor J s hs) (z : X) =
        cartierCoefficient J (z : X) + X.ord (cartierSectionRational J s) (z : X) := by
      rw [cartierSectionZeroDivisor, cartierCoefficient_add, cartierCoefficient_principal,
        cartierSectionUnit_val]
    rw [X.ord_mul hrat0 (inv_ne_zero hu0), Scheme.ord_inv, cartierCoefficient_sub]
    by_cases hz : z ∈ Set.range η
    · obtain ⟨i, rfl⟩ := hz
      have h1 := one_le_ord_add_coefficient_of_mem_vanishingAt hnorm D (η i) f hf0
        ((Submodule.mem_iInf _).mp hfS i)
      have hcz := hcoef₁ i
      omega
    · have hcz := hcoef₀ z hz
      omega
  let φ : S →ₗ[K] cartierSectionSpace K (D - J) :=
    (ψ.domRestrict S).codRestrict _ fun f => hmem f f.2
  have hinj : Function.Injective φ := by
    intro f₁ f₂ h
    have h' : ψ f₁ = ψ f₂ := congrArg Subtype.val h
    rw [hψ, hψ] at h'
    have h'' := mul_right_cancel₀ (inv_ne_zero hu0) h'
    exact Subtype.ext (cartierSectionRational_injective D h'')
  have : FiniteDimensional K (cartierSectionSpace K (D - J)) := by
    unfold cartierSectionSpace; infer_instance
  calc Module.finrank K S ≤ Module.finrank K (cartierSectionSpace K (D - J)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank K Γ((D - J).sheaf, ⊤) := finrank_cartierSectionSpace K (D - J)

/-- The counting step of Kodaira's lemma: with s as above and finitely many points η_i,
h⁰(D) ≤ h⁰(D − J) + Σ_i (dimension of the sections of D restricted at η_i). -/
theorem finrank_le_finrank_sub_add_sum_cartierRestrictedDim
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D J : CartierDivisor X)
    (s : Γ(J.sheaf, ⊤)) (hs : s ≠ 0) {ι : Type*} [Fintype ι] (η : ι → CodimensionOnePoint X)
    (hcoef₁ : ∀ i, cartierCoefficient (cartierSectionZeroDivisor J s hs) (η i : X) ≤ 1)
    (hcoef₀ : ∀ z : CodimensionOnePoint X, z ∉ Set.range η →
      cartierCoefficient (cartierSectionZeroDivisor J s hs) (z : X) ≤ 0)
    [FiniteDimensional K Γ(D.sheaf, ⊤)] [FiniteDimensional K Γ((D - J).sheaf, ⊤)] :
    Module.finrank K Γ(D.sheaf, ⊤) ≤
      Module.finrank K Γ((D - J).sheaf, ⊤) + ∑ i, cartierRestrictedDim K D (η i : X) :=
  (finrank_le_finrank_iInf_add_sum_cartierRestrictedDim K D fun i => (η i : X)).trans
    (Nat.add_le_add_right
      (finrank_iInf_vanishingAt_le_finrank_sub hnorm D J s hs η hcoef₁ hcoef₀) _)

end MixedFujita
