/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HartogsSectionDivision
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.SmoothClosedPoints

/-!
Further pieces of Kodaira's lemma (step 17).

* The closure of a codimension-one point of an integral scheme of dimension n has dimension a
  natural number d with d + 1 ≤ n (`exists_topologicalKrullDim_closure_eq_of_coheight_eq_one`):
  a chain of irreducible closed subsets of a proper closed subset S of an irreducible space maps
  to a chain in the space that can be extended by the whole space
  (`topologicalKrullDim_le_pred_of_isClosed_ne_univ`). With
  `projectiveHyperplane_exists_cartierRestrictedDim_le_mul_pow` this bounds the restricted
  dimensions at the components of a hyperplane section by C (q + 1)^(n − 1) when n ≥ 2.
* At a closed point of a smooth scheme over an algebraically closed field the sections restricted
  at the point have dimension at most one (`cartierRestrictedDim_le_one_of_isClosed`): the
  residue field is K. This is the case n = 1.
* If a nonzero section of O(E) is given and the sections of O(D + E) are finite-dimensional, so
  are those of O(D) (`finiteDimensional_of_section_mul`).
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

section Dimension

/-- A proper closed subset of an irreducible space of dimension n has dimension at most n − 1. -/
theorem topologicalKrullDim_le_pred_of_isClosed_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {n : ℕ} (hn : topologicalKrullDim T = n) {S : Set T}
    (hS : IsClosed S) (hSne : S ≠ Set.univ) :
    topologicalKrullDim S ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  let M := IrreducibleCloseds.map (Subtype.val : S → T) continuous_subtype_val
  have hM : StrictMono M := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let top : IrreducibleCloseds T :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hlt : ∀ Z : IrreducibleCloseds S, M Z < top := by
    intro Z
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun h => hSne ?_
    have hsub : (M Z : Set T) ⊆ S :=
      closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hS
    have hsub' : (top : Set T) ⊆ S := h ▸ hsub
    exact Set.eq_univ_of_univ_subset hsub'
  refine iSup_le fun p => ?_
  have h1 := Order.LTSeries.length_le_krullDim ((p.map M hM).snoc top (hlt _))
  have hlen : ((p.map M hM).snoc top (hlt _)).length = p.length + 1 := rfl
  change _ ≤ topologicalKrullDim T at h1
  rw [hlen, hn] at h1
  have h2 : p.length + 1 ≤ n := by exact_mod_cast h1
  have h3 : p.length ≤ n - 1 := by omega
  exact_mod_cast h3

/-- The closure of a codimension-one point of an integral scheme of dimension n has dimension a
natural number d with d + 1 ≤ n. -/
theorem exists_topologicalKrullDim_closure_eq_of_coheight_eq_one {X : Scheme.{u}} [IsIntegral X]
    {n : ℕ} (hn : topologicalKrullDim X = n) {η : X} (hη : Order.coheight η = 1) :
    ∃ d : ℕ, d + 1 ≤ n ∧
      topologicalKrullDim (closure ({η} : Set X)) = ((d : ℕ) : WithBot ℕ∞) := by
  obtain ⟨D', -, hD'⟩ := exists_nat_topologicalKrullDim_closure_eq hn η
  have hne : closure ({η} : Set X) ≠ Set.univ := fun h =>
    genericPoint_notMem_closure_of_coheight_eq_one hη (h ▸ Set.mem_univ _)
  have hle := topologicalKrullDim_le_pred_of_isClosed_ne_univ hn isClosed_closure hne
  rw [hD'] at hle
  have hD'le : D' ≤ n - 1 := by exact_mod_cast hle
  have hn1 : (1 : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    have := TauCeti.coheight_le_topologicalKrullDim η
    rw [hη, hn] at this
    exact_mod_cast this
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  exact ⟨D', by omega, hD'⟩

end Dimension

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

section ClosedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]

/-- At a closed point of a smooth scheme over an algebraically closed field the sections restricted
at the point have dimension at most one. -/
theorem cartierRestrictedDim_le_one_of_isClosed (D : CartierDivisor X) (x : X)
    (hx : IsClosed ({x} : Set X)) : cartierRestrictedDim K D x ≤ 1 := by
  obtain ⟨e⟩ := smoothScheme_closedPoint_residueField (K := K) x hx
  let c : Γ(D.sheaf, ⊤) →ₗ[K] X.presheaf.stalk x :=
    (cartierLocalCoefficient D x (Classical.choose (D.exists_isLocalEquationAt x))
      (Classical.choose_spec (D.exists_isLocalEquationAt x))).restrictScalars K
  let φ : Γ(D.sheaf, ⊤) →ₗ[K]
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).toLinearMap ∘ₗ c
  have hker : LinearMap.ker φ = cartierSectionsVanishingAt K D x := by
    ext s
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk _ (c s) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Iff.rfl
  have h1 : Module.finrank K
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) = 1 := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]
  have : FiniteDimensional K
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    Module.finite_of_finrank_eq_succ h1
  unfold cartierRestrictedDim
  rw [← hker, (LinearMap.quotKerEquivRange φ).finrank_eq]
  exact (Submodule.finrank_le _).trans h1.le

end ClosedPoint

section Finite

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- Multiplication by a nonzero section of O(E) embeds the sections of O(D) into those of
O(D + E); so they are finite-dimensional when the latter are. -/
theorem finiteDimensional_of_section_mul (D E : CartierDivisor X) (t : Γ(E.sheaf, ⊤))
    (ht : t ≠ 0) [FiniteDimensional K Γ((D + E).sheaf, ⊤)] :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  have hinj : Function.Injective (cartierSectionProductLinear (K := K) D E t) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    rw [LinearMap.mem_ker] at hs
    by_contra h
    exact cartierSectionProduct_ne_zero D E s t h ht hs
  exact Module.Finite.of_injective _ hinj

end Finite

end MixedFujita
