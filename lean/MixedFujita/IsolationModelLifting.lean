/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FloorDivisorLifting
public import MixedFujita.IsolationRationalData
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.BirationalComposition
public import MixedFujita.CrepantBoundaryPerturbation

/-!
The lifting of section 6.3 of the manuscript on the isolation model (step 12).

Let π : X → V be a proper birational morphism from a smooth variety X to a normal scheme V (a
simple normal crossing model of the pair), B the boundary on X, effective at the prime divisors of
X which are not exceptional over V, and ρ : T → X the isolation model of sections 6.1 and 6.2,
with its prime divisors ξ_k, their member divisors E_k, the effective divisor G and

  Ψ = (1 − η) Σ_i c_i ρ*D_i + (η/M) G,   Γ = B_T + Ψ,

where B_T is the crepant boundary of T. The set S of sections 6.1 and 6.2 consists of members over
a closed point x of V on which Ψ equals the log discrepancy, every other prime divisor meeting S
having Ψ smaller than its log discrepancy. Then Γ has coefficient one on S, coefficient smaller
than one on the other members meeting S, and nonnegative coefficient on the members which are not
exceptional over V. Hence, if H¹(T, O(ρ*π*P − ⌊Γ⌋)) = 0, the Cartier divisor P of V has a global
section generating it at x.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

section Gamma

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]

/-- The coefficient at t of the real divisor Γ = B_T + Ψ of section 6.3: B_T = BT/d is the crepant
boundary and Ψ = (1 − η) Σ_i c_i D'_i + (η/M) G. -/
noncomputable def isolationGammaCoefficient {N : ℕ} (d : ℕ) (BT : CartierDivisor T)
    (D' : Fin N → CartierDivisor T) (c : Fin N → ℝ) (η M : ℝ) (G : CartierDivisor T) (t : T) : ℝ :=
  (cartierCoefficient BT t : ℝ) / d +
    ((1 - η) * ∑ i, c i * (cartierCoefficient (D' i) t : ℝ) + η / M * (cartierCoefficient G t : ℝ))

end Gamma

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- At a prime divisor of T which is not exceptional over X the crepant boundary has the
coefficient of the boundary of X at its image. -/
theorem crepantBoundaryCartier_coefficient_of_coheight_eq_one (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X) (cT : EtaleChart K T n)
    (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
    cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT etaleCharts_cover)
      (t : T) = cartierCoefficient B (ρ (t : T)) := by
  have hb := stalkMap_bijective_of_birational_over_smooth_prime (n := n) ρ hρ (t : T) ht
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let ξ : CodimensionOnePoint X := ⟨ρ (t : T), ht⟩
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) ξ
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  obtain ⟨e, he⟩ : ∃ e : EtaleChart K X n, ρ (t : T) ∈ e.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸
      Opens.mem_top (ρ (t : T)))
  obtain ⟨e', he'⟩ : ∃ e' : EtaleChart K T n, (t : T) ∈ e'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (t : T))
  rw [crepantBoundaryCartier_eq_neg_discrepancy, logDiscrepancyDivisor_boundary_add, neg_sub,
    cartierCoefficient_sub, cartierCoefficient_nsmul,
    birationalRelativeCanonicalDivisor_coefficient_zero_of_stalkMap_bijective ρ hρ c₀
      etaleCharts_cover cT etaleCharts_cover t hb e he e' he', mul_zero, sub_zero]
  exact cartierCoefficient_pullback_of_stalkMap_bijective ρ t ht hb B

variable {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsProper ρ]

/-- The lifting of section 6.3 on the isolation model. Let π : X → V be proper birational from the
smooth X to the normal V, ρ : T → X an isolation model with prime divisors ξ_k and member divisors
E_k, and S a nonempty set of indices whose members lie over the closed point x of V, with Ψ equal
to the log discrepancy on S and, for every prime divisor meeting S, Ψ at most the log discrepancy
with equality only for the members of S. If the boundary B of X is effective at the prime divisors
not exceptional over V and H¹(T, O(ρ*π*P − Σ ⌊Γ_k⌋ E_k)) = 0, the Cartier divisor P of V has a
global section generating it at x. -/
theorem isolation_model_exists_section_generating
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1) (E : Fin r' → CartierDivisor T)
    (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective) (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i)
    (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (S : Set (Fin r')) (hS : S.Nonempty)
    (hSx : ∀ k ∈ S, π (ρ (ξT k)) = x)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (hvan : Subsingleton (Scheme.Modules.Cohomology
      (cartierPullback ρ (cartierPullback π P) -
        ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
          etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k).sheaf
      1)) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u = f * g := by
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  have hρ' : Function.Bijective (dominantFunctionFieldMap ρ).hom := hρ
  have hτ : Function.Bijective (dominantFunctionFieldMap (ρ ≫ π)).hom := by
    rw [dominantFunctionFieldMap_comp π ρ]
    exact hρ'.comp hπ
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  -- Γ = 1 − (log discrepancy) + Ψ
  have hΓ : ∀ t : T, isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT etaleCharts_cover)
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc t =
      1 - ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) t) / d +
        ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) t : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc t : ℝ)) := by
    intro t
    unfold isolationGammaCoefficient
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, Int.cast_neg]
    field_simp
    ring
  refine exists_section_generating_of_floor_vanishing hnormV hnormT (ρ ≫ π) hτ P ξT hinjT hξT E
    hE hEc _ S hS x hx hSx ?_ ?_ ?_ (by rw [cartierPullback_comp π ρ P]; exact hvan)
  · intro k hk
    rw [hΓ (ξT k), hSeq k hk]
    ring
  · intro k hk hex
    obtain ⟨hle, heq⟩ := hSmeet ⟨ξT k, hξT k⟩ hex
    have hlt := lt_of_le_of_ne hle fun h => by
      obtain ⟨k', hk', hkk'⟩ := heq h
      have hkk : k = k' := hinjT hkk'
      exact hk (hkk ▸ hk')
    rw [hΓ (ξT k)]
    linarith
  · intro k hcoh
    have hcoh' : Order.coheight (π (ρ (ξT k))) = 1 := hcoh
    have hbπ := stalkMap_bijective_of_birational_over_normal_prime hnormV π hπ (ρ (ξT k)) hcoh'
    have hcohX : Order.coheight (ρ (ξT k)) = 1 :=
      (coheight_eq_of_stalkMap_bijective π (ρ (ξT k)) hbπ).trans hcoh'
    have hBT := crepantBoundaryCartier_coefficient_of_coheight_eq_one ρ hρ c₀ f₀ d B cT
      ⟨ξT k, hξT k⟩ hcohX
    have hB0 : (0 : ℝ) ≤ (cartierCoefficient B (ρ (ξT k)) : ℝ) := by
      exact_mod_cast hBexc ⟨ρ (ξT k), hcohX⟩ hcoh'
    have hD0 : ∀ i, (0 : ℝ) ≤ (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) :=
      fun i => by
        exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
          (cartierPullback_isEffective ρ (Dv i) (hDeff i)) (ξT k)
    have hG0 : (0 : ℝ) ≤ (cartierCoefficient Gc (ξT k) : ℝ) := by
      exact_mod_cast cartierCoefficient_nonneg_of_isEffective Gc hGc (ξT k)
    unfold isolationGammaCoefficient
    rw [hBT]
    have h1 : (0 : ℝ) ≤ (cartierCoefficient B (ρ (ξT k)) : ℝ) / d := div_nonneg hB0 hdpos.le
    have h2 : (0 : ℝ) ≤ (1 - η) * ∑ i, c₁ i *
        (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) :=
      mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => mul_nonneg (hc₁ i) (hD0 i))
    have h3 : (0 : ℝ) ≤ η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) :=
      mul_nonneg (div_nonneg hη0 (Nat.cast_nonneg Mn)) hG0
    linarith

end Model

end MixedFujita
