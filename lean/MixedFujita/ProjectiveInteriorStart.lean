/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorInteriorStart
public import MixedFujita.ProjectiveSubspaceBound
public import MixedFujita.CartierGradedTaylor

/-!
The interior condition (7) at a closed point of an actual smooth integral closed subscheme Y of
dimension d ≥ 1 of polynomial projective space over an algebraically closed field, for the
multiples j J of the hyperplane class. Let r = J^d be the degree, the leading coefficient of
h^0(j J) = r j^d / d! + o(j^d). If (d/(d+1)) r^(1/d) > d/b, then at every closed point x with
completion coordinates in d variables there are t_0 < b, ζ > 0 and δ > 0 such that for all large
j and all t ∈ [t_0, b] some basis of Γ(j J) has F_{j,t}(ζ ord_x, basis) ≤ 1 - δ, where ζ d is the
log discrepancy of ζ ord_x. The inputs are the Hilbert asymptotics, the uniform order bound
ord_x(s) ≤ c j and the equality of the Taylor order with the vanishing order; this is the
starting point of §7 (with L = rA, b = 1/r) and of §8 after (33) (with b = 1), at a smooth point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- (7) at a smooth closed point for the multiples of the hyperplane class: if
(d/(d+1)) (J^d)^(1/d) > d/b, the basis adapted to the total-degree order gives
F_{j,t}(ζ ord_x, basis) ≤ 1 - δ for all large j and all t ∈ [t_0, b]. -/
theorem projectiveHyperplane_interior_start
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      ∀ {b : ℝ}, 0 < b → (d : ℝ) / b < (d : ℝ) / (d + 1) * (r : ℝ) ^ (d : ℝ)⁻¹ →
      ∀ x : Y, IsClosed {x} → ∀ (f : Y.functionFieldˣ)
        (hf : (projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt x f)
        (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
          (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin d) K),
        ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t → t ≤ b →
          ∃ B : Module.Basis (Fin (Module.finrank K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
            minimizationFunctional j t (ζ * d) (fun i => ζ * realWeightedOrder (fun _ => (1 : ℝ))
              (cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coordinates j
                (B i))) ≤ 1 - δ := by
  obtain ⟨r, hr, hfin, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  obtain ⟨c, hc⟩ := projectiveHyperplane_cartierOrder_le e g hg hggen he hn hd
  refine ⟨r, hr, hfin, fun {b} hb hvol x hx f hf coordinates => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) x
  have hfin' : ∀ D : ℕ, FiniteDimensional K
      Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := hfin
  have hd0 : 0 < d := hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hc0 : (0 : ℝ) < (r : ℝ) / d.factorial := div_pos hr0 (by exact_mod_cast d.factorial_pos)
  have hvol' : (d : ℝ) / b <
      (d : ℝ) / (d + 1) * ((d.factorial : ℝ) * ((r : ℝ) / d.factorial)) ^ (d : ℝ)⁻¹ := by
    rwa [mul_div_cancel₀ _ (by exact_mod_cast d.factorial_ne_zero : (d.factorial : ℝ) ≠ 0)]
  set T := cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coordinates
    with hT
  have hTinj : ∀ j, Function.Injective (T j) :=
    cartierGradedTaylor_injective _ x f hf coordinates
  have hord : ∀ᶠ j : ℕ in atTop, ∀ s : Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      s ≠ 0 → realWeightedOrder (fun _ => (1 : ℝ)) (T j s) ≤ (c : ℝ) * j := by
    filter_upwards [eventually_ge_atTop 1] with j hj s hs
    have hT0 : T j s ≠ 0 := fun h => hs (hTinj j (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin d => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    have heq : (T j s).order = cartierSectionVanishingOrder
        (j • projectiveHyperplaneCartier e g hg hggen) x s := by
      rw [hT, cartierGradedTaylor_fin_eq]
      exact cartierTaylorCoordinates_order_eq_vanishingOrder _ x _ _ coordinates s
    have hle : (T j s).order ≤ ((c * j : ℕ) : ℕ∞) := heq ▸ hc x hx j hj s hs
    have hnat' : ((T j s).weightedOrder (fun _ => 1)).toNat ≤ c * j :=
      ENat.toNat_le_of_le_natCast hle
    calc (((T j s).weightedOrder (fun _ => 1)).toNat : ℝ) ≤ ((c * j : ℕ) : ℝ) := by
          exact_mod_cast hnat'
      _ = (c : ℝ) * j := by push_cast; ring
  exact taylor_interior_start hd0 T hTinj hc0 hb (Nat.cast_nonneg c) hlim hord hvol'

/-- (7) at every smooth closed point for the multiples of the hyperplane class, in terms of the
vanishing orders: if (d/(d+1)) (J^d)^(1/d) > d/b, then for all large j and all t ∈ [t_0, b]
some basis of Γ(j J) has (1/N_j) Σ exp(ζ d/t - ζ ord_x(s_i)/j) ≤ 1 - δ. -/
theorem projectiveHyperplane_interior_start_vanishingOrder
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      ∀ {b : ℝ}, 0 < b → (d : ℝ) / b < (d : ℝ) / (d + 1) * (r : ℝ) ^ (d : ℝ)⁻¹ →
      ∀ x : Y, IsClosed {x} →
        ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t → t ≤ b →
          ∃ B : Module.Basis (Fin (Module.finrank K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
            minimizationFunctional j t (ζ * d) (fun i => ζ * ((cartierSectionVanishingOrder
              (j • projectiveHyperplaneCartier e g hg hggen) x (B i)).toNat : ℝ)) ≤ 1 - δ := by
  obtain ⟨r, hr, hfin, hmain⟩ := projectiveHyperplane_interior_start e g hg hggen he hn hd
  refine ⟨r, hr, hfin, fun {b} hb hvol x hx => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨f, hf, coords, -, -⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d
    hn (projectiveHyperplaneCartier e g hg hggen) x hx
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ := hmain hb hvol x hx f hf coords
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hev] with j hj t ht₀t htb
  obtain ⟨B, hB⟩ := hj t ht₀t htb
  refine ⟨B, ?_⟩
  have hvals : (fun i => ζ * realWeightedOrder (fun _ => (1 : ℝ))
      (cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coords j (B i))) =
      (fun i => ζ * ((cartierSectionVanishingOrder
        (j • projectiveHyperplaneCartier e g hg hggen) x (B i)).toNat : ℝ)) := by
    funext i
    have hT0 : cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coords j
        (B i) ≠ 0 := by
      intro h
      apply B.ne_zero i
      exact cartierGradedTaylor_injective _ x f hf coords j (h.trans (map_zero _).symm)
    have hnat := realWeightedOrder_natCast (fun _ : Fin d => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    have heq : (cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coords j
        (B i)).order = cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B i) := by
      rw [cartierGradedTaylor_fin_eq]
      exact cartierTaylorCoordinates_order_eq_vanishingOrder _ x _ _ coords (B i)
    change ζ * (((cartierGradedTaylor (projectiveHyperplaneCartier e g hg hggen) x f hf coords j
      (B i)).order).toNat : ℝ) = _
    rw [heq]
  rwa [hvals] at hB

end MixedFujita
