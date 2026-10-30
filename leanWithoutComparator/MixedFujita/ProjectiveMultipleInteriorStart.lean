/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveMultipleHilbert
public import MixedFujita.ProjectiveInteriorStart
public import MixedFujita.CartierAmpleTransfer

/-!
The uniform order bound and the interior condition (7) for the multiples of a Cartier divisor A
whose multiple k A is the hyperplane class J of an actual smooth integral closed subscheme of
polynomial projective space over an algebraically closed field, as for L = rA in §7. If for every
m ≥ e₀ and every closed point x some section of m A does not vanish at x, multiplying a section s
of j A by such a section of m A with j + m = k (j + e₀ + 1) does not change ord_x and lands in
Γ((j + e₀ + 1) J), so ord_x(s) ≤ c (2 + e₀) j. The same bound also follows from s^k ∈ Γ(j J)
without any sections of m A. With the Hilbert asymptotics h^0(j A) ~ (J^d / k^d) j^d / d!, which
need nonzero sections of m A for m ≥ e₀, this gives (7) at every closed point when
(d/(d+1)) (A^d)^(1/d) > d/b, where A^d = J^d / k^d.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
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

/-- The uniform order bound for the multiples of A. -/
theorem projectiveHyperplane_multiple_order_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (A : CartierDivisor Y) {k : ℕ}
    (hk : 0 < k) (hkA : k • A = projectiveHyperplaneCartier e g hg hggen) (e₀ : ℕ)
    (hbpf : ∀ m, e₀ ≤ m → ∀ x : Y, IsClosed {x} →
      ∃ σ : Γ((m • A).sheaf, ⊤), cartierSectionVanishingOrder (m • A) x σ = 0) :
    ∃ C : ℕ, ∀ x : Y, IsClosed {x} → ∀ j : ℕ, 1 ≤ j → ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
      cartierSectionVanishingOrder (j • A) x s ≤ ((C * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := projectiveHyperplane_cartierOrder_le e g hg hggen he hn hd
  set J := projectiveHyperplaneCartier e g hg hggen with hJ
  have hmul : ∀ q : ℕ, (k * q) • A = q • J := by
    intro q
    rw [mul_comm, mul_smul, hkA]
  have hcJ : ∀ (D : CartierDivisor Y) (q : ℕ), D = q • J → 1 ≤ q → ∀ x : Y, IsClosed {x} →
      ∀ t : Γ(D.sheaf, ⊤), t ≠ 0 → cartierSectionVanishingOrder D x t ≤ ((c * q : ℕ) : ℕ∞) := by
    intro D q hD hq x hx t ht
    subst hD
    exact hc x hx q hq t ht
  refine ⟨c * (2 + e₀), fun x hx j hj s hs => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨f, hf, coords, -, -⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d
    hn A x hx
  set q := j + e₀ + 1 with hq
  set m := k * q - j with hm
  have hkq : q ≤ k * q := Nat.le_mul_of_pos_left q hk
  have hjm : j + m = k * q := by omega
  have hme : e₀ ≤ m := by omega
  obtain ⟨σ, hσ⟩ := hbpf m hme x hx
  have hordT : ∀ (i : ℕ) (u : Γ((i • A).sheaf, ⊤)),
      (cartierGradedTaylor A x f hf coords i u).order =
        cartierSectionVanishingOrder (i • A) x u := by
    intro i u
    rw [cartierGradedTaylor_fin_eq]
    exact cartierTaylorCoordinates_order_eq_vanishingOrder _ x _ _ coords u
  set t := cartierGradedSectionProduct A j m s σ with ht
  have hprod : cartierSectionVanishingOrder ((j + m) • A) x t =
      cartierSectionVanishingOrder (j • A) x s := by
    rw [← hordT, ht, cartierGradedTaylor_product, powerSeries_order_mul_exact, hordT, hordT, hσ,
      add_zero]
  have ht0 : t ≠ 0 := by
    intro h0
    have h1 := (cartierSectionVanishingOrder_eq_top_iff ((j + m) • A) x t).mpr h0
    rw [hprod, cartierSectionVanishingOrder_eq_top_iff] at h1
    exact hs h1
  have hbound := hcJ ((j + m) • A) q (by rw [hjm, hmul]) (by omega) x hx t ht0
  rw [hprod] at hbound
  refine hbound.trans ?_
  have hqj : q ≤ (2 + e₀) * j := by
    have h1 : (1 + e₀) ≤ (1 + e₀) * j := Nat.le_mul_of_pos_right _ hj
    have h2 : (2 + e₀) * j = j + (1 + e₀) * j := by ring
    omega
  have h3 : c * q ≤ c * (2 + e₀) * j := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left c hqj
  exact_mod_cast h3

/-- (7) at every smooth closed point for the multiples of A, when k A is the hyperplane class,
the multiples m A with m ≥ e₀ have nonzero sections, and (d/(d+1)) (J^d / k^d)^(1/d) > d/b, where
J^d = r is the leading coefficient of the Hilbert function of J (the limit is part of the
statement). -/
theorem projectiveHyperplane_multiple_interior_start
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (A : CartierDivisor Y) {k : ℕ}
    (hk : 0 < k) (hkA : k • A = projectiveHyperplaneCartier e g hg hggen) (e₀ : ℕ)
    (hsec : ∀ m, e₀ ≤ m → ∃ σ : Γ((m • A).sheaf, ⊤), σ ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ _ : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K Γ((D • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d) atTop
        (𝓝 ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) ∧
      ∀ {b : ℝ}, 0 < b →
        (d : ℝ) / b < (d : ℝ) / (d + 1) * ((r : ℝ) / (k : ℝ) ^ d) ^ (d : ℝ)⁻¹ →
      ∀ x : Y, IsClosed {x} →
        ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t → t ≤ b →
          ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K
              Γ((j • A).sheaf, ⊤),
            minimizationFunctional j t (ζ * d) (fun i => ζ * ((cartierSectionVanishingOrder
              (j • A) x (B i)).toNat : ℝ)) ≤ 1 - δ := by
  obtain ⟨r, hr, hfin, hlim⟩ := projectiveHyperplane_hilbert_of_multiple e g hg hggen he hn hd A
    hk hkA e₀ hsec
  obtain ⟨C, hC⟩ := cartierMultiple_vanishingOrder_le e g hg hggen he hn hd A hk
    (1 : Y.functionFieldˣ) (by rw [principalCartierDivisor_one, add_zero]; exact hkA)
  refine ⟨r, hr, hfin, hlim, fun {b} hb hvol x hx => ?_⟩
  have := smoothScheme_stalk_isNoetherianRing (K := K) x
  have hfin' : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤) := hfin
  obtain ⟨f, hf, coords, -, -⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d
    hn A x hx
  have hd0 : 0 < d := hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hc0 : (0 : ℝ) < (r : ℝ) / d.factorial / (k : ℝ) ^ d := by positivity
  have hvol' : (d : ℝ) / b < (d : ℝ) / (d + 1) *
      ((d.factorial : ℝ) * ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) ^ (d : ℝ)⁻¹ := by
    have h1 : (d.factorial : ℝ) * ((r : ℝ) / d.factorial / (k : ℝ) ^ d) =
        (r : ℝ) / (k : ℝ) ^ d := by
      field_simp
    rwa [h1]
  set T := cartierGradedTaylor A x f hf coords with hT
  have hTinj : ∀ j, Function.Injective (T j) := cartierGradedTaylor_injective _ x f hf coords
  have hordT : ∀ (i : ℕ) (u : Γ((i • A).sheaf, ⊤)),
      (T i u).order = cartierSectionVanishingOrder (i • A) x u := by
    intro i u
    rw [hT, cartierGradedTaylor_fin_eq]
    exact cartierTaylorCoordinates_order_eq_vanishingOrder _ x _ _ coords u
  have hrw : ∀ (i : ℕ) (u : Γ((i • A).sheaf, ⊤)), u ≠ 0 →
      realWeightedOrder (fun _ => (1 : ℝ)) (T i u) =
        ((cartierSectionVanishingOrder (i • A) x u).toNat : ℝ) := by
    intro i u hu
    have hT0 : T i u ≠ 0 := fun h => hu (hTinj i (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin d => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    change (((T i u).order).toNat : ℝ) = _
    rw [hordT]
  have hord : ∀ᶠ j : ℕ in atTop, ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
      realWeightedOrder (fun _ => (1 : ℝ)) (T j s) ≤ (C : ℝ) * j := by
    filter_upwards [eventually_ge_atTop 1] with j hj s hs
    rw [hrw j s hs]
    have hle := hC x hx j hj s hs
    have hnat' : (cartierSectionVanishingOrder (j • A) x s).toNat ≤ C * j :=
      ENat.toNat_le_of_le_natCast hle
    calc ((cartierSectionVanishingOrder (j • A) x s).toNat : ℝ) ≤ ((C * j : ℕ) : ℝ) := by
          exact_mod_cast hnat'
      _ = (C : ℝ) * j := by push_cast; ring
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ :=
    taylor_interior_start hd0 T hTinj hc0 hb (Nat.cast_nonneg C) hlim hord hvol'
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hev] with j hj t ht₀t htb
  obtain ⟨B, hB⟩ := hj t ht₀t htb
  refine ⟨B, ?_⟩
  have hvals : (fun i => ζ * realWeightedOrder (fun _ => (1 : ℝ)) (T j (B i))) =
      (fun i => ζ * ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) := by
    funext i
    rw [hrw j (B i) (B.ne_zero i)]
  rwa [hvals] at hB

end MixedFujita
