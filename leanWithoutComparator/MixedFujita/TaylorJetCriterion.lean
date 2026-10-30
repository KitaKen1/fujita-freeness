/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialJetIdeal
public import MixedFujita.GeometricJacobianBound

/-!
Exact characteristic-zero jet equations for ordinary Taylor order. Order at least h is
vanishing of all derivatives of length below h; the converse uses the already proved existence
of a unit derivative at the actual order. Polynomial Taylor translation commutes with partials,
so the actual polynomial jet ideal detects high Taylor order at every affine point.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {σ K : Type*} [Field K]

/-- A derivative list lowers ordinary power-series order by at most its length. -/
theorem order_le_iteratedPDeriv_add_length (L : List σ) (f : MvPowerSeries σ K) :
    f.order ≤ (iteratedPDeriv L f).order + L.length := by
  induction L with
  | nil => simp [iteratedPDeriv]
  | cons i L ih =>
    calc f.order ≤ (iteratedPDeriv L f).order + L.length := ih
      _ ≤ ((pderiv i (iteratedPDeriv L f)).order + 1) + L.length := by
        gcongr
        exact order_le_pderiv_add_one i _
      _ = (iteratedPDeriv (i :: L) f).order + (i :: L).length := by
        simp only [iteratedPDeriv, List.length_cons, Nat.cast_add, Nat.cast_one]
        ac_rfl

/-- In characteristic zero, the exact high-order condition is vanishing of every lower jet,
including the zero series and h = 0. -/
theorem order_ge_iff_iteratedPDeriv_constantCoeff [CharZero K]
    (f : MvPowerSeries σ K) (h : ℕ) :
    (h : ℕ∞) ≤ f.order ↔ ∀ L : List σ, L.length < h →
      constantCoeff (iteratedPDeriv L f) = 0 := by
  constructor
  · intro hf L hL
    by_contra hc
    have hzero : (iteratedPDeriv L f).order = 0 := by
      by_contra hn
      exact hc (order_ne_zero_iff_constCoeff_eq_zero.mp hn)
    have hb := hf.trans (order_le_iteratedPDeriv_add_length L f)
    rw [hzero, zero_add] at hb
    have : h ≤ L.length := by exact_mod_cast hb
    omega
  · intro hj
    by_contra hn
    have hf : f ≠ 0 := by
      intro h0
      simp only [h0, order_zero, le_top, not_true_eq_false] at hn
    obtain ⟨L, hL, hu⟩ := exists_iteratedPDeriv_isUnit hf
    have hlen : L.length < h := by
      have ht : f.order < (h : ℕ∞) := lt_of_not_ge hn
      rw [← hL] at ht
      exact_mod_cast ht
    exact (isUnit_iff_constantCoeff.mp hu).ne_zero (hj L hlen)

/-- The actual polynomial Taylor translation at an affine K-valued point. -/
noncomputable def affinePolynomialTaylor (a : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPowerSeries σ K :=
  MvPolynomial.aeval (fun i => C (a i) + X i)

/-- Its constant term is ordinary polynomial evaluation at the point. -/
theorem constantCoeff_affinePolynomialTaylor (a : σ → K) (f : MvPolynomial σ K) :
    constantCoeff (affinePolynomialTaylor a f) = MvPolynomial.eval a f := by
  have heq : constantCoeff.comp (affinePolynomialTaylor a).toRingHom = MvPolynomial.eval a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affinePolynomialTaylor, RingHom.comp_apply, ← MvPowerSeries.c_eq_algebraMap]
    · intro i
      simp [affinePolynomialTaylor, RingHom.comp_apply]
  exact congrArg (fun H => H f) heq

/-- Formal partial differentiation commutes with the actual polynomial translation. -/
theorem pderiv_affinePolynomialTaylor (a : σ → K) (i : σ) (f : MvPolynomial σ K) :
    pderiv i (affinePolynomialTaylor a f) = affinePolynomialTaylor a (MvPolynomial.pderiv i f) := by
  classical
  have hX (j : σ) : pderiv i (affinePolynomialTaylor a (MvPolynomial.X j)) =
      affinePolynomialTaylor a (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
    by_cases hji : j = i
    · subst j
      simp [affinePolynomialTaylor, pderiv_X_self]
    · simp [affinePolynomialTaylor, MvPowerSeries.pderiv_X_of_ne hji,
        MvPolynomial.pderiv_X_of_ne hji]
  induction f using MvPolynomial.induction_on with
  | C r => simp [affinePolynomialTaylor]
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | mul_X f j ih =>
    simp only [map_mul, (pderiv i).leibniz, smul_eq_mul, MvPolynomial.pderiv_mul, map_add]
    rw [ih, hX]
    ring

/-- All iterated derivatives commute with Taylor translation. -/
theorem iteratedPDeriv_affinePolynomialTaylor (a : σ → K) (L : List σ)
    (f : MvPolynomial σ K) :
    iteratedPDeriv L (affinePolynomialTaylor a f) =
      affinePolynomialTaylor a (polynomialIteratedPDeriv L f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [iteratedPDeriv, ih, pderiv_affinePolynomialTaylor]
    rfl

/-- Exact polynomial derivative equations for high Taylor order, without any preselected
nonzero coefficient or nonvanishing assumption on the polynomial. -/
theorem affinePolynomialTaylor_order_ge_iff [CharZero K] (a : σ → K)
    (f : MvPolynomial σ K) (h : ℕ) :
    (h : ℕ∞) ≤ (affinePolynomialTaylor a f).order ↔
      ∀ L : List σ, L.length < h →
        MvPolynomial.eval a (polynomialIteratedPDeriv L f) = 0 := by
  rw [order_ge_iff_iteratedPDeriv_constantCoeff]
  simp only [iteratedPDeriv_affinePolynomialTaylor, constantCoeff_affinePolynomialTaylor]

/-- The global polynomial jet ideal at an affine point detects simultaneous actual Taylor
order conditions for every generator. -/
theorem polynomialJetIdeal_le_eval_ker_iff [CharZero K] {J : Type*}
    (g : J → MvPolynomial σ K) (h : ℕ) (a : σ → K) :
    polynomialJetIdeal g h ≤ RingHom.ker (MvPolynomial.eval a) ↔
      ∀ j, (h : ℕ∞) ≤ (affinePolynomialTaylor a (g j)).order := by
  rw [polynomialJetIdeal_le_iff]
  simp only [RingHom.mem_ker, affinePolynomialTaylor_order_ge_iff]

end MixedFujita
