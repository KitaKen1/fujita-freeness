/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompletionQuotientEquiv
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
Localization at a maximal ideal preserves its adic completion. The
isomorphisms of the actual ideal-power quotients are Mathlib's localization
isomorphisms; their compatibility is proved here, then passed to the
inverse-limit construction. This is valid without Noetherianity.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] [IsLocalRing S]

theorem localizationQuotientPow_compatible {m n : ℕ} (h : m ≤ n) (x : R ⧸ p ^ n) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p S m
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (p ^ n) x
  rfl

noncomputable def localizationCompletionEquiv :
    AdicCompletion p R ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  adicCompletionQuotientEquiv p (IsLocalRing.maximalIdeal S)
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S)
    (localizationQuotientPow_compatible p S)

theorem localizationCompletionEquiv_eval (n : ℕ) (x : AdicCompletion p R) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n (localizationCompletionEquiv p S x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n (AdicCompletion.evalₐ p n x) :=
  adicCompletionQuotientEquiv_eval p (IsLocalRing.maximalIdeal S)
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S)
    (localizationQuotientPow_compatible p S) n x

theorem localizationCompletionEquiv_symm_eval (n : ℕ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal S) S) :
    AdicCompletion.evalₐ p n ((localizationCompletionEquiv p S).symm x) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).symm
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x) :=
  adicCompletionQuotientEquiv_symm_eval p (IsLocalRing.maximalIdeal S)
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S)
    (localizationQuotientPow_compatible p S) n x

theorem localizationCompletionEquiv_of (r : R) :
    localizationCompletionEquiv p S (AdicCompletion.of p R r) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [localizationCompletionEquiv_eval, AdicCompletion.evalₐ_of,
    IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk, AdicCompletion.evalₐ_of]

theorem localizationCompletionEquiv_symm_fraction_eval (n : ℕ) (r : R)
    (s : p.primeCompl) :
    AdicCompletion.evalₐ p n ((localizationCompletionEquiv p S).symm
      (AdicCompletion.of (IsLocalRing.maximalIdeal S) S (IsLocalization.mk' S r s))) *
        Ideal.Quotient.mk (p ^ n) s = Ideal.Quotient.mk (p ^ n) r := by
  rw [localizationCompletionEquiv_symm_eval, AdicCompletion.evalₐ_of]
  exact IsLocalization.AtPrime.equivQuotMaximalIdealPow_symm_apply_mk_mul p S n r s

end MixedFujita
