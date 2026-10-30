/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
Compatible algebra isomorphisms of all ideal-power quotients give an
actual algebra isomorphism of the adic completions. Both maps are built
using the inverse-limit universal property; inverse laws are checked in
every quotient. No completeness, Noetherianity or coordinate existence
is assumed in this construction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {B R S : Type*} [CommRing B] [CommRing R] [CommRing S]
  [Algebra B R] [Algebra B S]

noncomputable def adicCompletionIdealEquiv (I J : Ideal R) (h : I = J) :
    AdicCompletion I R ≃ₐ[B] AdicCompletion J R := by
  subst J
  exact AlgEquiv.refl

theorem adicCompletionIdealEquiv_of (I J : Ideal R) (h : I = J) (r : R) :
    adicCompletionIdealEquiv (B := B) I J h (AdicCompletion.of I R r) =
      AdicCompletion.of J R r := by
  subst J
  rfl

theorem adicCompletion_eval_factor (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I R with | _ a =>
    simp only [AdicCompletion.evalₐ_mk]
    change Ideal.Quotient.mk (I ^ m) (a.val n) = Ideal.Quotient.mk (I ^ m) (a.val m)
    exact AdicCompletion.Ideal.mk_eq_mk I h a

variable (I : Ideal R) (J : Ideal S)
  (e : (n : ℕ) → (R ⧸ I ^ n) ≃ₐ[B] S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) (e n x) =
      e m (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) x))

include he

theorem adicQuotientEquiv_symm_compatible {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ J ^ n) :
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) ((e n).symm x) =
      (e m).symm (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) x) := by
  apply (e m).injective
  rw [← he h, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

noncomputable def adicQuotientEquivLift : AdicCompletion I R →ₐ[B] AdicCompletion J S :=
  AdicCompletion.liftAlgHom J
    (fun n => (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars B))
    (fun h => by
      ext1 x
      change Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h)
        (e _ (AdicCompletion.evalₐ I _ x)) =
        e _ (AdicCompletion.evalₐ I _ x)
      rw [he h, adicCompletion_eval_factor I h])

theorem adicQuotientEquivLift_eval (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicQuotientEquivLift I J e he x) =
      e n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom _ _ _ _ _

noncomputable def adicCompletionQuotientEquiv : AdicCompletion I R ≃ₐ[B] AdicCompletion J S :=
  AlgEquiv.ofAlgHom (adicQuotientEquivLift I J e he)
    (adicQuotientEquivLift J I (fun n => (e n).symm)
      (adicQuotientEquiv_symm_compatible I J e he))
    (by
      ext1 x
      apply AdicCompletion.ext_evalₐ
      intro n
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
        adicQuotientEquivLift_eval, AlgEquiv.apply_symm_apply])
    (by
      ext1 x
      apply AdicCompletion.ext_evalₐ
      intro n
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply,
        adicQuotientEquivLift_eval, AlgEquiv.symm_apply_apply])

theorem adicCompletionQuotientEquiv_eval (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicCompletionQuotientEquiv I J e he x) =
      e n (AdicCompletion.evalₐ I n x) :=
  adicQuotientEquivLift_eval I J e he n x

theorem adicCompletionQuotientEquiv_symm_eval (n : ℕ) (x : AdicCompletion J S) :
    AdicCompletion.evalₐ I n ((adicCompletionQuotientEquiv I J e he).symm x) =
      (e n).symm (AdicCompletion.evalₐ J n x) :=
  adicQuotientEquivLift_eval J I (fun n => (e n).symm)
    (adicQuotientEquiv_symm_compatible I J e he) n x

end MixedFujita
