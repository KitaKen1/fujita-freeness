/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CompletionQuotientEquiv
public import Mathlib.RingTheory.Etale.Basic

/-!
A formally etale algebra with an isomorphic quotient modulo an ideal has
isomorphic quotients modulo every power of that ideal. Formal smoothness
constructs the inverse modulo each power; formal unramifiedness proves
the inverse law. This avoids a separate Cohen structure theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem quotientPowFactor_ker_nilpotent (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    IsNilpotent (RingHom.ker
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn) : R ⧸ I ^ n →ₐ[R] R ⧸ I)) := by
  have hk : RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn)) =
      I.map (Ideal.Quotient.mk (I ^ n)) := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.mem_quotient_iff_mem (Ideal.pow_le_self hn)]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk]
  use n
  simp [← Ideal.map_pow]

noncomputable def mappedIdealQuotientPowMap (I : Ideal R) (S : Type*) [CommRing S]
    [Algebra R S] (n : ℕ) :
    (R ⧸ I ^ n) →ₐ[R] S ⧸ (I.map (algebraMap R S)) ^ n :=
  Ideal.Quotient.liftₐ (I ^ n) (Algebra.ofId R (S ⧸ (I.map (algebraMap R S)) ^ n))
    (fun r hr => by
      change Ideal.Quotient.mk _ (algebraMap R S r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr)

theorem mappedIdealQuotientPowMap_mk (I : Ideal R) (n : ℕ) (r : R) :
    mappedIdealQuotientPowMap I S n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R S)) ^ n) (algebraMap R S r) := rfl

theorem quotientAlgHom_kills_mappedIdeal_pow (I : Ideal R) (n : ℕ)
    (g : S →ₐ[R] R ⧸ I ^ n) :
    (I.map (algebraMap R S)) ^ n ≤ RingHom.ker g := by
  rw [← Ideal.map_eq_bot_iff_le_ker, ← Ideal.map_pow]
  change ((I ^ n).map (algebraMap R S)).map g.toRingHom = ⊥
  rw [Ideal.map_map]
  have hg : g.toRingHom.comp (algebraMap R S) = Ideal.Quotient.mk (I ^ n) :=
    RingHom.ext (fun r => g.commutes r)
  rw [hg, Ideal.map_quotient_self]

variable (I : Ideal R) (S)
  [Algebra.FormallyEtale R S]
  (e : (R ⧸ I) ≃ₐ[R] S ⧸ I.map (algebraMap R S))

include e

@[irreducible]
noncomputable def formallyEtaleQuotientPowEquiv (n : ℕ) :
    (R ⧸ I ^ n) ≃ₐ[R] S ⧸ (I.map (algebraMap R S)) ^ n := by
  let f := mappedIdealQuotientPowMap I S n
  by_cases hn : n = 0
  · subst n
    letI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    letI : Subsingleton (S ⧸ (I.map (algebraMap R S)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact AlgEquiv.ofBijective f
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · let q := Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn : I ^ n ≤ I)
    let qS := Ideal.Quotient.factorₐ R
      (Ideal.pow_le_self hn : (I.map (algebraMap R S)) ^ n ≤ I.map (algebraMap R S))
    let g := Algebra.FormallySmooth.liftOfSurjective
      (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S)))) q
      (Ideal.Quotient.factor_surjective (Ideal.pow_le_self hn : I ^ n ≤ I))
      (quotientPowFactor_ker_nilpotent I hn)
    let gi := Ideal.Quotient.liftₐ ((I.map (algebraMap R S)) ^ n) g
      (fun s hs => (RingHom.mem_ker).mp (quotientAlgHom_kills_mappedIdeal_pow I n g hs))
    have hgf : gi.comp f = AlgHom.id R (R ⧸ I ^ n) := by
      apply AlgHom.ext
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact g.commutes r
    have hfg : f.comp gi = AlgHom.id R (S ⧸ (I.map (algebraMap R S)) ^ n) := by
      have hcan : qS.comp f =
          e.toAlgHom.comp q := by
        apply AlgHom.ext
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact (e.commutes r).symm
      have hgg : q.comp g =
          e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))) :=
        Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
      have hcomp : f.comp g = Ideal.Quotient.mkₐ R ((I.map (algebraMap R S)) ^ n) := by
        apply Algebra.FormallyUnramified.lift_unique' qS
          (quotientPowFactor_ker_nilpotent (I.map (algebraMap R S)) hn)
        rw [← AlgHom.comp_assoc, hcan, AlgHom.comp_assoc, hgg,
          ← AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.id_comp]
        rfl
      apply AlgHom.ext
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact AlgHom.congr_fun hcomp s
    exact AlgEquiv.ofAlgHom f gi hfg hgf

theorem formallyEtaleQuotientPowEquiv_mk (n : ℕ) (r : R) :
    formallyEtaleQuotientPowEquiv (I := I) (S := S) (e := e) n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk ((I.map (algebraMap R S)) ^ n) (algebraMap R S r) :=
  (formallyEtaleQuotientPowEquiv (I := I) (S := S) (e := e) n).commutes r

theorem formallyEtaleQuotientPowEquiv_compatible {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)
      (formallyEtaleQuotientPowEquiv (I := I) (S := S) (e := e) n x) =
      formallyEtaleQuotientPowEquiv (I := I) (S := S) (e := e) m
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factorₐ_apply_mk, formallyEtaleQuotientPowEquiv_mk]

noncomputable def formallyEtaleCompletionEquiv :
    AdicCompletion I R ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  adicCompletionQuotientEquiv I (I.map (algebraMap R S))
    (formallyEtaleQuotientPowEquiv (I := I) (S := S) (e := e)) (formallyEtaleQuotientPowEquiv_compatible (I := I) (S := S) (e := e))

theorem formallyEtaleCompletionEquiv_of (r : R) :
    formallyEtaleCompletionEquiv (I := I) (S := S) (e := e) (AdicCompletion.of I R r) =
      AdicCompletion.of (I.map (algebraMap R S)) S (algebraMap R S r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [formallyEtaleCompletionEquiv, adicCompletionQuotientEquiv_eval,
    AdicCompletion.evalₐ_of, formallyEtaleQuotientPowEquiv_mk, AdicCompletion.evalₐ_of]

end MixedFujita
