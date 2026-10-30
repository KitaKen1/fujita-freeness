/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
The map of adic completions induced by a ring homomorphism φ : A → B with φ(I) ⊆ J. The maps
Â → A/I^n → B/J^n are compatible, so they lift to Â → B̂ by the universal property of the
completion; the lift sends the image of a ∈ A to the image of φ(a), and it is a map of algebras
over a base ring when φ is. This is the map of completed local rings of a morphism of schemes
at a point, used to transport Taylor expansions along the morphism.
-/

@[expose] public section

namespace MixedFujita

open AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B]

theorem adicCompletion_factor_evalₐ (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk, AdicCompletion.Ideal.mk_eq_mk I hle s]

theorem pow_le_comap_pow_of_map_le {I : Ideal A} {J : Ideal B} (φ : A →+* B) (h : I.map φ ≤ J)
    (n : ℕ) : I ^ n ≤ (J ^ n).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

theorem adicCompletionMap_compat (I : Ideal A) (J : Ideal B) (φ : A →+* B) (h : I.map φ ≤ J)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp
        ((Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_map_le φ h n)).comp
          (evalₐ I n).toRingHom) =
      (Ideal.quotientMap (J ^ m) φ (pow_le_comap_pow_of_map_le φ h m)).comp
        (evalₐ I m).toRingHom := by
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← adicCompletion_factor_evalₐ I hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← ha, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  simp [Ideal.Quotient.factorPow]

/-- The map of adic completions induced by φ with φ(I) ⊆ J. -/
noncomputable def adicCompletionMap (I : Ideal A) (J : Ideal B) (φ : A →+* B) (h : I.map φ ≤ J) :
    AdicCompletion I A →+* AdicCompletion J B :=
  liftRingHom J (fun n => (Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_map_le φ h n)).comp
      (evalₐ I n).toRingHom) (fun hle => adicCompletionMap_compat I J φ h hle)

theorem evalₐ_adicCompletionMap (I : Ideal A) (J : Ideal B) (φ : A →+* B) (h : I.map φ ≤ J)
    (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (adicCompletionMap I J φ h x) =
      Ideal.quotientMap (J ^ n) φ (pow_le_comap_pow_of_map_le φ h n) (evalₐ I n x) := by
  rw [adicCompletionMap, evalₐ_liftRingHom]
  rfl

/-- The completion map sends the image of a to the image of φ(a). -/
theorem adicCompletionMap_of (I : Ideal A) (J : Ideal B) (φ : A →+* B) (h : I.map φ ≤ J)
    (a : A) : adicCompletionMap I J φ h (of I A a) = of J B (φ a) := by
  apply ext_evalₐ
  intro n
  rw [evalₐ_adicCompletionMap, evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

variable (R : Type*) [CommRing R] [Algebra R A] [Algebra R B]

/-- The completion map of an algebra homomorphism is an algebra homomorphism. -/
noncomputable def adicCompletionMapₐ (I : Ideal A) (J : Ideal B) (φ : A →ₐ[R] B)
    (h : I.map φ.toRingHom ≤ J) : AdicCompletion I A →ₐ[R] AdicCompletion J B :=
  AlgHom.mk (adicCompletionMap I J φ.toRingHom h) (fun r => by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass]
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, adicCompletionMap_of]
    simp)

theorem adicCompletionMapₐ_of (I : Ideal A) (J : Ideal B) (φ : A →ₐ[R] B)
    (h : I.map φ.toRingHom ≤ J) (a : A) :
    adicCompletionMapₐ R I J φ h (of I A a) = of J B (φ a) :=
  adicCompletionMap_of I J φ.toRingHom h a

end MixedFujita
