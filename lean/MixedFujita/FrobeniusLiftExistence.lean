/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftOneForms
public import Mathlib.RingTheory.Smooth.Basic

/-!
Existence of local Frobenius lifts (step 10).

Let `A` be a ring with an endomorphism `σ` (for instance the Witt vectors `W₂(K)` with their
Frobenius), `L` a formally smooth `A`-algebra and `π : L → S` a surjection onto a ring of
characteristic `p` with square-zero kernel, such that `σ` lifts the `p`-th power map modulo the
kernel. Then the Frobenius of `S` lifts to a ring endomorphism `F` of `L`, `σ`-semilinear over `A`
(`exists_frobeniusLift_of_formallySmooth`): view `L` as an `A`-algebra through `σ`
(`SigmaTwisted`) and lift `L → S → S ≅ L ⧸ ker π` by formal smoothness. If moreover the constants
of the base field have `σ`-fixed Teichmüller-type representatives in `A`, then `F` satisfies the
constant-lift hypothesis `hK` of the Deligne–Illusie map of check-407
(`frobeniusLift_constant_lift`). This is the local input of the global Deligne–Illusie map: every
affine open of a smooth lift over `W₂(K)` carries a Frobenius lift.
-/

@[expose] public section

namespace MixedFujita

universe u v w

/-- `L` with its `A`-algebra structure twisted by an endomorphism `σ` of `A`. -/
def SigmaTwisted {A : Type u} [CommRing A] (_σ : A →+* A) (L : Type v) : Type v := L

section Twisted

variable {A : Type u} [CommRing A] (σ : A →+* A) (L : Type v) [CommRing L] [Algebra A L]

instance sigmaTwistedCommRing : CommRing (SigmaTwisted σ L) := inferInstanceAs (CommRing L)

/-- The `σ`-twisted `A`-algebra structure. -/
noncomputable instance sigmaTwistedAlgebra : Algebra A (SigmaTwisted σ L) :=
  (((algebraMap A L).comp σ : A →+* L) : A →+* SigmaTwisted σ L).toAlgebra

theorem sigmaTwisted_algebraMap_eq (a : A) :
    (algebraMap A (SigmaTwisted σ L) a : L) = algebraMap A L (σ a) := rfl

end Twisted

/-- **Frobenius lifts exist on formally smooth lifts.** -/
theorem exists_frobeniusLift_of_formallySmooth {A : Type u} [CommRing A] (σ : A →+* A)
    {L : Type v} [CommRing L] [Algebra A L] [Algebra.FormallySmooth A L]
    {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (π : L →+* S) (hπ : Function.Surjective π) (hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0)
    (hσ : ∀ a, π (algebraMap A L (σ a)) = π (algebraMap A L a) ^ p) :
    ∃ F : L →+* L, (∀ x, π (F x) = π x ^ p) ∧ ∀ a, F (algebraMap A L a) = algebraMap A L (σ a) := by
  let B := SigmaTwisted σ L
  let πB : B →+* S := π
  have hπB : Function.Surjective πB := hπ
  let I : Ideal B := RingHom.ker πB
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    exact hsq x y hx hy
  let e : B ⧸ I ≃+* S := RingHom.quotientKerEquivOfSurjective hπB
  have he : ∀ y : B, e.symm (πB y) = Ideal.Quotient.mk I y := fun y => by
    rw [RingEquiv.symm_apply_eq]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hπB y).symm
  let g₀ : L →+* B ⧸ I := e.symm.toRingHom.comp ((frobenius S p).comp π)
  let g : L →ₐ[A] B ⧸ I :=
    { g₀ with
      commutes' := fun a => by
        change e.symm (frobenius S p (π (algebraMap A L a))) =
          Ideal.Quotient.mk I (algebraMap A B a)
        rw [frobenius_def, ← hσ a, ← he]
        rfl }
  let F := Algebra.FormallySmooth.lift I hI g
  let F' : L →+* L :=
    { toFun := fun x => (F x : L)
      map_one' := F.map_one
      map_mul' := F.map_mul
      map_zero' := F.map_zero
      map_add' := F.map_add }
  refine ⟨F', fun x => ?_, fun a => F.commutes a⟩
  have h := congrArg e (Algebra.FormallySmooth.mk_lift I hI g x)
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk] at h
  change πB (F x) = π x ^ p
  rw [h]
  change e (e.symm (frobenius S p (π x))) = _
  rw [RingEquiv.apply_symm_apply, frobenius_def]

/-- With `σ`-fixed Teichmüller-type representatives of the constants, the Frobenius lift satisfies
the constant-lift hypothesis of the Deligne–Illusie map (check-407). -/
theorem frobeniusLift_constant_lift {A : Type u} [CommRing A] (σ : A →+* A)
    {K : Type w} [Field K] {L : Type v} [CommRing L] [Algebra A L] {S : Type v} [CommRing S]
    [Algebra K S] (p : ℕ) (π : L →+* S) (F : L →+* L)
    (hFA : ∀ a, F (algebraMap A L a) = algebraMap A L (σ a))
    (hT : ∀ c : K, ∃ a : A, σ a = a ^ p ∧ π (algebraMap A L a) = algebraMap K S c) :
    ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p := by
  intro c
  obtain ⟨a, haσ, hac⟩ := hT c
  exact ⟨algebraMap A L a, hac, by rw [hFA, haσ, map_pow]⟩

end MixedFujita
