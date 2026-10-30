/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieExteriorLift

/-!
The Deligne–Illusie map on `b`-forms of a chart is a cocycle of the right degrees, with diagonal
`b! · Φ` (step 10).

For the map `diSeqAlt : ⋀^b → (total index cochains)` of check 455 we transport three properties
from the generators `ω_1 ∧ ⋯ ∧ ω_b` to all of `⋀^b` (the image of `exteriorPower.ιMulti` spans):
* every value is a `D`-cocycle (`seqTotalD_diSeqAlt`; on generators from check 452, and `D`
  commutes with the Frobenius-twisted scalars because `d(f^p) = 0`, `seqTotalD_frobenius_smul`);
* the component of Čech degree `a` of every value is a `(b - a)`-form and vanishes for `a > b`
  (`seqTotalHomogeneous_diSeqAlt`, from check 453);
* the component of Čech degree `0` is `b! · Φ_{F_{s 0}}` (`diSeqAlt_zero`): on generators the
  permuted products are `sgn σ · ω_1 ∧ ⋯ ∧ ω_b`, so the signs square to `1`.
-/

@[expose] public section

namespace MixedFujita

universe u v w

section General

variable {J : Type*} {A : Type*} [Ring A] (d : A →+ A)

/-- **The total differential as an additive map.** -/
def seqTotalDHom : (ℕ → (ℕ → J) → A) →+ (ℕ → (ℕ → J) → A) where
  toFun := seqTotalD d
  map_zero' := by
    funext c s
    cases c <;> simp [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD]
  map_add' α β := by
    funext c s
    cases c <;>
      simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, Pi.add_apply, map_add,
        mul_add, Finset.sum_add_distrib] <;> abel

theorem seqTotalDHom_apply (α : ℕ → (ℕ → J) → A) : seqTotalDHom d α = seqTotalD d α := rfl

end General

section Homogeneous

variable {J : Type*} {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem seqTotalHomogeneous_zero (t : ℕ) :
    SeqTotalHomogeneous t (0 : ℕ → (ℕ → J) → ExteriorAlgebra R M) :=
  fun _ _ => ⟨Submodule.zero_mem _, fun _ => rfl⟩

theorem seqTotalHomogeneous_add {t : ℕ} {α β : ℕ → (ℕ → J) → ExteriorAlgebra R M}
    (hα : SeqTotalHomogeneous t α) (hβ : SeqTotalHomogeneous t β) :
    SeqTotalHomogeneous t (α + β) := fun a s =>
  ⟨Submodule.add_mem _ (hα a s).1 (hβ a s).1, fun h => by
    simp only [Pi.add_apply, (hα a s).2 h, (hβ a s).2 h, add_zero]⟩

theorem seqTotalHomogeneous_smul {t : ℕ} {α : ℕ → (ℕ → J) → ExteriorAlgebra R M} (r : R)
    (hα : SeqTotalHomogeneous t α) : SeqTotalHomogeneous t (r • α) := fun a s =>
  ⟨Submodule.smul_mem _ r (hα a s).1, fun h => by
    simp only [Pi.smul_apply, (hα a s).2 h, smul_zero]⟩

theorem seqTotalHomogeneous_zsmul {t : ℕ} {α : ℕ → (ℕ → J) → ExteriorAlgebra R M} (k : ℤ)
    (hα : SeqTotalHomogeneous t α) : SeqTotalHomogeneous t (k • α) := fun a s =>
  ⟨Submodule.smul_of_tower_mem _ k (hα a s).1, fun h => by
    simp only [Pi.smul_apply, (hα a s).2 h, smul_zero]⟩

end Homogeneous

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

omit hp in
/-- **`D` commutes with the Frobenius-twisted scalars**, because `d(f^p) = 0`. -/
theorem seqTotalD_frobenius_smul (f : S) (g : ℕ → (ℕ → J) → ExteriorAlgebra S Ω[S⁄K]) (c : ℕ)
    (s : ℕ → J) :
    seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom (fun a t => f ^ p • g a t) c s =
      f ^ p • seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom g c s := by
  have hd : ∀ x : ExteriorAlgebra S Ω[S⁄K],
      kaehlerDeRhamDiff y hy (f ^ p • x) = f ^ p • kaehlerDeRhamDiff y hy x := fun x => by
    rw [kaehlerDeRhamDiff_smul, kaehlerD_pow_char p f, map_zero, zero_mul, zero_add]
  cases c with
  | zero =>
    simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, LinearMap.toAddMonoidHom_coe, hd,
      mul_smul_comm, zero_add]
  | succ c =>
    simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, LinearMap.toAddMonoidHom_coe,
      hd, mul_smul_comm, Finset.smul_sum, smul_add]

variable (K S J) in
/-- Reading total cochains with values in the Frobenius twist in the exterior algebra. -/
def twistedPiHom :
    (ℕ → (ℕ → J) → FrobeniusTwistedExterior K S p) →+ (ℕ → (ℕ → J) → ExteriorAlgebra S Ω[S⁄K]) where
  toFun g a t := twistedToExterior (g a t)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem twistedPiHom_smul (f : S) (g : ℕ → (ℕ → J) → FrobeniusTwistedExterior K S p) :
    twistedPiHom K S p J (f • g) = fun a t => f ^ p • twistedPiHom K S p J g a t :=
  funext fun a => funext fun t => frobeniusTwisted_smul_eq p f (g a t)

theorem frobeniusLiftExterior_zsmul (G : L →+* L) (hG : ∀ x, π (G x) = π x ^ p) (k : ℤ)
    (x : ExteriorAlgebra S Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p G hG hker (k • x) =
      k • frobeniusLiftExterior y hy π hπ p G hG hker x := by
  simp only [frobeniusLiftExterior, map_zsmul]
  rfl

theorem frobeniusLiftExterior_zero (G : L →+* L) (hG : ∀ x, π (G x) = π x ^ p) :
    frobeniusLiftExterior y hy π hπ p G hG hker 0 = 0 := by
  simp only [frobeniusLiftExterior, map_zero]
  rfl

theorem span_ιMulti_mem (b : ℕ) (x : ⋀[S]^b Ω[S⁄K]) :
    x ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S b)) := by
  rw [exteriorPower.ιMulti_span]
  trivial

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)

include hann hp2 in
/-- **Every value of the Deligne–Illusie map on `b`-forms is a `D`-cocycle.** -/
theorem seqTotalD_diSeqAlt [Algebra.FiniteType K S]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p) (b : ℕ)
    (x : ⋀[S]^b Ω[S⁄K]) :
    seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom
      (twistedPiHom K S p J (diSeqAlt y hy π hπ p F hF hker b x)) = 0 := by
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [← seqTotalDHom_apply, diSeqAlt_ιMulti, map_sum, map_sum]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, map_zsmul, seqTotalDHom_apply,
      show seqTotalD (kaehlerDeRhamDiff y hy).toAddMonoidHom (twistedPiHom K S p J
        (diSeqMultilinear y hy π hπ p F hF hker b fun i => ω (σ i))) = 0 from
        funext fun c => funext fun s => seqTotalD_diSeqProd y hy π hπ p F hF hker hann hp2 hK _ c s,
      smul_zero]
  | zero => rw [map_zero, map_zero, ← seqTotalDHom_apply, map_zero]
  | add x z _ _ hx hz =>
    rw [map_add, map_add, ← seqTotalDHom_apply, map_add, seqTotalDHom_apply, seqTotalDHom_apply,
      hx, hz, add_zero]
  | smul f x _ hx =>
    rw [map_smul, twistedPiHom_smul]
    funext c s
    rw [seqTotalD_frobenius_smul, hx, Pi.zero_apply, Pi.zero_apply, smul_zero]

theorem seqTotalHomogeneous_diSeqMultilinear (b : ℕ) (m : Fin b → Ω[S⁄K]) :
    SeqTotalHomogeneous b (twistedPiHom K S p J (diSeqMultilinear y hy π hπ p F hF hker b m)) := by
  have h := seqTotalHomogeneous_diSeqProd y hy π hπ p F hF hker (List.ofFn m)
  rwa [List.length_ofFn] at h

/-- **The component of Čech degree `a` of every value is a `(b - a)`-form**, zero for `a > b`. -/
theorem seqTotalHomogeneous_diSeqAlt (b : ℕ) (x : ⋀[S]^b Ω[S⁄K]) :
    SeqTotalHomogeneous b (twistedPiHom K S p J (diSeqAlt y hy π hπ p F hF hker b x)) := by
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [diSeqAlt_ιMulti, map_sum]
    refine Finset.sum_induction _ (SeqTotalHomogeneous b) (fun _ _ => seqTotalHomogeneous_add)
      (seqTotalHomogeneous_zero b) fun σ _ => ?_
    rw [Units.smul_def, map_zsmul]
    exact seqTotalHomogeneous_zsmul _ (seqTotalHomogeneous_diSeqMultilinear y hy π hπ p F hF hker b _)
  | zero =>
    rw [map_zero, map_zero]
    exact seqTotalHomogeneous_zero b
  | add x z _ _ hx hz =>
    rw [map_add, map_add]
    exact seqTotalHomogeneous_add hx hz
  | smul f x _ hx =>
    rw [map_smul, twistedPiHom_smul]
    exact seqTotalHomogeneous_smul (f ^ p) hx

/-- **The component of Čech degree `0` is `b! · Φ_{F_{s 0}}`.** -/
theorem diSeqAlt_zero (b : ℕ) (x : ⋀[S]^b Ω[S⁄K]) (s : ℕ → J) :
    twistedPiHom K S p J (diSeqAlt y hy π hπ p F hF hker b x) 0 s =
      (b.factorial : ℤ) • frobeniusLiftExterior y hy π hπ p (F (s 0)) (hF (s 0)) hker
        (x : ExteriorAlgebra S Ω[S⁄K]) := by
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [diSeqAlt_ιMulti, map_sum, Finset.sum_apply, Finset.sum_apply]
    have hterm : ∀ σ : Equiv.Perm (Fin b),
        twistedPiHom K S p J (Equiv.Perm.sign σ •
          diSeqMultilinear y hy π hπ p F hF hker b fun i => ω (σ i)) 0 s =
          frobeniusLiftExterior y hy π hπ p (F (s 0)) (hF (s 0)) hker
            (exteriorPower.ιMulti S b ω : ExteriorAlgebra S Ω[S⁄K]) := by
      intro σ
      rw [Units.smul_def, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      have h1 : twistedPiHom K S p J (diSeqMultilinear y hy π hπ p F hF hker b fun i => ω (σ i)) 0 s
          = frobeniusLiftExterior y hy π hπ p (F (s 0)) (hF (s 0)) hker
            (ExteriorAlgebra.ιMulti S b fun i => ω (σ i)) := by
        have hl : (List.ofFn fun i => ExteriorAlgebra.ι S (ω (σ i))) =
            (List.ofFn fun i => ω (σ i)).map (ExteriorAlgebra.ι S) := List.map_ofFn.symm
        rw [ExteriorAlgebra.ιMulti_apply, hl]
        exact diSeqProd_zero_eq_frobeniusLiftExterior y hy π hπ p F hF hker _ s
      rw [h1, show (fun i => ω (σ i)) = ω ∘ σ from rfl, AlternatingMap.map_perm,
        Units.smul_def, frobeniusLiftExterior_zsmul, smul_smul, ← Units.val_mul,
        Int.units_mul_self, Units.val_one, one_smul, exteriorPower.ιMulti_apply_coe]
    rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, natCast_zsmul]
  | zero =>
    rw [map_zero, map_zero, Submodule.coe_zero, frobeniusLiftExterior_zero, smul_zero]
    rfl
  | add x z _ _ hx hz =>
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hz, Submodule.coe_add,
      frobeniusLiftExterior_add, smul_add]
  | smul f x _ hx =>
    rw [map_smul, twistedPiHom_smul]
    dsimp only
    rw [hx, Submodule.coe_smul, frobeniusLiftExterior_smul, smul_comm]

end MixedFujita
