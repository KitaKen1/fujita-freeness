/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericSmoothSpreading
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
Spreading out étale coordinates (step 10, R4-3).

Let `y : K[Y₁, …, Y_d] → C` be étale and let `C` be generated over the image of `y` by a finite
set `γ`. There is a finitely generated subring `A₀ ⊆ K` such that for every subring `A ⊇ A₀`, every
ring `M` with `ψ : A[Y₁, …, Y_d] → M` and an injective `ρ : M → C` compatible with `y`, generated
over the image of `ψ` by `ρ⁻¹(γ)` and with image containing `γ`, has `ψ` étale
(`exists_fg_forall_etale_of_injective`).

This is check 505 for the base `ℤ[Y] → K[Y]` in relative dimension zero: the polynomials over a
subring `A ⊆ K` form a `ℤ[Y]`-subalgebra of `K[Y]`, which contains a given finitely generated one
once `A` contains finitely many coefficients; the conclusion is transported along
`A[Y] ≅ (its image in K[Y])`. In the application `C` is the ring of a simple normal crossing chart
of `T_K` with its étale coordinates, and `M` that of the same chart of the closure `T_A`.
-/

@[expose] public section

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {C : Type u} [CommRing C] (d : ℕ)

/-- **Spreading out étale coordinates.** -/
theorem exists_fg_forall_etale_of_injective (y : MvPolynomial (Fin d) K →+* C) (hy : y.Etale)
    (γ : Finset C) (hγ : Subring.closure (Set.range y ∪ (γ : Set C)) = ⊤) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ A : Subalgebra ℤ K, A₀ ≤ A →
      ∀ (M : Type u) [CommRing M] (ψ : MvPolynomial (Fin d) A →+* M) (ρ : M →+* C),
        ρ.comp ψ = y.comp (MvPolynomial.map (algebraMap A K)) → Function.Injective ρ →
        (γ : Set C) ⊆ Set.range ρ → Subring.closure (Set.range ψ ∪ ρ ⁻¹' (γ : Set C)) = ⊤ →
        ψ.Etale := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℤ) (MvPolynomial (Fin d) K) :=
    MvPolynomial.algebraMvPolynomial
  let _ : Algebra (MvPolynomial (Fin d) K) C := y.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin d) K) C :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 hy
  have hγ' : Algebra.adjoin (MvPolynomial (Fin d) K) (γ : Set C) = ⊤ := by
    apply Subalgebra.toSubring_injective
    rw [Algebra.adjoin_eq_ring_closure, Algebra.top_toSubring]
    exact hγ
  obtain ⟨A₀', ⟨P, hP⟩, h⟩ :=
    exists_fg_forall_isStandardSmooth_of_injective (R := MvPolynomial (Fin d) ℤ) 0 γ hγ'
  let U : Finset K := P.biUnion fun p => p.coeffs
  refine ⟨Algebra.adjoin ℤ (U : Set K), ⟨U, rfl⟩, fun A hA => ?_⟩
  intro M _ ψ ρ hcomp hinj hγρ hgen
  let c := algebraMap A K
  have hc : Function.Injective (MvPolynomial.map (σ := Fin d) c) :=
    MvPolynomial.map_injective c Subtype.val_injective
  -- the polynomials over `A` as a subalgebra of the polynomials over `K`
  let A' : Subalgebra (MvPolynomial (Fin d) ℤ) (MvPolynomial (Fin d) K) :=
    { (MvPolynomial.map (σ := Fin d) c).range with
      algebraMap_mem' := fun r => ⟨MvPolynomial.map (algebraMap ℤ A) r, by
        change MvPolynomial.map c (MvPolynomial.map (algebraMap ℤ A) r) =
          MvPolynomial.map (algebraMap ℤ K) r
        rw [MvPolynomial.map_map]
        congr 1⟩ }
  have hA' : A₀' ≤ A' := by
    rw [← hP, Algebra.adjoin_le_iff]
    intro p hp
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.2 fun z hz => ?_
    exact ⟨⟨z, hA (Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨p, Finset.mem_coe.1 hp, hz⟩)))⟩, rfl⟩
  let eHom : MvPolynomial (Fin d) A →+* A' :=
    (MvPolynomial.map c).codRestrict A' fun p => ⟨p, rfl⟩
  have he : Function.Bijective eHom := by
    refine ⟨fun p q hpq => hc (congrArg Subtype.val hpq), ?_⟩
    rintro ⟨_, p, rfl⟩
    exact ⟨p, rfl⟩
  let e : MvPolynomial (Fin d) A ≃+* A' := RingEquiv.ofBijective eHom he
  let _ : Algebra A' M := (ψ.comp e.symm.toRingHom).toAlgebra
  have hcomp' : ρ.comp (algebraMap A' M) =
      (algebraMap (MvPolynomial (Fin d) K) C).comp (algebraMap A' (MvPolynomial (Fin d) K)) := by
    refine RingHom.ext fun a => ?_
    obtain ⟨p, rfl⟩ := e.surjective a
    change ρ (ψ (e.symm (e p))) = y (MvPolynomial.map c p)
    rw [e.symm_apply_apply]
    exact RingHom.congr_fun hcomp p
  have hadj : Algebra.adjoin A' (ρ ⁻¹' (γ : Set C)) = ⊤ := by
    apply Subalgebra.toSubring_injective
    rw [Algebra.adjoin_eq_ring_closure, Algebra.top_toSubring, ← hgen]
    congr 2
    ext m
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e.symm a, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨e p, by change ψ (e.symm (e p)) = ψ p; rw [e.symm_apply_apply]⟩
  have hsm := h A' hA' M ρ hcomp' hinj hγρ hadj
  let _ : Algebra (MvPolynomial (Fin d) A) A' := e.toRingHom.toAlgebra
  let _ : Algebra (MvPolynomial (Fin d) A) M := ψ.toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) A) A' M := IsScalarTower.of_algebraMap_eq fun p => by
    change ψ p = ψ (e.symm (e p))
    rw [e.symm_apply_apply]
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin d) A) A' :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective
  have : Algebra.IsStandardSmoothOfRelativeDimension (0 + 0) (MvPolynomial (Fin d) A) M :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 0 0 (MvPolynomial (Fin d) A) A' M
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.2 this

end MixedFujita
