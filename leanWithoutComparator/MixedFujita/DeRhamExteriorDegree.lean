/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FrobeniusLiftNaturality

/-!
Degrees in the intrinsic de Rham complex (step 10, the graded pieces `Ω^b`).

The maps of checks 402–412 are defined on the whole exterior algebra `⋀_S Ω[S⁄K]`. For the
Čech–de Rham double complex we need the graded pieces `⋀^b = (range ι)^b`:
* the de Rham differential maps `⋀^b` into `⋀^{b+1}` (`kaehlerDeRhamDiff_mem_exteriorPower`): the
  differential of a `1`-form is a `2`-form, and `d(ι v ∧ x) = dι v ∧ x - ι v ∧ dx`;
* the Deligne–Illusie map of a Frobenius lift and the inverse Cartier operator preserve `⋀^b`
  (`frobeniusLiftExterior_mem_exteriorPower`, `kaehlerInverseCartier_mem_exteriorPower`);
* the map induced by an algebra map preserves `⋀^b` (`kaehlerExteriorMap_mem_exteriorPower`).
The differential restricted to degree `b` is `kaehlerDeRhamDiffDeg b : ⋀^b → ⋀^{b+1}`, with
`d ∘ d = 0` in each degree (`kaehlerDeRhamDiffDeg_comp`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Degree

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

theorem ι_mul_mem_exteriorPower {v : Ω[S⁄K]} {b : ℕ}
    {x : ExteriorAlgebra S Ω[S⁄K]} (hx : x ∈ ⋀[S]^b Ω[S⁄K]) :
    ExteriorAlgebra.ι S v * x ∈ ⋀[S]^(b + 1) Ω[S⁄K] := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) hx

theorem ι_mem_exteriorPower_one (v : Ω[S⁄K]) :
    ExteriorAlgebra.ι S v ∈ ⋀[S]^1 Ω[S⁄K] := by
  rw [ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ v

variable {n : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The differential of a `1`-form is a `2`-form. -/
theorem kaehlerDeRhamDiff_ι_mem (v : Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S v) ∈ ⋀[S]^2 Ω[S⁄K] := by
  have hv : v ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    rw [kaehlerDeRhamDiff_ι_D]
    exact Submodule.zero_mem _
  | zero =>
    rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  | add v w _ _ hv hw =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hv hw
  | smul s v _ hv =>
    rw [map_smul, kaehlerDeRhamDiff_smul]
    exact Submodule.add_mem _ (ι_mul_mem_exteriorPower (ι_mem_exteriorPower_one v))
      (Submodule.smul_mem _ s hv)

/-- **The de Rham differential raises the degree by one.** -/
theorem kaehlerDeRhamDiff_mem_exteriorPower {b : ℕ} {x : ExteriorAlgebra S Ω[S⁄K]}
    (hx : x ∈ ⋀[S]^b Ω[S⁄K]) : kaehlerDeRhamDiff y hy x ∈ ⋀[S]^(b + 1) Ω[S⁄K] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_one, smul_zero,
      add_zero, mul_one]
    exact ι_mem_exteriorPower_one _
  | add x z i _ _ hx hz =>
    rw [map_add]
    exact Submodule.add_mem _ hx hz
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    have h := kaehlerDeRhamDiff_one_form_mul y hy v x
    have heq : kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S v * x) =
        kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S v) * x -
          ExteriorAlgebra.ι S v * kaehlerDeRhamDiff y hy x := by
      rw [← h]
      abel
    rw [heq]
    refine Submodule.sub_mem _ ?_ (ι_mul_mem_exteriorPower ih)
    have h2 : kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S v) * x ∈ ⋀[S]^(2 + i) Ω[S⁄K] := by
      rw [ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul (kaehlerDeRhamDiff_ι_mem y hy v) hx
    have he : i.succ + 1 = 2 + i := by omega
    rw [he]
    exact h2

/-- The de Rham differential in degree `b`, `⋀^b → ⋀^{b+1}`. -/
noncomputable def kaehlerDeRhamDiffDeg (b : ℕ) :
    (⋀[S]^b Ω[S⁄K]).restrictScalars K →ₗ[K] (⋀[S]^(b + 1) Ω[S⁄K]).restrictScalars K :=
  (kaehlerDeRhamDiff y hy).restrict fun _ hx => kaehlerDeRhamDiff_mem_exteriorPower y hy hx

theorem kaehlerDeRhamDiffDeg_apply (b : ℕ) (x : (⋀[S]^b Ω[S⁄K]).restrictScalars K) :
    (kaehlerDeRhamDiffDeg y hy b x : ExteriorAlgebra S Ω[S⁄K]) = kaehlerDeRhamDiff y hy x := rfl

/-- `d ∘ d = 0` in each degree. -/
theorem kaehlerDeRhamDiffDeg_comp (b : ℕ) :
    kaehlerDeRhamDiffDeg y hy (b + 1) ∘ₗ kaehlerDeRhamDiffDeg y hy b = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [LinearMap.comp_apply, kaehlerDeRhamDiffDeg_apply, kaehlerDeRhamDiffDeg_apply,
    LinearMap.zero_apply, Submodule.coe_zero]
  exact LinearMap.congr_fun (kaehlerDeRhamDiff_comp_self y hy) (x : ExteriorAlgebra S Ω[S⁄K])

end Degree

section Maps

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The inverse Cartier operator preserves the degree. -/
theorem kaehlerInverseCartier_mem_exteriorPower (p : ℕ) [Fact p.Prime] [CharP K p] {b : ℕ}
    {x : ExteriorAlgebra S Ω[S⁄K]} (hx : x ∈ ⋀[S]^b Ω[S⁄K]) :
    kaehlerInverseCartier y hy p x ∈ ⋀[S]^b Ω[S⁄K] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, kaehlerInverseCartier_smul, kaehlerInverseCartier_one,
      ← Algebra.algebraMap_eq_smul_one, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | add x z i _ _ hx hz =>
    rw [kaehlerInverseCartier_add]
    exact Submodule.add_mem _ hx hz
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [kaehlerInverseCartier_mul, kaehlerInverseCartier_ι]
    exact ι_mul_mem_exteriorPower ih

variable {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ)
  [Fact p.Prime] [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- The Deligne–Illusie map of a Frobenius lift preserves the degree. -/
theorem frobeniusLiftExterior_mem_exteriorPower {b : ℕ} {x : ExteriorAlgebra S Ω[S⁄K]}
    (hx : x ∈ ⋀[S]^b Ω[S⁄K]) :
    frobeniusLiftExterior y hy π hπ p F hF hker x ∈ ⋀[S]^b Ω[S⁄K] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, frobeniusLiftExterior_smul, frobeniusLiftExterior_one,
      ← Algebra.algebraMap_eq_smul_one, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | add x z i _ _ hx hz =>
    rw [frobeniusLiftExterior_add]
    exact Submodule.add_mem _ hx hz
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [frobeniusLiftExterior_mul, frobeniusLiftExterior_ι]
    exact ι_mul_mem_exteriorPower ih

end Maps

section Functorial

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]
  {T : Type w} [CommRing T] [Algebra K T] [Algebra S T] [IsScalarTower K S T]

/-- The map induced by an algebra map preserves the degree. -/
theorem kaehlerExteriorMap_mem_exteriorPower {b : ℕ} {x : ExteriorAlgebra S Ω[S⁄K]}
    (hx : x ∈ ⋀[S]^b Ω[S⁄K]) : kaehlerExteriorMap K S T x ∈ ⋀[T]^b Ω[T⁄K] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S T (ExteriorAlgebra T Ω[T⁄K]),
      ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | add x z i _ _ hx hz =>
    rw [map_add]
    exact Submodule.add_mem _ hx hz
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, kaehlerExteriorMap_ι]
    exact ι_mul_mem_exteriorPower ih

end Functorial

end MixedFujita
