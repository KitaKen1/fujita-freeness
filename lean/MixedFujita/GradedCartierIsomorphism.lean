/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeRhamExteriorDegree

/-!
The Cartier isomorphisms of an étale chart degree by degree (step 10).

The projections of the exterior algebra onto the `b`-forms (`formsProj`, Mathlib's grading of the
exterior algebra) commute with every additive map preserving the degrees
(`formsProj_map_of_preserves`), and the de Rham differential shifts them
(`formsProj_succ_kaehlerDeRhamDiff`, `formsProj_zero_kaehlerDeRhamDiff`). So if every cocycle `z` is
`Φ ω` plus a coboundary for a unique `ω`, with `Φ` preserving degrees, then for a `b`-cocycle the
form `ω` is a `b`-form and the coboundary is the differential of a `(b - 1)`-form
(`graded_cartier_refine`).

Applied to the inverse Cartier operator (check-402) and to the Deligne–Illusie map of a Frobenius
lift (check-408): every closed `b`-form of an étale chart is `C⁻¹ ω + dη` (resp. `Φ_F ω + dη`) with
`ω` a `b`-form and `η` a `(b - 1)`-form (`kaehler_cartier_isomorphism_deg`,
`frobeniusLift_cartier_isomorphism_deg`), and `C⁻¹ ω` (resp. `Φ_F ω`) is exact only for `ω = 0`
(`kaehlerInverseCartier_eq_zero_of_mem_range`, `frobeniusLiftExterior_eq_zero_of_mem_range`): the
Cartier isomorphism `H^b(Ω^•) ≅ Ω^b` degree by degree.
-/

@[expose] public section

namespace MixedFujita

universe u v w

section Projection

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

/-- The projection of the exterior algebra onto the `b`-forms. -/
noncomputable abbrev formsProj (b : ℕ) :
    ExteriorAlgebra S Ω[S⁄K] →ₗ[S] ExteriorAlgebra S Ω[S⁄K] :=
  GradedAlgebra.proj (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) b

theorem formsProj_of_mem_same {b : ℕ} {x : ExteriorAlgebra S Ω[S⁄K]}
    (hx : x ∈ ⋀[S]^b Ω[S⁄K]) : formsProj b x = x := by
  rw [GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) hx]

theorem formsProj_of_mem_ne {i b : ℕ} {x : ExteriorAlgebra S Ω[S⁄K]}
    (hx : x ∈ ⋀[S]^i Ω[S⁄K]) (h : i ≠ b) : formsProj b x = 0 := by
  rw [GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) hx h]

theorem formsProj_mem (b : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]) :
    formsProj b x ∈ ⋀[S]^b Ω[S⁄K] := by
  rw [GradedAlgebra.proj_apply]
  exact SetLike.coe_mem _

theorem mem_exteriorPower_iff_formsProj (b : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]) :
    x ∈ ⋀[S]^b Ω[S⁄K] ↔ formsProj b x = x :=
  ⟨formsProj_of_mem_same, fun h => h ▸ formsProj_mem b x⟩

/-- **An additive map preserving the degrees commutes with the projections.** -/
theorem formsProj_map_of_preserves (Φ : ExteriorAlgebra S Ω[S⁄K] →+ ExteriorAlgebra S Ω[S⁄K])
    (hΦ : ∀ (i : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]), x ∈ ⋀[S]^i Ω[S⁄K] → Φ x ∈ ⋀[S]^i Ω[S⁄K])
    (b : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]) : formsProj b (Φ x) = Φ (formsProj b x) := by
  refine DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro i m
    by_cases hib : i = b
    · subst hib
      rw [formsProj_of_mem_same (hΦ i _ m.2), formsProj_of_mem_same m.2]
    · rw [formsProj_of_mem_ne (hΦ i _ m.2) hib, formsProj_of_mem_ne m.2 hib, map_zero]
  · intro m m' hm hm'
    rw [map_add, map_add, map_add, map_add, hm, hm']

variable {n : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The de Rham differential shifts the projections. -/
theorem formsProj_succ_kaehlerDeRhamDiff (b : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]) :
    formsProj (b + 1) (kaehlerDeRhamDiff y hy x) = kaehlerDeRhamDiff y hy (formsProj b x) := by
  refine DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro i m
    by_cases hib : i = b
    · subst hib
      rw [formsProj_of_mem_same (kaehlerDeRhamDiff_mem_exteriorPower y hy m.2),
        formsProj_of_mem_same m.2]
    · rw [formsProj_of_mem_ne (kaehlerDeRhamDiff_mem_exteriorPower y hy m.2) (by omega),
        formsProj_of_mem_ne m.2 hib, map_zero]
  · intro m m' hm hm'
    rw [map_add, map_add, map_add, map_add, hm, hm']

theorem formsProj_zero_kaehlerDeRhamDiff (x : ExteriorAlgebra S Ω[S⁄K]) :
    formsProj 0 (kaehlerDeRhamDiff y hy x) = 0 := by
  refine DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[S]^i Ω[S⁄K]) ?_ ?_ ?_ x
  · rw [map_zero, map_zero]
  · intro i m
    exact formsProj_of_mem_ne (kaehlerDeRhamDiff_mem_exteriorPower y hy m.2) (by omega)
  · intro m m' hm hm'
    rw [map_add, map_add, hm, hm', add_zero]

/-- **Graded refinement of a Cartier-type isomorphism.** -/
theorem graded_cartier_refine (Φ : ExteriorAlgebra S Ω[S⁄K] →+ ExteriorAlgebra S Ω[S⁄K])
    (hΦ : ∀ (i : ℕ) (x : ExteriorAlgebra S Ω[S⁄K]), x ∈ ⋀[S]^i Ω[S⁄K] → Φ x ∈ ⋀[S]^i Ω[S⁄K])
    {b : ℕ} {z : ExteriorAlgebra S Ω[S⁄K]} (hzb : z ∈ ⋀[S]^b Ω[S⁄K])
    {ω : ExteriorAlgebra S Ω[S⁄K]} (hω : z - Φ ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy))
    (huniq : ∀ ω', z - Φ ω' ∈ LinearMap.range (kaehlerDeRhamDiff y hy) → ω' = ω) :
    ω ∈ ⋀[S]^b Ω[S⁄K] ∧ ∃ η, η ∈ ⋀[S]^(b - 1) Ω[S⁄K] ∧ (b = 0 → η = 0) ∧
      z - Φ ω = kaehlerDeRhamDiff y hy η := by
  obtain ⟨η, hη⟩ := hω
  have hproj : formsProj b (kaehlerDeRhamDiff y hy η) = z - Φ (formsProj b ω) := by
    rw [hη, map_sub, formsProj_of_mem_same hzb, formsProj_map_of_preserves Φ hΦ]
  cases b with
  | zero =>
    have h0 : z - Φ (formsProj 0 ω) = 0 := by
      rw [← hproj, formsProj_zero_kaehlerDeRhamDiff]
    have hω' := huniq (formsProj 0 ω) ⟨0, by rw [map_zero, h0]⟩
    refine ⟨(mem_exteriorPower_iff_formsProj 0 ω).mpr hω', 0, Submodule.zero_mem _,
      fun _ => rfl, ?_⟩
    rw [map_zero, ← hω', h0]
  | succ k =>
    have h1 : z - Φ (formsProj (k + 1) ω) = kaehlerDeRhamDiff y hy (formsProj k η) := by
      rw [← hproj, formsProj_succ_kaehlerDeRhamDiff]
    have hω' := huniq (formsProj (k + 1) ω) ⟨formsProj k η, h1.symm⟩
    refine ⟨(mem_exteriorPower_iff_formsProj (k + 1) ω).mpr hω', formsProj k η,
      formsProj_mem k η, fun h => absurd h (Nat.succ_ne_zero k), ?_⟩
    rw [← hω', h1]

/-- Uniqueness with `z = 0`: `Φ ω` is exact only for `ω = 0`. -/
theorem eq_zero_of_cartier_unique (Φ : ExteriorAlgebra S Ω[S⁄K] →+ ExteriorAlgebra S Ω[S⁄K])
    (huniq : ∃! ω : ExteriorAlgebra S Ω[S⁄K],
      0 - Φ ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy))
    (ω : ExteriorAlgebra S Ω[S⁄K]) (h : Φ ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy)) :
    ω = 0 := by
  obtain ⟨ω₀, _, hu⟩ := huniq
  have h1 : ω = ω₀ := hu ω (show 0 - Φ ω ∈ _ by rw [zero_sub]; exact Submodule.neg_mem _ h)
  have h2 : (0 : ExteriorAlgebra S Ω[S⁄K]) = ω₀ :=
    hu 0 (show 0 - Φ 0 ∈ _ by rw [map_zero, sub_zero]; exact Submodule.zero_mem _)
  rw [h1, h2]

end Projection

section Cartier

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The inverse Cartier operator as an additive map. -/
noncomputable def inverseCartierAddHom :
    ExteriorAlgebra S Ω[S⁄K] →+ ExteriorAlgebra S Ω[S⁄K] :=
  AddMonoidHom.mk' (kaehlerInverseCartier y hy p) (kaehlerInverseCartier_add y hy p)

theorem inverseCartierAddHom_apply (ω : ExteriorAlgebra S Ω[S⁄K]) :
    inverseCartierAddHom y hy p ω = kaehlerInverseCartier y hy p ω := rfl

/-- **The Cartier isomorphism of an étale chart in degree `b`**: a closed `b`-form is `C⁻¹ ω + dη`
with `ω` a `b`-form and `η` a `(b - 1)`-form. -/
theorem kaehler_cartier_isomorphism_deg [PerfectRing K p] [Algebra.FiniteType K S] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) {b : ℕ} (z : ExteriorAlgebra S Ω[S⁄K])
    (hzb : z ∈ ⋀[S]^b Ω[S⁄K]) (hz : kaehlerDeRhamDiff y hy z = 0) :
    ∃ ω ∈ ⋀[S]^b Ω[S⁄K], ∃ η ∈ ⋀[S]^(b - 1) Ω[S⁄K],
      z - kaehlerInverseCartier y hy p ω = kaehlerDeRhamDiff y hy η := by
  obtain ⟨ω, hω, huniq⟩ := kaehler_cartier_isomorphism y hy p hy0 z hz
  obtain ⟨hωb, η, hηb, -, hη⟩ := graded_cartier_refine y hy (inverseCartierAddHom y hy p)
    (fun _ _ hx => kaehlerInverseCartier_mem_exteriorPower y hy p hx) hzb hω huniq
  exact ⟨ω, hωb, η, hηb, hη⟩

/-- `C⁻¹ ω` is exact only for `ω = 0`. -/
theorem kaehlerInverseCartier_eq_zero_of_mem_range [PerfectRing K p] [Algebra.FiniteType K S]
    [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (ω : ExteriorAlgebra S Ω[S⁄K])
    (h : kaehlerInverseCartier y hy p ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy)) : ω = 0 :=
  eq_zero_of_cartier_unique y hy (inverseCartierAddHom y hy p)
    (kaehler_cartier_isomorphism y hy p hy0 0 (map_zero _)) ω h

variable {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π)
  (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p)

/-- The Deligne–Illusie map of a Frobenius lift as an additive map. -/
noncomputable def frobeniusLiftAddHom :
    ExteriorAlgebra S Ω[S⁄K] →+ ExteriorAlgebra S Ω[S⁄K] :=
  AddMonoidHom.mk' (frobeniusLiftExterior y hy π hπ p F hF hker)
    (frobeniusLiftExterior_add y hy π hπ p F hF hker)

include hann hp2 hK in
/-- **The Deligne–Illusie map is a quasi-isomorphism of an étale chart in degree `b`**: a closed
`b`-form is `Φ_F ω + dη` with `ω` a `b`-form and `η` a `(b - 1)`-form. -/
theorem frobeniusLift_cartier_isomorphism_deg [PerfectRing K p] [Algebra.FiniteType K S]
    [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) {b : ℕ} (z : ExteriorAlgebra S Ω[S⁄K])
    (hzb : z ∈ ⋀[S]^b Ω[S⁄K]) (hz : kaehlerDeRhamDiff y hy z = 0) :
    ∃ ω ∈ ⋀[S]^b Ω[S⁄K], ∃ η ∈ ⋀[S]^(b - 1) Ω[S⁄K],
      z - frobeniusLiftExterior y hy π hπ p F hF hker ω = kaehlerDeRhamDiff y hy η := by
  obtain ⟨ω, hω, huniq⟩ :=
    frobeniusLift_cartier_isomorphism y hy π hπ p F hF hker hann hp2 hK hy0 z hz
  obtain ⟨hωb, η, hηb, -, hη⟩ := graded_cartier_refine y hy
    (frobeniusLiftAddHom y hy p π hπ F hF hker)
    (fun _ _ hx => frobeniusLiftExterior_mem_exteriorPower y hy π hπ p F hF hker hx) hzb hω huniq
  exact ⟨ω, hωb, η, hηb, hη⟩

include hann hp2 hK in
/-- `Φ_F ω` is exact only for `ω = 0`. -/
theorem frobeniusLiftExterior_eq_zero_of_mem_range [PerfectRing K p] [Algebra.FiniteType K S]
    [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (ω : ExteriorAlgebra S Ω[S⁄K])
    (h : frobeniusLiftExterior y hy π hπ p F hF hker ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy)) :
    ω = 0 :=
  eq_zero_of_cartier_unique y hy (frobeniusLiftAddHom y hy p π hπ F hF hker)
    (frobeniusLift_cartier_isomorphism y hy π hπ p F hF hker hann hp2 hK hy0 0 (map_zero _)) ω h

end Cartier

end MixedFujita
