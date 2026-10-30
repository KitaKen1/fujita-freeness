/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InverseCartierMultiplicative

/-!
The Cartier isomorphism of an étale chart does not depend on the coordinates (step 10).

Let `S` be a domain of finite type over a field `K` of characteristic `p`, with two systems of
nonzero formally étale coordinates `y` and `z`. The inverse Cartier operators `C⁻¹_y`, `C⁻¹_z`
on `⋀_S Ω[S⁄K]` differ by exact forms in every degree (`kaehlerInverseCartier_coordinate_independent`).
In degree one this is check-404. In general, the forms `ω` with `C⁻¹_y ω - C⁻¹_z ω` exact contain
`1` and are stable under `f ·` (`C⁻¹(f ω) = f^p C⁻¹ω`, and exact forms are stable under `p`-th
powers) and under `dg ∧ ·`: with `C⁻¹` multiplicative (check-405),
`C⁻¹_y(dg ω) - C⁻¹_z(dg ω) = (C⁻¹_y dg - C⁻¹_z dg) C⁻¹_y ω + C⁻¹_z(dg) (C⁻¹_y ω - C⁻¹_z ω)`;
the first term is `dξ ∧ (closed)`, exact by `d(ξ η) = dξ ∧ η` for closed `η`
(`kaehlerDeRhamDiff_mul_of_closed`); the second is `(closed 1-form) ∧ dβ`, exact by
`c ∧ dβ = -d(c ∧ β)` for closed `1`-forms `c` (`kaehlerDeRhamDiff_one_form_mul`).

Over a perfect field the Cartier operator `H(⋀_S Ω) → ⋀_S Ω` of an étale chart is therefore
canonical (`kaehler_cartier_operator_coordinate_independent`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

section Leibniz

/-- Induction over `⋀_S Ω[S⁄K]` by left multiplication with functions and exact `1`-forms. -/
theorem kaehlerExterior_mul_induction (P : ExteriorAlgebra S Ω[S⁄K] → Prop) (h1 : P 1)
    (hsmul : ∀ (f : S) ω, P ω → P (f • ω))
    (hD : ∀ (g : S) ω, P ω → P (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω))
    (hadd : ∀ ω ω', P ω → P ω' → P (ω + ω')) (h0 : P 0) (x : ExteriorAlgebra S Ω[S⁄K]) : P x := by
  have hι : ∀ v : Ω[S⁄K], ∀ ω, P ω → P (ExteriorAlgebra.ι S v * ω) := by
    intro v
    have hv : v ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      exact hD g
    | zero =>
      intro ω _
      rw [map_zero, zero_mul]
      exact h0
    | add v w _ _ hv hw =>
      intro ω h
      rw [map_add, add_mul]
      exact hadd _ _ (hv ω h) (hw ω h)
    | smul a v _ hv =>
      intro ω h
      rw [map_smul, smul_mul_assoc]
      exact hsmul a _ (hv ω h)
  have hall : ∀ a : ExteriorAlgebra S Ω[S⁄K], ∀ ω, P ω → P (a * ω) := by
    intro a
    induction a using ExteriorAlgebra.induction with
    | algebraMap f =>
      intro ω h
      rw [← Algebra.smul_def]
      exact hsmul f ω h
    | ι v => exact hι v
    | mul a b ha hb =>
      intro ω h
      rw [mul_assoc]
      exact ha _ (hb ω h)
    | add a b ha hb =>
      intro ω h
      rw [add_mul]
      exact hadd _ _ (ha ω h) (hb ω h)
  have := hall x 1 h1
  rwa [mul_one] at this

/-- `d(ξ ∧ η) = dξ ∧ η` when `η` is closed. -/
theorem kaehlerDeRhamDiff_mul_of_closed (ξ η : ExteriorAlgebra S Ω[S⁄K])
    (hη : kaehlerDeRhamDiff y hy η = 0) :
    kaehlerDeRhamDiff y hy (ξ * η) = kaehlerDeRhamDiff y hy ξ * η := by
  induction ξ using kaehlerExterior_mul_induction with
  | h1 => rw [one_mul, hη, kaehlerDeRhamDiff_one, zero_mul]
  | hsmul f ω h =>
    rw [smul_mul_assoc, kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_smul, h, add_mul, smul_mul_assoc,
      mul_assoc]
  | hD g ω h =>
    rw [mul_assoc, kaehlerDeRhamDiff_exact_mul, kaehlerDeRhamDiff_exact_mul, h, neg_mul, mul_assoc]
  | hadd ω ω' h h' => rw [add_mul, map_add, map_add, h, h', add_mul]
  | h0 => rw [zero_mul, map_zero, zero_mul]

/-- `ι(x) ∧ dβ + d(ι(x) ∧ β) = dι(x) ∧ β` for every `1`-form. -/
theorem kaehlerDeRhamDiff_one_form_mul (x : Ω[S⁄K]) (β : ExteriorAlgebra S Ω[S⁄K]) :
    ExteriorAlgebra.ι S x * kaehlerDeRhamDiff y hy β + kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S x * β) =
      kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S x) * β := by
  have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    have h1 : kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) = 0 := by
      have := kaehlerDeRhamDiff_exact_mul y hy g 1
      rwa [mul_one, kaehlerDeRhamDiff_one, mul_zero, neg_zero] at this
    rw [kaehlerDeRhamDiff_exact_mul, h1, zero_mul, add_neg_cancel]
  | zero => simp only [map_zero, zero_mul, add_zero]
  | add v w _ _ hv hw =>
    rw [map_add, add_mul, add_mul, map_add, map_add, add_mul, ← hv, ← hw]
    abel
  | smul a v _ hv =>
    rw [map_smul, smul_mul_assoc, smul_mul_assoc, kaehlerDeRhamDiff_smul, kaehlerDeRhamDiff_smul,
      add_mul, smul_mul_assoc, ← hv, mul_assoc]
    rw [smul_add]
    abel

/-- Exact forms are stable under multiplication by `p`-th powers. -/
theorem kaehler_pow_smul_mem_range (p : ℕ) [CharP K p] (a : S) {η : ExteriorAlgebra S Ω[S⁄K]}
    (hη : η ∈ LinearMap.range (kaehlerDeRhamDiff y hy)) :
    a ^ p • η ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
  obtain ⟨ξ, rfl⟩ := hη
  refine ⟨a ^ p • ξ, ?_⟩
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  have hD : KaehlerDifferential.D K S (a ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, hpS, zero_smul]
  rw [kaehlerDeRhamDiff_smul, hD, map_zero, zero_mul, zero_add]

/-- The values of the inverse Cartier operator are closed. -/
theorem kaehlerInverseCartier_closed (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra.FiniteType K S]
    [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (kaehlerInverseCartier y hy p ω) = 0 := by
  rw [kaehlerDeRhamDiff_apply, kaehlerInverseCartier, AlgEquiv.symm_apply_apply,
    etaleInverseCartier_cocycle y hy p hy0, map_zero]

end Leibniz

section Independence

/-- **Coordinate independence of the inverse Cartier operator in all degrees.** -/
theorem kaehlerInverseCartier_coordinate_independent {m : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra.FiniteType K S] [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : MvPolynomial (Fin m) K →ₐ[K] S) (hz : z.toRingHom.FormallyEtale)
    (hz0 : ∀ j : Fin m, etaleCoordFun z j ≠ 0) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerInverseCartier y hy p ω - kaehlerInverseCartier z hz p ω ∈
      LinearMap.range (kaehlerDeRhamDiff y hy) := by
  have hdz : kaehlerDeRhamDiff z hz = kaehlerDeRhamDiff y hy := kaehlerDeRhamDiff_eq z hz y hy
  induction ω using kaehlerExterior_mul_induction with
  | h1 =>
    rw [kaehlerInverseCartier_one, kaehlerInverseCartier_one, sub_self]
    exact Submodule.zero_mem _
  | hsmul f ω h =>
    rw [kaehlerInverseCartier_smul, kaehlerInverseCartier_smul, ← smul_sub]
    exact kaehler_pow_smul_mem_range y hy p f h
  | hD g ω h =>
    rw [kaehlerInverseCartier_mul, kaehlerInverseCartier_mul]
    obtain ⟨ξ, hξ⟩ := kaehlerInverseCartier_D_coordinate_independent y hy p z hz g
    obtain ⟨β, hβ⟩ := h
    have heq : kaehlerInverseCartier y hy p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) *
          kaehlerInverseCartier y hy p ω -
        kaehlerInverseCartier z hz p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) *
          kaehlerInverseCartier z hz p ω =
        kaehlerDeRhamDiff y hy ξ * kaehlerInverseCartier y hy p ω +
          kaehlerInverseCartier z hz p (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) *
            kaehlerDeRhamDiff y hy β := by
      rw [hξ, hβ]
      noncomm_ring
    rw [heq]
    refine Submodule.add_mem _ ⟨ξ * kaehlerInverseCartier y hy p ω, ?_⟩ ?_
    · exact kaehlerDeRhamDiff_mul_of_closed y hy _ _ (kaehlerInverseCartier_closed y hy p hy0 ω)
    · rw [kaehlerInverseCartier_ι]
      have hc : kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S
          (inverseCartierOneFormAux z hz p (KaehlerDifferential.D K S g))) = 0 := by
        rw [← kaehlerInverseCartier_ι, ← hdz]
        exact kaehlerInverseCartier_closed z hz p hz0 _
      have h2 := kaehlerDeRhamDiff_one_form_mul y hy
        (inverseCartierOneFormAux z hz p (KaehlerDifferential.D K S g)) β
      rw [hc, zero_mul, add_eq_zero_iff_eq_neg] at h2
      rw [h2, ← map_neg]
      exact ⟨_, rfl⟩
  | hadd ω ω' h h' =>
    rw [kaehlerInverseCartier_add, kaehlerInverseCartier_add, add_sub_add_comm]
    exact Submodule.add_mem _ h h'
  | h0 =>
    have h0y : kaehlerInverseCartier y hy p 0 = 0 := by
      have := kaehlerInverseCartier_smul y hy p 0 0
      rwa [zero_smul, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul] at this
    have h0z : kaehlerInverseCartier z hz p 0 = 0 := by
      have := kaehlerInverseCartier_smul z hz p 0 0
      rwa [zero_smul, zero_pow (Fact.out : p.Prime).ne_zero, zero_smul] at this
    rw [h0y, h0z, sub_self]
    exact Submodule.zero_mem _

/-- **The Cartier operator of an étale chart is canonical.** Over a perfect field, the form `ω`
with `z₀ - C⁻¹ ω` exact attached to a cocycle `z₀` (check-402) is the same for all systems of
nonzero formally étale coordinates. -/
theorem kaehler_cartier_operator_coordinate_independent {m : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectRing K p] [Algebra.FiniteType K S] [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : MvPolynomial (Fin m) K →ₐ[K] S) (hz : z.toRingHom.FormallyEtale)
    (hz0 : ∀ j : Fin m, etaleCoordFun z j ≠ 0) (z₀ ω ω' : ExteriorAlgebra S Ω[S⁄K])
    (hω : z₀ - kaehlerInverseCartier y hy p ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy))
    (hω' : z₀ - kaehlerInverseCartier z hz p ω' ∈ LinearMap.range (kaehlerDeRhamDiff z hz)) :
    ω = ω' := by
  rw [kaehlerDeRhamDiff_eq z hz y hy] at hω'
  have hind := kaehlerInverseCartier_coordinate_independent y hy p hy0 z hz hz0 ω'
  have hc : kaehlerDeRhamDiff y hy (kaehlerInverseCartier y hy p ω') = 0 :=
    kaehlerInverseCartier_closed y hy p hy0 ω'
  obtain ⟨w, -, huniq⟩ := kaehler_cartier_isomorphism y hy p hy0 _ hc
  have h1 : ω' = w := huniq ω' (by
    show kaehlerInverseCartier y hy p ω' - kaehlerInverseCartier y hy p ω' ∈ _
    rw [sub_self]
    exact Submodule.zero_mem _)
  have h2 : ω = w := huniq ω (by
    show kaehlerInverseCartier y hy p ω' - kaehlerInverseCartier y hy p ω ∈ _
    have h := Submodule.add_mem _ (Submodule.sub_mem _ hind hω') hω
    have heq : kaehlerInverseCartier y hy p ω' - kaehlerInverseCartier z hz p ω' -
        (z₀ - kaehlerInverseCartier z hz p ω') + (z₀ - kaehlerInverseCartier y hy p ω) =
          kaehlerInverseCartier y hy p ω' - kaehlerInverseCartier y hy p ω := by
      abel
    rwa [heq] at h)
  rw [h1, h2]

end Independence

end MixedFujita
