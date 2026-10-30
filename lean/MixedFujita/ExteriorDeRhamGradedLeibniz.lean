/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IndexNerveLeibniz
public import MixedFujita.CartierCoordinateIndependence

/-!
The graded Leibniz rule of the de Rham differential of an étale chart (step 10).

On `⋀_S Ω[S⁄K]` of an étale chart, the grade involution `σ` (Mathlib's
`CliffordAlgebra.involute`, as a ring homomorphism, `exteriorInvolute`) and the de Rham
differential `d` (check 402) satisfy `d(x y) = d x · y + σ x · d y` (`kaehlerDeRhamDiff_mul`) and
`d ∘ σ = -σ ∘ d` (`kaehlerDeRhamDiff_exteriorInvolute`), by the induction over functions and exact
`1`-forms of check 406; and `σ ∘ σ = id`. These are the hypotheses of the graded cup product of
check 447, so the cup product on the index nerve with values in the forms of a chart satisfies the
graded Leibniz rule.
-/

@[expose] public section

namespace MixedFujita

universe u v

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

variable (K S) in
/-- The grade involution of `⋀_S Ω[S⁄K]` as a ring homomorphism. -/
noncomputable def exteriorInvolute : ExteriorAlgebra S Ω[S⁄K] →+* ExteriorAlgebra S Ω[S⁄K] :=
  (CliffordAlgebra.involute (Q := (0 : QuadraticForm S Ω[S⁄K]))).toRingHom

theorem exteriorInvolute_apply (x : ExteriorAlgebra S Ω[S⁄K]) :
    exteriorInvolute K S x = CliffordAlgebra.involute (Q := (0 : QuadraticForm S Ω[S⁄K])) x := rfl

theorem exteriorInvolute_involute (x : ExteriorAlgebra S Ω[S⁄K]) :
    exteriorInvolute K S (exteriorInvolute K S x) = x :=
  CliffordAlgebra.involute_involute x

theorem exteriorInvolute_ι (v : Ω[S⁄K]) :
    exteriorInvolute K S (ExteriorAlgebra.ι S v) = -ExteriorAlgebra.ι S v :=
  CliffordAlgebra.involute_ι v

theorem exteriorInvolute_smul (f : S) (x : ExteriorAlgebra S Ω[S⁄K]) :
    exteriorInvolute K S (f • x) = f • exteriorInvolute K S x :=
  map_smul (CliffordAlgebra.involute (Q := (0 : QuadraticForm S Ω[S⁄K]))) f x

/-- **The graded Leibniz rule** `d(x y) = d x · y + σ x · d y`. -/
theorem kaehlerDeRhamDiff_mul (x : ExteriorAlgebra S Ω[S⁄K]) : ∀ z : ExteriorAlgebra S Ω[S⁄K],
    kaehlerDeRhamDiff y hy (x * z) =
      kaehlerDeRhamDiff y hy x * z + exteriorInvolute K S x * kaehlerDeRhamDiff y hy z := by
  refine kaehlerExterior_mul_induction (K := K) (fun x => ∀ z, kaehlerDeRhamDiff y hy (x * z) =
      kaehlerDeRhamDiff y hy x * z + exteriorInvolute K S x * kaehlerDeRhamDiff y hy z)
    ?_ ?_ ?_ ?_ ?_ x
  · intro z
    rw [one_mul, kaehlerDeRhamDiff_one, zero_mul, zero_add, map_one, one_mul]
  · intro f ω ih z
    rw [smul_mul_assoc, kaehlerDeRhamDiff_smul, ih, kaehlerDeRhamDiff_smul, exteriorInvolute_smul,
      add_mul, smul_add, mul_assoc, smul_mul_assoc, smul_mul_assoc, add_assoc]
  · intro g ω ih z
    rw [mul_assoc, kaehlerDeRhamDiff_exact_mul, ih, kaehlerDeRhamDiff_exact_mul, map_mul,
      exteriorInvolute_ι]
    noncomm_ring
  · intro ω ω' h h' z
    rw [add_mul, map_add, h, h', map_add, map_add, add_mul, add_mul]
    abel
  · intro z
    rw [zero_mul, map_zero, zero_mul, map_zero, zero_mul, add_zero]

/-- **`d ∘ σ = -σ ∘ d`.** -/
theorem kaehlerDeRhamDiff_exteriorInvolute (x : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (exteriorInvolute K S x) =
      -exteriorInvolute K S (kaehlerDeRhamDiff y hy x) := by
  refine kaehlerExterior_mul_induction (K := K) (fun x => kaehlerDeRhamDiff y hy
      (exteriorInvolute K S x) = -exteriorInvolute K S (kaehlerDeRhamDiff y hy x))
    ?_ ?_ ?_ ?_ ?_ x
  · rw [map_one, kaehlerDeRhamDiff_one, map_zero, neg_zero]
  · intro f ω ih
    rw [exteriorInvolute_smul, kaehlerDeRhamDiff_smul, ih, kaehlerDeRhamDiff_smul, map_add,
      map_mul, exteriorInvolute_ι, exteriorInvolute_smul, smul_neg, neg_add, neg_mul, neg_neg]
  · intro g ω ih
    rw [map_mul, exteriorInvolute_ι, neg_mul, map_neg, kaehlerDeRhamDiff_exact_mul, ih,
      kaehlerDeRhamDiff_exact_mul, map_neg, map_mul, exteriorInvolute_ι]
    noncomm_ring
  · intro ω ω' h h'
    rw [map_add, map_add, h, h', map_add, map_add, neg_add]
  · rw [map_zero, map_zero, map_zero, neg_zero]

end MixedFujita
