/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InverseCartierCanonical

/-!
The inverse Cartier operator is multiplicative (step 10).

Let `S` be a `K`-algebra with formally étale coordinates `y`, `K` of characteristic `p`. On
`⋀_S Ω[S⁄K]` let `S` act through the Frobenius `a ↦ a^p` (`FrobeniusTwistedExterior`). The map
`ω ↦ ι(Σ_j ω_j^p y_j^{p-1} d y_j)` from `Ω[S⁄K]` is `S`-linear into this twisted algebra and squares
to zero, so it extends to a homomorphism of `S`-algebras (`kaehlerInverseCartierHom`): a ring
homomorphism of `⋀_S Ω[S⁄K]` with `C⁻¹(a ω) = a^p C⁻¹(ω)` and `C⁻¹(d y_j) = y_j^{p-1} d y_j`.

It agrees with the inverse Cartier operator of checks 401–402 (`kaehlerInverseCartierHom_eq`):
both are additive and Frobenius-semilinear, and on the basis `d y_s = d y_{s_1} ∧ ⋯ ∧ d y_{s_k}`
both give `y_s^{p-1} d y_s` (a list product of `y_j^{p-1} d y_j` is `Π_{j ∈ s} y_j^{p-1}` times
`d y_s`). Hence the inverse Cartier operator is multiplicative
(`kaehlerInverseCartier_mul`), which the coordinate formula does not show directly because of the
signs of `e_s ∧ e_t`.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

section Twist

variable (K S) in
/-- The Frobenius `a ↦ a^p` of a `K`-algebra, `K` of characteristic `p`, as a ring homomorphism. -/
noncomputable def algebraFrobenius (p : ℕ) [hp : Fact p.Prime] [CharP K p] : S →+* S where
  toFun a := a ^ p
  map_one' := one_pow p
  map_mul' a b := mul_pow a b p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' a b := add_pow_prime_of_natCast_eq_zero hp.out (natCast_char_eq_zero_of_algebra (K := K) p) a b

theorem algebraFrobenius_apply (p : ℕ) [Fact p.Prime] [CharP K p] (a : S) :
    algebraFrobenius K S p a = a ^ p := rfl

variable (K S) in
/-- `⋀_S Ω[S⁄K]` on which `S` acts through the Frobenius. -/
def FrobeniusTwistedExterior (_p : ℕ) : Type _ := ExteriorAlgebra S Ω[S⁄K]

noncomputable instance (p : ℕ) : Ring (FrobeniusTwistedExterior K S p) :=
  inferInstanceAs (Ring (ExteriorAlgebra S Ω[S⁄K]))

/-- The identity from the twisted exterior algebra. -/
def twistedToExterior {p : ℕ} (x : FrobeniusTwistedExterior K S p) :
    ExteriorAlgebra S Ω[S⁄K] := x

noncomputable instance (p : ℕ) [Fact p.Prime] [CharP K p] :
    Algebra S (FrobeniusTwistedExterior K S p) :=
  RingHom.toAlgebra' ((algebraMap S (ExteriorAlgebra S Ω[S⁄K])).comp (algebraFrobenius K S p))
    fun c x => Algebra.commutes (A := ExteriorAlgebra S Ω[S⁄K]) (algebraFrobenius K S p c) (twistedToExterior x)

theorem frobeniusTwisted_smul_eq (p : ℕ) [Fact p.Prime] [CharP K p] (c : S)
    (x : FrobeniusTwistedExterior K S p) :
    twistedToExterior (c • x) = c ^ p • twistedToExterior x := by
  change algebraMap S (ExteriorAlgebra S Ω[S⁄K]) (c ^ p) * twistedToExterior x = _
  rw [Algebra.smul_def]

end Twist

section Hom

variable {n : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- `ω ↦ Σ_j ω_j^p y_j^{p-1} d y_j` on `Ω[S⁄K]`. -/
noncomputable def inverseCartierOneFormAux (p : ℕ) (ω : Ω[S⁄K]) : Ω[S⁄K] :=
  ∑ j, ((etaleCoordinateBasis y hy).repr ω j ^ p * etaleCoordFun y j ^ (p - 1)) •
    etaleCoordinateBasis y hy j

theorem inverseCartierOneFormAux_add (p : ℕ) [hp : Fact p.Prime] [CharP K p] (ω η : Ω[S⁄K]) :
    inverseCartierOneFormAux y hy p (ω + η) =
      inverseCartierOneFormAux y hy p ω + inverseCartierOneFormAux y hy p η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [inverseCartierOneFormAux, map_add, Finsupp.add_apply,
    add_pow_prime_of_natCast_eq_zero hp.out hpS, add_mul, add_smul, Finset.sum_add_distrib]

theorem inverseCartierOneFormAux_smul (p : ℕ) (c : S) (ω : Ω[S⁄K]) :
    inverseCartierOneFormAux y hy p (c • ω) = c ^ p • inverseCartierOneFormAux y hy p ω := by
  simp only [inverseCartierOneFormAux, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_pow,
    Finset.smul_sum, smul_smul, mul_assoc]

theorem inverseCartierOneFormAux_basis (p : ℕ) [hp : Fact p.Prime] (j : Fin n) :
    inverseCartierOneFormAux y hy p (etaleCoordinateBasis y hy j) =
      etaleCoordFun y j ^ (p - 1) • etaleCoordinateBasis y hy j := by
  classical
  rw [inverseCartierOneFormAux, Finset.sum_eq_single j]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_pow, one_mul]
  · intro k _ hkj
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne' hkj.symm, zero_pow hp.out.ne_zero,
      zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The inverse Cartier operator on `1`-forms, `S`-linear into the twisted exterior algebra. -/
noncomputable def inverseCartierOneForm (p : ℕ) [Fact p.Prime] [CharP K p] :
    Ω[S⁄K] →ₗ[S] FrobeniusTwistedExterior K S p where
  toFun ω := ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω)
  map_add' ω η := by
    change ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p (ω + η)) =
      ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω) +
        ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p η)
    rw [inverseCartierOneFormAux_add, map_add]
  map_smul' c ω := by
    change ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p (c • ω)) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄K]) (c ^ p) *
        ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω)
    rw [inverseCartierOneFormAux_smul, map_smul, Algebra.smul_def]

/-- **The inverse Cartier operator as a ring homomorphism** of `⋀_S Ω[S⁄K]`. -/
noncomputable def kaehlerInverseCartierHom (p : ℕ) [Fact p.Prime] [CharP K p] :
    ExteriorAlgebra S Ω[S⁄K] →ₐ[S] FrobeniusTwistedExterior K S p :=
  ExteriorAlgebra.lift S ⟨inverseCartierOneForm y hy p, fun ω => by
    change ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω) *
      ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω) = 0
    exact ExteriorAlgebra.ι_sq_zero _⟩

theorem kaehlerInverseCartierHom_ι (p : ℕ) [Fact p.Prime] [CharP K p] (ω : Ω[S⁄K]) :
    twistedToExterior (kaehlerInverseCartierHom y hy p (ExteriorAlgebra.ι S ω)) =
      ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω) := by
  rw [kaehlerInverseCartierHom, ExteriorAlgebra.lift_ι_apply]
  rfl

theorem kaehlerInverseCartierHom_mul (p : ℕ) [Fact p.Prime] [CharP K p]
    (x x' : ExteriorAlgebra S Ω[S⁄K]) :
    twistedToExterior (kaehlerInverseCartierHom y hy p (x * x')) =
      twistedToExterior (kaehlerInverseCartierHom y hy p x) * twistedToExterior (kaehlerInverseCartierHom y hy p x') :=
  congrArg twistedToExterior (map_mul _ x x')

theorem kaehlerInverseCartierHom_add (p : ℕ) [Fact p.Prime] [CharP K p]
    (x x' : ExteriorAlgebra S Ω[S⁄K]) :
    twistedToExterior (kaehlerInverseCartierHom y hy p (x + x')) =
      twistedToExterior (kaehlerInverseCartierHom y hy p x) + twistedToExterior (kaehlerInverseCartierHom y hy p x') :=
  congrArg twistedToExterior (map_add _ x x')

theorem kaehlerInverseCartierHom_smul (p : ℕ) [Fact p.Prime] [CharP K p] (c : S)
    (x : ExteriorAlgebra S Ω[S⁄K]) :
    twistedToExterior (kaehlerInverseCartierHom y hy p (c • x)) =
      c ^ p • twistedToExterior (kaehlerInverseCartierHom y hy p x) := by
  rw [map_smul, frobeniusTwisted_smul_eq]

theorem kaehlerInverseCartierHom_one (p : ℕ) [Fact p.Prime] [CharP K p] :
    twistedToExterior (kaehlerInverseCartierHom y hy p 1) = 1 :=
  congrArg twistedToExterior (map_one _)

/-- A list product of `c_j • v_j` in an `S`-algebra. -/
theorem list_prod_map_smul {E : Type*} [Ring E] [Algebra S E] {ι : Type*} (l : List ι) (c : ι → S)
    (v : ι → E) : (l.map fun j => c j • v j).prod = (l.map c).prod • (l.map v).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      List.prod_cons, smul_mul_smul_comm]

/-- The monomial `y_s^{p-1}` is the product of `y_j^{p-1}` over the sorted list of `s`. -/
theorem cartierMonomial_eq_listProd (p : ℕ) (s : Finset (Fin n)) :
    y (MvPolynomial.monomial (cartierExponent p s) 1) =
      ((List.ofFn (s.orderEmbOfFin rfl)).map fun j => etaleCoordFun y j ^ (p - 1)).prod := by
  classical
  rw [List.map_ofFn, List.prod_ofFn, coordinate_monomial_eq_prod,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h1 : ∏ i, etaleCoordFun y i ^ cartierExponent p s i =
      ∏ i, if i ∈ s then etaleCoordFun y i ^ (p - 1) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [cartierExponent_apply]
    split_ifs <;> simp
  rw [h1, Finset.prod_ite_mem, Finset.univ_inter]
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ s rfl]
  rw [Finset.prod_map]
  rfl

theorem kaehlerInverseCartierHom_listProd (p : ℕ) [Fact p.Prime] [CharP K p]
    (l : List (ExteriorAlgebra S Ω[S⁄K])) :
    twistedToExterior (kaehlerInverseCartierHom y hy p l.prod) =
      (l.map fun x => twistedToExterior (kaehlerInverseCartierHom y hy p x)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil]
    exact kaehlerInverseCartierHom_one y hy p
  | cons a l ih => rw [List.prod_cons, kaehlerInverseCartierHom_mul, ih, List.map_cons, List.prod_cons]

theorem kaehlerInverseCartierHom_basis (p : ℕ) [Fact p.Prime] [CharP K p] (s : Finset (Fin n)) :
    twistedToExterior (kaehlerInverseCartierHom y hy p ((etaleCoordinateBasis y hy).ExteriorAlgebra s)) =
      y (MvPolynomial.monomial (cartierExponent p s) 1) • (etaleCoordinateBasis y hy).ExteriorAlgebra s := by
  rw [kaehlerExteriorBasis_eq_listProd, kaehlerInverseCartierHom_listProd, List.map_map]
  have h : ((fun x => twistedToExterior (kaehlerInverseCartierHom y hy p x)) ∘
      fun j => ExteriorAlgebra.ι S (etaleCoordinateBasis y hy j)) =
      fun j => etaleCoordFun y j ^ (p - 1) • ExteriorAlgebra.ι S (etaleCoordinateBasis y hy j) := by
    funext j
    rw [Function.comp_apply, kaehlerInverseCartierHom_ι, inverseCartierOneFormAux_basis, map_smul]
  rw [h, list_prod_map_smul, ← cartierMonomial_eq_listProd]

theorem kaehlerInverseCartier_add (p : ℕ) [Fact p.Prime] [CharP K p] (u v : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerInverseCartier y hy p (u + v) =
      kaehlerInverseCartier y hy p u + kaehlerInverseCartier y hy p v := by
  rw [kaehlerInverseCartier, kaehlerInverseCartier, kaehlerInverseCartier, map_add,
    etaleInverseCartier_add, map_add]

theorem kaehlerInverseCartier_smul (p : ℕ) (c : S) (u : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerInverseCartier y hy p (c • u) = c ^ p • kaehlerInverseCartier y hy p u := by
  rw [kaehlerInverseCartier, kaehlerInverseCartier, map_smul, etaleInverseCartier_smul, map_smul]

theorem kaehlerInverseCartier_basis (p : ℕ) [hp : Fact p.Prime] (s : Finset (Fin n)) :
    kaehlerInverseCartier y hy p ((etaleCoordinateBasis y hy).ExteriorAlgebra s) =
      y (MvPolynomial.monomial (cartierExponent p s) 1) • (etaleCoordinateBasis y hy).ExteriorAlgebra s := by
  classical
  have hΦ : (coordModelKaehlerEquiv y hy).symm ((etaleCoordinateBasis y hy).ExteriorAlgebra s) =
      Algebra.TensorProduct.basis S (coordExteriorBasis K n) s := by
    rw [AlgEquiv.symm_apply_eq, coordModelKaehlerEquiv_apply, coordModelToKaehler_basis]
  have hcoef : ∀ t, coordExteriorCoeff (Algebra.TensorProduct.basis S (coordExteriorBasis K n) s) t =
      if t = s then 1 else 0 := by
    intro t
    rw [coordExteriorCoeff, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : t = s
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (fun e => h e.symm), ite_eq_right h]
  rw [kaehlerInverseCartier, hΦ, etaleInverseCartier, Finset.sum_eq_single s]
  · rw [hcoef, ite_eq_left rfl, one_pow, one_mul, coordModelKaehlerEquiv_apply,
      coordModelToKaehler_tmul, ← coordModelToKaehler_basis y hy s, Algebra.TensorProduct.basis_apply,
      coordModelToKaehler_tmul, one_smul]
  · intro t _ ht
    rw [hcoef, ite_eq_right ht, zero_pow hp.out.ne_zero, zero_mul, TensorProduct.zero_tmul]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- **The two inverse Cartier operators agree.** -/
theorem kaehlerInverseCartierHom_eq (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (x : ExteriorAlgebra S Ω[S⁄K]) :
    twistedToExterior (kaehlerInverseCartierHom y hy p x) = kaehlerInverseCartier y hy p x := by
  classical
  have hF := map_sum (AddMonoidHom.mk' (fun x => twistedToExterior (kaehlerInverseCartierHom y hy p x))
    (kaehlerInverseCartierHom_add y hy p))
    (fun s => (etaleCoordinateBasis y hy).ExteriorAlgebra.repr x s •
      (etaleCoordinateBasis y hy).ExteriorAlgebra s) Finset.univ
  have hG := map_sum (AddMonoidHom.mk' (kaehlerInverseCartier y hy p) (kaehlerInverseCartier_add y hy p))
    (fun s => (etaleCoordinateBasis y hy).ExteriorAlgebra.repr x s •
      (etaleCoordinateBasis y hy).ExteriorAlgebra s) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hF hG
  rw [(etaleCoordinateBasis y hy).ExteriorAlgebra.sum_repr x] at hF hG
  rw [hF, hG]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [kaehlerInverseCartierHom_smul, kaehlerInverseCartier_smul, kaehlerInverseCartierHom_basis,
    kaehlerInverseCartier_basis]

/-- **The inverse Cartier operator is multiplicative.** -/
theorem kaehlerInverseCartier_mul (p : ℕ) [Fact p.Prime] [CharP K p] (x x' : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerInverseCartier y hy p (x * x') =
      kaehlerInverseCartier y hy p x * kaehlerInverseCartier y hy p x' := by
  rw [← kaehlerInverseCartierHom_eq, ← kaehlerInverseCartierHom_eq, ← kaehlerInverseCartierHom_eq,
    kaehlerInverseCartierHom_mul]

theorem kaehlerInverseCartier_one (p : ℕ) [Fact p.Prime] [CharP K p] :
    kaehlerInverseCartier y hy p 1 = 1 := by
  rw [← kaehlerInverseCartierHom_eq, kaehlerInverseCartierHom_one]

theorem kaehlerInverseCartier_ι (p : ℕ) [Fact p.Prime] [CharP K p] (ω : Ω[S⁄K]) :
    kaehlerInverseCartier y hy p (ExteriorAlgebra.ι S ω) =
      ExteriorAlgebra.ι S (inverseCartierOneFormAux y hy p ω) := by
  rw [← kaehlerInverseCartierHom_eq, kaehlerInverseCartierHom_ι]

end Hom

end MixedFujita
