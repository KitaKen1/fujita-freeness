/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleInverseCartier

/-!
The intrinsic de Rham differential of an étale chart (step 10, compatibility with coordinate
changes).

The coordinate model `S ⊗ ⋀(Kⁿ)` of checks 395–401 depends on the étale coordinates `y`. Sending
`a ⊗ e_s` to `a · d y_s` is an isomorphism of `S`-algebras onto the exterior algebra `⋀_S Ω[S⁄K]`
of the Kähler differentials (`coordModelKaehlerEquiv`; it maps the basis `1 ⊗ e_s` to the basis
`d y_s`). Transporting the coordinate differential gives a `K`-linear map `kaehlerDeRhamDiff y` of
`⋀_S Ω[S⁄K]`.

**It does not depend on the coordinates** (`kaehlerDeRhamDiff_eq`). The coordinate differential
satisfies `d(a ω) = da ∧ ω + a dω` and `d(dg ∧ ω) = -dg ∧ dω` (`koszulDeRhamDiff_smul`,
`koszulDeRhamDiff_exact_mul`), so its transport `δ` satisfies
`δ 1 = 0`, `δ(f ω) = df ∧ ω + f δω`, `δ(df ∧ ω) = -df ∧ δω`.
These three rules determine `δ` (`kaehlerDeRham_unique`): the elements `x` with
`x ∧ N ⊆ N` for the agreement locus `N` of two such maps form a subalgebra containing the functions
and the exact differentials `dg`, which generate `⋀_S Ω[S⁄K]` because `Ω[S⁄K]` is spanned by the
`dg`. Hence any two systems of formally étale coordinates (even of different lengths) give the same
de Rham differential, with `d ∘ d = 0`, and the Cartier isomorphism of check-401 transports to the
intrinsic de Rham complex (`kaehler_cartier_isomorphism`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Leibniz

variable {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] {n : ℕ}

/-- **Leibniz rule for functions** in the coordinate model: `d(a ω) = da ∧ ω + a dω`. -/
theorem koszulDeRhamDiff_smul (D : Fin n → A →ₗ[K] A)
    (hD : ∀ j a b, D j (a * b) = D j a * b + a * D j b) (a : A) (ω : A ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff D (a • ω) = koszulDeRhamDiff D (a ⊗ₜ 1) * ω + a • koszulDeRhamDiff D ω := by
  induction ω using TensorProduct.inductionOn with
  | tmul b e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, koszulDeRhamDiff_tmul, koszulDeRhamDiff_tmul,
      koszulDeRhamDiff_tmul, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul, hD,
      TensorProduct.add_tmul]
  | add x z hx hz =>
    rw [smul_add, map_add, hx, hz, map_add, mul_add, smul_add]
    abel

/-- `d(e_j ∧ ω) = -e_j ∧ dω` in the coordinate model. -/
theorem koszulDeRhamDiff_coordVector_mul (D : Fin n → A →ₗ[K] A) (j : Fin n)
    (ω : A ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff D (((1 : A) ⊗ₜ coordVector K j) * ω) =
      -(((1 : A) ⊗ₜ coordVector K j) * koszulDeRhamDiff D ω) := by
  induction ω using TensorProduct.inductionOn with
  | tmul b e =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, koszulDeRhamDiff_tmul, koszulDeRhamDiff_tmul,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coordVector_mul_comm_neg i j e,
      TensorProduct.tmul_neg, neg_neg]
  | add x z hx hz => rw [mul_add, map_add, hx, hz, map_add, mul_add, neg_add]

/-- **Leibniz rule for exact `1`-forms**: `d(dg ∧ ω) = -dg ∧ dω`. -/
theorem koszulDeRhamDiff_exact_mul (D : Fin n → A →ₗ[K] A)
    (hD : ∀ j a b, D j (a * b) = D j a * b + a * D j b)
    (hcomm : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i) (g : A) (ω : A ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff D (koszulDeRhamDiff D (g ⊗ₜ 1) * ω) =
      -(koszulDeRhamDiff D (g ⊗ₜ 1) * koszulDeRhamDiff D ω) := by
  have hD1 : ∀ j, D j 1 = 0 := fun j => by
    have h := hD j 1 1
    simp only [one_mul, mul_one] at h
    exact left_eq_add.mp h
  have hd1 : ∀ j, koszulDeRhamDiff D ((1 : A) ⊗ₜ coordVector K j) = 0 := fun j => by
    rw [koszulDeRhamDiff_tmul]
    simp [hD1]
  have hexp : koszulDeRhamDiff D (g ⊗ₜ 1) = ∑ j, D j g • ((1 : A) ⊗ₜ coordVector K j) := by
    rw [koszulDeRhamDiff_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hzero : ∑ j, koszulDeRhamDiff D (D j g ⊗ₜ 1) * ((1 : A) ⊗ₜ coordVector K j) = 0 := by
    have h := LinearMap.congr_fun (koszulDeRhamDiff_comp_self D hcomm) (g ⊗ₜ 1)
    rw [LinearMap.comp_apply, hexp, map_sum, LinearMap.zero_apply] at h
    simpa only [koszulDeRhamDiff_smul D hD, hd1, smul_zero, add_zero] using h
  have h1 : ∑ j, koszulDeRhamDiff D (D j g ⊗ₜ 1) * (((1 : A) ⊗ₜ coordVector K j) * ω) = 0 := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hzero, zero_mul]
  have h2 : ∑ j, D j g • -(((1 : A) ⊗ₜ coordVector K j) * koszulDeRhamDiff D ω) =
      -((∑ j, D j g • ((1 : A) ⊗ₜ coordVector K j)) * koszulDeRhamDiff D ω) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp_rw [smul_neg, smul_mul_assoc]
  rw [hexp, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, koszulDeRhamDiff_smul D hD, koszulDeRhamDiff_coordVector_mul]
  rw [Finset.sum_add_distrib, h1, zero_add, h2]

end Leibniz

section Comparison

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- `e_j ↦ d y_j` on `Kⁿ`. -/
noncomputable def coordDifferentialMap : (Fin n → K) →ₗ[K] Ω[S⁄K] :=
  Fintype.linearCombination K fun j => KaehlerDifferential.D K S (y (MvPolynomial.X j))

theorem coordDifferentialMap_single (j : Fin n) :
    coordDifferentialMap y (Pi.single j 1) = KaehlerDifferential.D K S (y (MvPolynomial.X j)) := by
  simp [coordDifferentialMap, Fintype.linearCombination_apply_single]

/-- `⋀(Kⁿ) → ⋀_S Ω[S⁄K]`, `e_j ↦ d y_j`. -/
noncomputable def coordExteriorToKaehler : CoordExterior K n →ₐ[K] ExteriorAlgebra S Ω[S⁄K] :=
  ExteriorAlgebra.lift K ⟨((ExteriorAlgebra.ι S).restrictScalars K) ∘ₗ coordDifferentialMap y,
    fun m => by
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      exact ExteriorAlgebra.ι_sq_zero _⟩

theorem coordExteriorToKaehler_coordVector (j : Fin n) :
    coordExteriorToKaehler y (coordVector K j) =
      ExteriorAlgebra.ι S (etaleCoordinateBasis y hy j) := by
  rw [coordExteriorToKaehler, coordVector, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, coordDifferentialMap_single, etaleCoordinateBasis_apply]

/-- **The comparison** `S ⊗ ⋀(Kⁿ) → ⋀_S Ω[S⁄K]`, `a ⊗ e_s ↦ a · d y_s`. -/
noncomputable def coordModelToKaehler : S ⊗[K] CoordExterior K n →ₐ[S] ExteriorAlgebra S Ω[S⁄K] :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coordExteriorToKaehler y) fun a _ => by
    rw [Algebra.ofId_apply]
    exact Algebra.commute_algebraMap_left a _

theorem coordModelToKaehler_tmul (a : S) (e : CoordExterior K n) :
    coordModelToKaehler y (a ⊗ₜ e) = a • coordExteriorToKaehler y e := by
  rw [coordModelToKaehler, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

theorem kaehlerExteriorBasis_eq_listProd (s : Finset (Fin n)) :
    (etaleCoordinateBasis y hy).ExteriorAlgebra s =
      ((List.ofFn (s.orderEmbOfFin rfl)).map
        fun j => ExteriorAlgebra.ι S (etaleCoordinateBasis y hy j)).prod := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti S s.card ((etaleCoordinateBasis y hy) ∘ (s.orderEmbOfFin rfl)) = _
  rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  rfl

theorem coordModelToKaehler_basis (s : Finset (Fin n)) :
    coordModelToKaehler y (Algebra.TensorProduct.basis S (coordExteriorBasis K n) s) =
      (etaleCoordinateBasis y hy).ExteriorAlgebra s := by
  rw [Algebra.TensorProduct.basis_apply, coordModelToKaehler_tmul, one_smul,
    coordExteriorBasis_eq_listProd, map_list_prod, List.map_map, kaehlerExteriorBasis_eq_listProd]
  congr 2
  funext j
  exact coordExteriorToKaehler_coordVector y hy j

include hy in
theorem coordModelToKaehler_bijective : Function.Bijective (coordModelToKaehler y) := by
  set b₁ := Algebra.TensorProduct.basis S (coordExteriorBasis K n)
  set b₂ := (etaleCoordinateBasis y hy).ExteriorAlgebra
  have h : (coordModelToKaehler y).toLinearMap = (b₁.equiv b₂ (Equiv.refl _)).toLinearMap := by
    apply b₁.ext
    intro s
    rw [AlgHom.toLinearMap_apply, coordModelToKaehler_basis y hy, LinearEquiv.coe_toLinearMap,
      Module.Basis.equiv_apply, Equiv.refl_apply]
  have h2 : ⇑(coordModelToKaehler y) = ⇑(b₁.equiv b₂ (Equiv.refl _)) := by
    ext ω
    exact LinearMap.congr_fun h ω
  rw [h2]
  exact (b₁.equiv b₂ (Equiv.refl _)).bijective

/-- The comparison as an isomorphism of `S`-algebras. -/
noncomputable def coordModelKaehlerEquiv :
    S ⊗[K] CoordExterior K n ≃ₐ[S] ExteriorAlgebra S Ω[S⁄K] :=
  AlgEquiv.ofBijective (coordModelToKaehler y) (coordModelToKaehler_bijective y hy)

theorem coordModelKaehlerEquiv_apply (ω : S ⊗[K] CoordExterior K n) :
    coordModelKaehlerEquiv y hy ω = coordModelToKaehler y ω := rfl

/-- The comparison sends `dg` to `dg`. -/
theorem coordModelToKaehler_diff_tmul_one (g : S) :
    coordModelToKaehler y (koszulDeRhamDiff (etaleCoordPartial y hy) (g ⊗ₜ 1)) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) := by
  rw [koszulDeRhamDiff_tmul, map_sum]
  conv_rhs => rw [← (etaleCoordinateBasis y hy).sum_repr (KaehlerDifferential.D K S g), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_one, coordModelToKaehler_tmul, coordExteriorToKaehler_coordVector y hy, map_smul]
  rfl

/-- **The de Rham differential of `⋀_S Ω[S⁄K]`**, transported from the coordinate model. -/
noncomputable def kaehlerDeRhamDiff :
    ExteriorAlgebra S Ω[S⁄K] →ₗ[K] ExteriorAlgebra S Ω[S⁄K] :=
  (((coordModelKaehlerEquiv y hy : _ →ₐ[S] _).restrictScalars K).toLinearMap ∘ₗ
    koszulDeRhamDiff (etaleCoordPartial y hy)) ∘ₗ
      (((coordModelKaehlerEquiv y hy).symm : _ →ₐ[S] _).restrictScalars K).toLinearMap

theorem kaehlerDeRhamDiff_apply (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy ω = coordModelKaehlerEquiv y hy
      (koszulDeRhamDiff (etaleCoordPartial y hy) ((coordModelKaehlerEquiv y hy).symm ω)) := rfl

theorem etaleCoordPartial_leibniz (j : Fin n) (a b : S) :
    etaleCoordPartial y hy j (a * b) =
      etaleCoordPartial y hy j a * b + a * etaleCoordPartial y hy j b := by
  change etaleCoordinateDerivation y hy j (a * b) = _
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm b]
  rfl

theorem kaehlerDeRhamDiff_one : kaehlerDeRhamDiff y hy 1 = 0 := by
  rw [kaehlerDeRhamDiff_apply, map_one, Algebra.TensorProduct.one_def, koszulDeRhamDiff_tmul]
  have hD1 : ∀ j, etaleCoordPartial y hy j 1 = 0 := fun j => by
    change etaleCoordinateDerivation y hy j 1 = 0
    exact Derivation.map_one_eq_zero _
  simp [hD1]

theorem kaehlerDeRhamDiff_smul (f : S) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (f • ω) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D K S f) * ω + f • kaehlerDeRhamDiff y hy ω := by
  rw [kaehlerDeRhamDiff_apply, kaehlerDeRhamDiff_apply, map_smul,
    koszulDeRhamDiff_smul _ (etaleCoordPartial_leibniz y hy), map_add, map_mul, map_smul,
    coordModelKaehlerEquiv_apply, coordModelToKaehler_diff_tmul_one, AlgEquiv.apply_symm_apply]

theorem kaehlerDeRhamDiff_exact_mul (g : S) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff y hy (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω) =
      -(ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * kaehlerDeRhamDiff y hy ω) := by
  have hι : ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) =
      coordModelKaehlerEquiv y hy (koszulDeRhamDiff (etaleCoordPartial y hy) (g ⊗ₜ 1)) :=
    (coordModelToKaehler_diff_tmul_one y hy g).symm
  rw [kaehlerDeRhamDiff_apply, kaehlerDeRhamDiff_apply, hι, map_mul, AlgEquiv.symm_apply_apply,
    koszulDeRhamDiff_exact_mul _ (etaleCoordPartial_leibniz y hy) (etaleCoordPartial_comm y hy),
    map_neg, map_mul]

/-- `d ∘ d = 0` on `⋀_S Ω[S⁄K]`. -/
theorem kaehlerDeRhamDiff_comp_self :
    kaehlerDeRhamDiff y hy ∘ₗ kaehlerDeRhamDiff y hy = 0 := by
  refine LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, kaehlerDeRhamDiff_apply, kaehlerDeRhamDiff_apply,
    AlgEquiv.symm_apply_apply, LinearMap.zero_apply]
  have h := LinearMap.congr_fun (koszulDeRhamDiff_comp_self (etaleCoordPartial y hy)
    (etaleCoordPartial_comm y hy)) ((coordModelKaehlerEquiv y hy).symm ω)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [h, map_zero]

end Comparison

section Uniqueness

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

/-- **The de Rham differential is determined by three rules**: `δ 1 = 0`,
`δ(f ω) = df ∧ ω + f δω` and `δ(dg ∧ ω) = -dg ∧ δω`. -/
theorem kaehlerDeRham_unique (δ δ' : ExteriorAlgebra S Ω[S⁄K] →ₗ[K] ExteriorAlgebra S Ω[S⁄K])
    (h1 : δ 1 = 0) (h1' : δ' 1 = 0)
    (h2 : ∀ (f : S) ω, δ (f • ω) = ExteriorAlgebra.ι S (KaehlerDifferential.D K S f) * ω + f • δ ω)
    (h2' : ∀ (f : S) ω,
      δ' (f • ω) = ExteriorAlgebra.ι S (KaehlerDifferential.D K S f) * ω + f • δ' ω)
    (h3 : ∀ (g : S) ω, δ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω) =
      -(ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * δ ω))
    (h3' : ∀ (g : S) ω, δ' (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω) =
      -(ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * δ' ω)) : δ = δ' := by
  have hsmul : ∀ (f : S) ω, δ ω = δ' ω → δ (f • ω) = δ' (f • ω) := fun f ω h => by
    rw [h2, h2', h]
  have hι : ∀ x : Ω[S⁄K], ∀ ω, δ ω = δ' ω →
      δ (ExteriorAlgebra.ι S x * ω) = δ' (ExteriorAlgebra.ι S x * ω) := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro ω h
      rw [h3, h3', h]
    | zero =>
      intro ω _
      rw [map_zero, zero_mul, map_zero, map_zero]
    | add x z _ _ hx hz =>
      intro ω h
      rw [map_add, add_mul, map_add, map_add, hx ω h, hz ω h]
    | smul a x _ hx =>
      intro ω h
      rw [map_smul, smul_mul_assoc]
      exact hsmul a _ (hx ω h)
  have hall : ∀ x : ExteriorAlgebra S Ω[S⁄K], ∀ ω, δ ω = δ' ω → δ (x * ω) = δ' (x * ω) := by
    intro x
    induction x using ExteriorAlgebra.induction with
    | algebraMap f =>
      intro ω h
      rw [← Algebra.smul_def]
      exact hsmul f ω h
    | ι x => exact hι x
    | mul a b ha hb =>
      intro ω h
      rw [mul_assoc]
      exact ha _ (hb ω h)
    | add a b ha hb =>
      intro ω h
      rw [add_mul, map_add, map_add, ha ω h, hb ω h]
  refine LinearMap.ext fun ω => ?_
  have := hall ω 1 (by rw [h1, h1'])
  rwa [mul_one] at this

/-- **Independence of the coordinates.** Any two systems of formally étale coordinates give the
same de Rham differential on `⋀_S Ω[S⁄K]`. -/
theorem kaehlerDeRhamDiff_eq {n m : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin m) K →ₐ[K] S)
    (hz : z.toRingHom.FormallyEtale) : kaehlerDeRhamDiff y hy = kaehlerDeRhamDiff z hz :=
  kaehlerDeRham_unique _ _ (kaehlerDeRhamDiff_one y hy) (kaehlerDeRhamDiff_one z hz)
    (kaehlerDeRhamDiff_smul y hy) (kaehlerDeRhamDiff_smul z hz)
    (kaehlerDeRhamDiff_exact_mul y hy) (kaehlerDeRhamDiff_exact_mul z hz)

end Uniqueness

section Cartier

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The inverse Cartier operator of the chart on `⋀_S Ω[S⁄K]`. -/
noncomputable def kaehlerInverseCartier (p : ℕ) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    ExteriorAlgebra S Ω[S⁄K] :=
  coordModelKaehlerEquiv y hy (etaleInverseCartier y p ((coordModelKaehlerEquiv y hy).symm ω))

/-- **The Cartier isomorphism on the intrinsic de Rham complex of an étale chart.** -/
theorem kaehler_cartier_isomorphism (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]
    [Algebra.FiniteType K S] [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : ExteriorAlgebra S Ω[S⁄K]) (hz : kaehlerDeRhamDiff y hy z = 0) :
    ∃! ω : ExteriorAlgebra S Ω[S⁄K],
      z - kaehlerInverseCartier y hy p ω ∈ LinearMap.range (kaehlerDeRhamDiff y hy) := by
  set Φ := coordModelKaehlerEquiv y hy
  have hz' : koszulDeRhamDiff (etaleCoordPartial y hy) (Φ.symm z) = 0 := by
    have h := congrArg Φ.symm hz
    rwa [kaehlerDeRhamDiff_apply, AlgEquiv.symm_apply_apply, map_zero] at h
  have hrange : ∀ w : ExteriorAlgebra S Ω[S⁄K], w ∈ LinearMap.range (kaehlerDeRhamDiff y hy) ↔
      Φ.symm w ∈ LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) := by
    intro w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Φ.symm v, by rw [kaehlerDeRhamDiff_apply, AlgEquiv.symm_apply_apply]⟩
    · rintro ⟨v, hv⟩
      exact ⟨Φ v, by rw [kaehlerDeRhamDiff_apply, AlgEquiv.symm_apply_apply, hv,
        AlgEquiv.apply_symm_apply]⟩
  have hsub : ∀ ω : ExteriorAlgebra S Ω[S⁄K], Φ.symm (z - kaehlerInverseCartier y hy p ω) =
      Φ.symm z - etaleInverseCartier y p (Φ.symm ω) := by
    intro ω
    rw [map_sub, kaehlerInverseCartier, AlgEquiv.symm_apply_apply]
  obtain ⟨ω₀, hω₀, huniq⟩ := etale_cartier_isomorphism y hy p hy0 (Φ.symm z) hz'
  refine ⟨Φ ω₀, ?_, fun ω hω => ?_⟩
  · show z - kaehlerInverseCartier y hy p (Φ ω₀) ∈ _
    rw [hrange, hsub, AlgEquiv.symm_apply_apply]
    exact hω₀
  · have hω' : Φ.symm z - etaleInverseCartier y p (Φ.symm ω) ∈
        LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) := by
      rw [← hsub, ← hrange]
      exact hω
    have h := huniq (Φ.symm ω) hω'
    rw [← h, AlgEquiv.apply_symm_apply]

end Cartier

end MixedFujita
