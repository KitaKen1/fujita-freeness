/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KaehlerDeRhamComparison

/-!
Functoriality of the intrinsic de Rham complex (step 10, gluing of étale charts).

Let `S → T` be a map of `K`-algebras, both with formally étale coordinates (for instance the
restriction to a smaller affine open of a smooth variety). The induced map
`⋀_S Ω[S⁄K] → ⋀_T Ω[T⁄K]` (`kaehlerExteriorMap`, `dg ↦ d(g|_T)`) commutes with the de Rham
differentials (`kaehlerDeRhamDiff_comp_exteriorMap`), whatever coordinates are used on `S` and
on `T`. The proof is the uniqueness argument of check-402 for maps `δ : ⋀_S Ω → ⋀_T Ω` twisted by
the induced map `Φ`: the rules `δ 1 = 0`, `δ(f ω) = d(f|_T) ∧ Φ ω + f|_T δω` and
`δ(dg ∧ ω) = -d(g|_T) ∧ δω` determine `δ` (`kaehlerDeRham_map_unique`), and both `d_T ∘ Φ` and
`Φ ∘ d_S` satisfy them.

If the coordinates of `T` are the images of those of `S`, the induced map also commutes with the
inverse Cartier operators (`kaehlerInverseCartier_exteriorMap`), since on the coordinate models it is
`φ ⊗ id` and the inverse Cartier operator is given by the same formula on coefficients.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Map

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]
  {T : Type w} [CommRing T] [Algebra K T] [Algebra S T] [IsScalarTower K S T]

variable (K S T) in
/-- The map `⋀_S Ω[S⁄K] → ⋀_T Ω[T⁄K]` induced by `S → T`. -/
noncomputable def kaehlerExteriorMap : ExteriorAlgebra S Ω[S⁄K] →ₐ[S] ExteriorAlgebra T Ω[T⁄K] :=
  ExteriorAlgebra.lift S ⟨((ExteriorAlgebra.ι T).restrictScalars S) ∘ₗ
    KaehlerDifferential.map K K S T, fun m => by
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      exact ExteriorAlgebra.ι_sq_zero _⟩

theorem kaehlerExteriorMap_ι (x : Ω[S⁄K]) :
    kaehlerExteriorMap K S T (ExteriorAlgebra.ι S x) =
      ExteriorAlgebra.ι T (KaehlerDifferential.map K K S T x) := by
  rw [kaehlerExteriorMap, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply]

theorem kaehlerExteriorMap_ι_D (g : S) :
    kaehlerExteriorMap K S T (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g)) =
      ExteriorAlgebra.ι T (KaehlerDifferential.D K T (algebraMap S T g)) := by
  rw [kaehlerExteriorMap_ι, KaehlerDifferential.map_D]

theorem kaehlerExteriorMap_smul (f : S) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerExteriorMap K S T (f • ω) = algebraMap S T f • kaehlerExteriorMap K S T ω := by
  rw [map_smul, algebraMap_smul]

/-- **Twisted uniqueness.** A `K`-linear map `δ : ⋀_S Ω → ⋀_T Ω` is determined by `δ 1 = 0`,
`δ(f ω) = d(f|_T) ∧ Φ ω + f|_T δω` and `δ(dg ∧ ω) = -d(g|_T) ∧ δω`. -/
theorem kaehlerDeRham_map_unique (δ δ' : ExteriorAlgebra S Ω[S⁄K] →ₗ[K] ExteriorAlgebra T Ω[T⁄K])
    (h1 : δ 1 = 0) (h1' : δ' 1 = 0)
    (h2 : ∀ (f : S) ω, δ (f • ω) = ExteriorAlgebra.ι T (KaehlerDifferential.D K T (algebraMap S T f)) *
      kaehlerExteriorMap K S T ω + algebraMap S T f • δ ω)
    (h2' : ∀ (f : S) ω, δ' (f • ω) =
      ExteriorAlgebra.ι T (KaehlerDifferential.D K T (algebraMap S T f)) *
        kaehlerExteriorMap K S T ω + algebraMap S T f • δ' ω)
    (h3 : ∀ (g : S) ω, δ (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω) =
      -(ExteriorAlgebra.ι T (KaehlerDifferential.D K T (algebraMap S T g)) * δ ω))
    (h3' : ∀ (g : S) ω, δ' (ExteriorAlgebra.ι S (KaehlerDifferential.D K S g) * ω) =
      -(ExteriorAlgebra.ι T (KaehlerDifferential.D K T (algebraMap S T g)) * δ' ω)) :
    δ = δ' := by
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

/-- **Functoriality of the de Rham differential.** For a map `S → T` of `K`-algebras with formally
étale coordinates (chosen independently), the induced map of exterior algebras of Kähler
differentials commutes with the de Rham differentials. -/
theorem kaehlerDeRhamDiff_comp_exteriorMap {n m : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin m) K →ₐ[K] T)
    (hz : z.toRingHom.FormallyEtale) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerDeRhamDiff z hz (kaehlerExteriorMap K S T ω) =
      kaehlerExteriorMap K S T (kaehlerDeRhamDiff y hy ω) := by
  let Φ : ExteriorAlgebra S Ω[S⁄K] →ₗ[K] ExteriorAlgebra T Ω[T⁄K] :=
    ((kaehlerExteriorMap K S T).restrictScalars K).toLinearMap
  have hΦ : ∀ x, Φ x = kaehlerExteriorMap K S T x := fun _ => rfl
  have key := kaehlerDeRham_map_unique (kaehlerDeRhamDiff z hz ∘ₗ Φ) (Φ ∘ₗ kaehlerDeRhamDiff y hy)
    (by rw [LinearMap.comp_apply, hΦ, map_one, kaehlerDeRhamDiff_one])
    (by rw [LinearMap.comp_apply, kaehlerDeRhamDiff_one, map_zero])
    (fun f ω => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ, hΦ, kaehlerExteriorMap_smul,
        kaehlerDeRhamDiff_smul])
    (fun f ω => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, kaehlerDeRhamDiff_smul, hΦ, hΦ, map_add,
        map_mul, kaehlerExteriorMap_ι_D, kaehlerExteriorMap_smul])
    (fun g ω => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ, hΦ, map_mul, kaehlerExteriorMap_ι_D,
        kaehlerDeRhamDiff_exact_mul])
    (fun g ω => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, kaehlerDeRhamDiff_exact_mul, hΦ, hΦ, map_neg,
        map_mul, kaehlerExteriorMap_ι_D])
  exact LinearMap.congr_fun key ω

end Map

section Coordinates

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]
  {T : Type w} [CommRing T] [Algebra K T] [Algebra S T] [IsScalarTower K S T] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The coordinates of `S` pushed to `T`. -/
noncomputable abbrev pushedCoordinates : MvPolynomial (Fin n) K →ₐ[K] T :=
  (IsScalarTower.toAlgHom K S T).comp y

theorem kaehlerExteriorMap_coordExteriorToKaehler (e : CoordExterior K n) :
    kaehlerExteriorMap K S T (coordExteriorToKaehler y e) =
      coordExteriorToKaehler (pushedCoordinates (T := T) y) e := by
  have h : ((kaehlerExteriorMap K S T).restrictScalars K).comp (coordExteriorToKaehler y) =
      coordExteriorToKaehler (pushedCoordinates (T := T) y) := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    show kaehlerExteriorMap K S T (coordExteriorToKaehler y (ExteriorAlgebra.ι K v)) =
      coordExteriorToKaehler (pushedCoordinates (T := T) y) (ExteriorAlgebra.ι K v)
    unfold coordExteriorToKaehler
    rw [ExteriorAlgebra.lift_ι_apply, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
      kaehlerExteriorMap_ι]
    congr 1
    simp only [coordDifferentialMap, Fintype.linearCombination_apply, map_sum,
      LinearMap.map_smul_of_tower]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [KaehlerDifferential.map_D]
    rfl
  exact AlgHom.congr_fun h e

/-- On the coordinate models the induced map is `φ ⊗ id`. -/
theorem kaehlerExteriorMap_coordModel (ω : S ⊗[K] CoordExterior K n) :
    kaehlerExteriorMap K S T (coordModelToKaehler y ω) =
      coordModelToKaehler (pushedCoordinates (T := T) y)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K _) ω) := by
  have hext : ((kaehlerExteriorMap K S T).restrictScalars K).comp
      ((coordModelToKaehler y).restrictScalars K) =
      ((coordModelToKaehler (pushedCoordinates (T := T) y)).restrictScalars K).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K _)) := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
        coordModelToKaehler_tmul, map_one, IsScalarTower.coe_toAlgHom', kaehlerExteriorMap_smul]
    · apply AlgHom.ext
      intro e
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
        coordModelToKaehler_tmul, one_smul, map_one, AlgHom.id_apply]
      exact kaehlerExteriorMap_coordExteriorToKaehler y e
  exact congrArg (fun F => F ω) (congrArg DFunLike.coe hext)

theorem coordExteriorCoeff_map (ω : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) :
    coordExteriorCoeff (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K _) ω) s =
      algebraMap S T (coordExteriorCoeff ω s) := by
  conv_lhs => rw [eq_sum_tmul_coordExteriorBasis ω]
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply]
  rw [coordExteriorCoeff_sum_tmul]

/-- The inverse Cartier operators of `S` and of `T` with the pushed coordinates are compatible on
the coordinate models. -/
theorem etaleInverseCartier_map (p : ℕ) (ω : S ⊗[K] CoordExterior K n) :
    etaleInverseCartier (pushedCoordinates (T := T) y) p
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K _) ω) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K _)
        (etaleInverseCartier y p ω) := by
  rw [etaleInverseCartier, etaleInverseCartier, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coordExteriorCoeff_map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_mul, map_pow]
  rfl

/-- **The inverse Cartier operators commute with maps carrying coordinates to coordinates.** -/
theorem kaehlerInverseCartier_exteriorMap (hz : (pushedCoordinates (T := T) y).toRingHom.FormallyEtale)
    (p : ℕ) (ω : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerInverseCartier (pushedCoordinates (T := T) y) hz p (kaehlerExteriorMap K S T ω) =
      kaehlerExteriorMap K S T (kaehlerInverseCartier y hy p ω) := by
  set Φy := coordModelKaehlerEquiv y hy
  set Φz := coordModelKaehlerEquiv (pushedCoordinates (T := T) y) hz
  set M := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K S T) (AlgHom.id K (CoordExterior K n))
  have hω : kaehlerExteriorMap K S T ω = Φz (M (Φy.symm ω)) := by
    conv_lhs => rw [← Φy.apply_symm_apply ω]
    exact kaehlerExteriorMap_coordModel y _
  rw [kaehlerInverseCartier, kaehlerInverseCartier, hω, AlgEquiv.symm_apply_apply,
    etaleInverseCartier_map]
  exact (kaehlerExteriorMap_coordModel y _).symm

end Coordinates

end MixedFujita
