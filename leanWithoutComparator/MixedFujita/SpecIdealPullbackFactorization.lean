/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealTensorTorsionFactor
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-! The actual pullback of an ideal's associated sheaf maps epimorphically
onto the sheaf of the actual extended ideal. Tensor balancing and the
tilde/global-section adjunction give unique factorization of every map into
a sheaf whose global-section module has no zero scalar divisors. No flatness
or target quasi-coherence input is used. General-scheme gluing remains separate. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open TauCeti.AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (I : Ideal R)

/-- Tensor multiplication with codomain the actual ring-map image ideal. -/
noncomputable def extendedIdealTensorMap :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R I) ⟶ ModuleCat.of S (I.map φ.hom) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let m := idealTensorMultiply I (B := S)
  have hr : LinearMap.range m = I.map φ.hom := idealTensorMultiply_range I
  let e := LinearEquiv.ofEq (LinearMap.range m) (I.map φ.hom) hr
  exact ModuleCat.ofHom (e.toLinearMap ∘ₗ m.rangeRestrict)

theorem extendedIdealTensorMap_epi : Epi (extendedIdealTensorMap φ I) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let m := idealTensorMultiply I (B := S)
  have hr : LinearMap.range m = I.map φ.hom := idealTensorMultiply_range I
  let e := LinearEquiv.ofEq (LinearMap.range m) (I.map φ.hom) hr
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact e.surjective.comp m.surjective_rangeRestrict

theorem extendedIdealTensorMap_exists_factor
    (hI : I ≠ ⊥) (hφ : Function.Injective φ.hom)
    (N : ModuleCat.{u} S) [NoZeroSMulDivisors S N]
    (f : (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R I) ⟶ N) :
    ∃ g : ModuleCat.of S (I.map φ.hom) ⟶ N, extendedIdealTensorMap φ I ≫ g = f := by
  letI : Algebra R S := φ.hom.toAlgebra
  let m := idealTensorMultiply I (B := S)
  have hr : LinearMap.range m = I.map φ.hom := idealTensorMultiply_range I
  let e := LinearEquiv.ofEq (LinearMap.range m) (I.map φ.hom) hr
  obtain ⟨g, hg⟩ := idealTensorMultiply_exists_range_factor_to_torsionFree I hI hφ f.hom
  refine ⟨ModuleCat.ofHom (g ∘ₗ e.symm.toLinearMap), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change g (e.symm (e (m.rangeRestrict x))) = f.hom x
  rw [e.symm_apply_apply]
  exact hg x

/-- A genuine scheme-module morphism from the pullback to the extended-ideal sheaf. -/
noncomputable def specIdealPullbackImageMap :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde (ModuleCat.of R I)) ⟶
      tilde (ModuleCat.of S (I.map φ.hom)) :=
  ((tildeFunctorCompPullbackIso φ).app (ModuleCat.of R I)).hom ≫
    (tilde.functor S).map (extendedIdealTensorMap φ I)

theorem specIdealPullbackImageMap_epi : Epi (specIdealPullbackImageMap φ I) := by
  letI := extendedIdealTensorMap_epi φ I
  unfold specIdealPullbackImageMap
  infer_instance

/-- Every map into a target with torsion-free global sections factors uniquely
through the actual extended ideal sheaf. No target quasi-coherence is assumed. -/
theorem specIdealPullbackImageMap_existsUnique_factor
    (hI : I ≠ ⊥) (hφ : Function.Injective φ.hom) (N : (Spec S).Modules)
    [NoZeroSMulDivisors S ((moduleSpecΓFunctor (R := S)).obj N)]
    (ψ : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde (ModuleCat.of R I)) ⟶ N) :
    ∃! δ : tilde (ModuleCat.of S (I.map φ.hom)) ⟶ N,
      specIdealPullbackImageMap φ I ≫ δ = ψ := by
  let e := (tildeFunctorCompPullbackIso φ).app (ModuleCat.of R I)
  let adj := tilde.adjunction (R := S)
  let f := adj.homEquiv _ N (e.inv ≫ ψ)
  obtain ⟨g, hg⟩ := extendedIdealTensorMap_exists_factor φ I hI hφ
    ((moduleSpecΓFunctor (R := S)).obj N) f
  let δ := (adj.homEquiv _ N).symm g
  have hmid : (tilde.functor S).map (extendedIdealTensorMap φ I) ≫ δ = e.inv ≫ ψ := by
    apply (adj.homEquiv _ N).injective
    rw [Adjunction.homEquiv_naturality_left]
    simpa only [δ, Equiv.apply_symm_apply] using hg
  have hδ : specIdealPullbackImageMap φ I ≫ δ = ψ := by
    change (e.hom ≫ (tilde.functor S).map (extendedIdealTensorMap φ I)) ≫ δ = ψ
    rw [Category.assoc, hmid, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  letI := specIdealPullbackImageMap_epi φ I
  exact ⟨δ, hδ, fun δ' hδ' => (cancel_epi (specIdealPullbackImageMap φ I)).mp (hδ'.trans hδ.symm)⟩

end MixedFujita
