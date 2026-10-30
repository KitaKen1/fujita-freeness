/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedIdealLemmaThree
public import MixedFujita.ClosedRationalPoints
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
Products over an algebraically closed field (step 9). Over an algebraically closed field K the
tensor product of a finitely generated domain A and a domain B is a domain
(`isDomain_tensorProduct_of_isAlgClosed`): write elements of A ⊗ B in a K-basis of B with
coefficients in A; if x y = 0 with x, y ≠ 0, a coefficient a of x and a coefficient a' of y have
a a' ≠ 0, so a a' does not vanish at some K-point φ of A (Nullstellensatz), and the
specialization at φ sends x and y to nonzero elements of B with product zero. Hence an affine
integral scheme of finite type over K is geometrically integral
(`geometricallyIntegral_of_isAffine_of_isAlgClosed`), and its fibre product over K with an
integral locally noetherian K-scheme is integral (`isIntegral_pullback_of_isAffine`); fibre
products of smooth schemes are smooth, of the sum of the relative dimensions. These are the
products V × S of an affine open of a smooth variety with a smooth base on which the families of
Lemma 3 live.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section TensorDomain

variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- A nonzero element of a finitely generated domain over an algebraically closed field does not
vanish at some K-point. -/
theorem exists_algHom_apply_ne_zero {a : A} (ha : a ≠ 0) : ∃ φ : A →ₐ[K] K, φ a ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hj := IsJacobsonRing.out this (Ideal.isRadical_bot (R := A))
  have hmem : a ∉ (⊥ : Ideal A).jacobson := by
    rw [hj]
    simpa using ha
  rw [Ideal.jacobson, Ideal.mem_sInf] at hmem
  push Not at hmem
  obtain ⟨m, ⟨-, hm⟩, ham⟩ := hmem
  exact ⟨closedPointEvaluation (K := K) m,
    fun h => ham ((closedPointEvaluation_eq_zero_iff (K := K) m a).mp h)⟩

variable (K A) in
/-- Over an algebraically closed field, the tensor product of a finitely generated domain and a
domain is a domain. -/
theorem isDomain_tensorProduct_of_isAlgClosed (B : Type*) [CommRing B] [IsDomain B]
    [Algebra K B] : IsDomain (A ⊗[K] B) := by
  classical
  let b := Module.Free.chooseBasis K B
  let 𝔅 := Algebra.TensorProduct.basis A b
  let sp : (A →ₐ[K] K) → (A ⊗[K] B →ₐ[K] B) := fun φ =>
    (Algebra.TensorProduct.lid K B).toAlgHom.comp
      (Algebra.TensorProduct.map φ (AlgHom.id K B))
  have hsp : ∀ (φ : A →ₐ[K] K) (x : A ⊗[K] B) (i : Module.Free.ChooseBasisIndex K B),
      b.repr (sp φ x) i = φ (𝔅.repr x i) := by
    intro φ x i
    induction x with
    | tmul a m =>
      simp only [sp, 𝔅, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      change b.repr ((Algebra.TensorProduct.lid K B) (φ a ⊗ₜ[K] m)) i = _
      rw [Algebra.TensorProduct.lid_tmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hne : ∀ x : A ⊗[K] B, x ≠ 0 → ∃ i, 𝔅.repr x i ≠ 0 := by
    intro x hx
    by_contra h
    push Not at h
    apply hx
    have h0 : 𝔅.repr x = 0 := Finsupp.ext h
    simpa using congrArg 𝔅.repr.symm h0
  have hntr : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  have hnzd : NoZeroDivisors (A ⊗[K] B) := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hne x h.1
    obtain ⟨j, hj⟩ := hne y h.2
    obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero (K := K) (mul_ne_zero hi hj)
    rw [map_mul] at hφ
    have h0 : sp φ x * sp φ y = 0 := by rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · have h2 := hsp φ x i
      rw [h1, map_zero, Finsupp.zero_apply] at h2
      exact left_ne_zero_of_mul hφ h2.symm
    · have h2 := hsp φ y j
      rw [h1, map_zero, Finsupp.zero_apply] at h2
      exact right_ne_zero_of_mul hφ h2.symm
  exact NoZeroDivisors.to_isDomain _

end TensorDomain

section Geometric

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- An affine integral scheme of finite type over an algebraically closed field is geometrically
integral. -/
theorem geometricallyIntegral_of_isAffine_of_isAlgClosed {X : Scheme.{u}} [IsAffine X]
    [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  set A : CommRingCat := Γ(X, ⊤) with hA
  let φ : CommRingCat.of K ⟶ A := Spec.preimage (X.isoSpec.inv ≫ f)
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  let ψ : CommRingCat.of K ⟶ CommRingCat.of L := Spec.preimage y
  have hψ : Spec.map ψ = y := Spec.map_preimage _
  let : Algebra K A := φ.hom.toAlgebra
  let : Algebra K L := ψ.hom.toAlgebra
  have hft : Algebra.FiniteType K A := by
    have : LocallyOfFiniteType (Spec.map φ) := by
      rw [hφ]
      infer_instance
    have h1 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    exact h1
  have : IsDomain (A ⊗[K] L) := isDomain_tensorProduct_of_isAlgClosed K A L
  have h' : IsPullback (fst ≫ X.isoSpec.hom) snd
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    refine h.of_iso (Iso.refl Z) X.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · change f ≫ 𝟙 _ = X.isoSpec.hom ≫ Spec.map φ
      rw [hφ]
      simp
    · change y ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map ψ
      rw [hψ]
      simp
  let e : Z ≅ Spec (CommRingCat.of (A ⊗[K] L)) := h'.isoPullback ≪≫ pullbackSpecIso K A L
  exact IsIntegral.of_isIso e.inv

/-- The fibre product over K of an affine integral scheme of finite type with an integral locally
noetherian scheme is integral. -/
theorem isIntegral_pullback_of_isAffine {X W : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [IsIntegral W]
    [IsLocallyNoetherian W] (g : W ⟶ Spec (CommRingCat.of K)) : IsIntegral (pullback f g) := by
  have := geometricallyIntegral_of_isAffine_of_isAlgClosed f
  infer_instance

omit [IsAlgClosed K] in
/-- The fibre product of smooth schemes is smooth of the sum of the relative dimensions. -/
theorem smoothOfRelativeDimension_pullback {X W : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (g : W ⟶ Spec (CommRingCat.of K)) {n d : ℕ} [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension d g] :
    SmoothOfRelativeDimension (n + d) (pullback.snd f g ≫ g) :=
  inferInstance

end Geometric

end MixedFujita
