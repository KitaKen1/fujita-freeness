/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModelThresholdLocalization

/-!
Conormal differentials and prescribed étale coordinates (step 9, restriction theorem).

For a surjection A → B and a B-algebra F (a residue field), the map F ⊗_A Ω_A → F ⊗_B Ω_B is
surjective, and its kernel is spanned by the differentials of the kernel of A → B: the conormal
sequence I/I² → B ⊗_A Ω_A → Ω_B → 0 stays exact after F ⊗_B − (right exactness). So if all these
differentials vanish, the map is injective (`residueKaehlerMap_injective_of_forall_ker`), and if
F ⊗_B Ω_B has smaller dimension, some element of the kernel has a nonzero differential at the
point (`exists_mem_ker_tmul_D_ne_zero`). For a smooth closed subvariety of positive codimension
this is an element of its ideal with a nonzero differential at a point, the first step of the
induction on the codimension in the restriction theorem.

Functions on a smooth affine scheme with independent differentials at a K-point are étale
coordinates on a basic open around the point
(`exists_away_formallyEtale_of_differentialsIndependentAt`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
open KaehlerDifferential

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Conormal

variable (K : Type*) [CommRing K] {A B : Type*} [CommRing A] [CommRing B] [Algebra K A]
  [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  (F : Type*) [CommRing F] [Algebra B F] [Algebra A F] [IsScalarTower A B F]

/-- If the differentials of the kernel of a surjection A → B vanish in F ⊗_A Ω_A, then
F ⊗_A Ω_A → F ⊗_B Ω_B is injective. -/
theorem residueKaehlerMap_injective_of_forall_ker (h : Function.Surjective (algebraMap A B))
    (hI : ∀ t ∈ RingHom.ker (algebraMap A B), (1 : F) ⊗ₜ[A] D K A t = 0) :
    Function.Injective (residueKaehlerMap K (R := A) (O' := B) F) := by
  have hex : Function.Exact (LinearMap.lTensor F (LinearMap.ker (mapBaseChange K A B)).subtype)
      (LinearMap.lTensor F (mapBaseChange K A B)) :=
    lTensor_exact F (LinearMap.exact_subtype_ker_map _) (mapBaseChange_surjective K A B h)
  have hzero : ∀ z, LinearMap.lTensor F (LinearMap.ker (mapBaseChange K A B)).subtype z = 0 := by
    intro z
    induction z with
    | tmul k x =>
      rw [LinearMap.lTensor_tmul]
      obtain ⟨c, hc⟩ : (x : B ⊗[A] Ω[A⁄K]) ∈ LinearMap.range (kerCotangentToTensor K A B) := by
        rw [range_kerCotangentToTensor K A B h]
        exact x.2
      obtain ⟨t, rfl⟩ := Ideal.toCotangent_surjective _ c
      rw [Submodule.coe_subtype, ← hc, kerCotangentToTensor_toCotangent]
      apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B F F Ω[A⁄K]).injective
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, map_zero, one_smul]
      have h1 : k ⊗ₜ[A] D K A (t : A) = k • ((1 : F) ⊗ₜ[A] D K A (t : A)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, hI t t.2, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have hinj : Function.Injective (LinearMap.lTensor F (mapBaseChange K A B)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (hex z).mp hz
    exact hzero w
  unfold residueKaehlerMap
  rw [LinearMap.coe_comp, TensorProduct.AlgebraTensorModule.coe_lTensor]
  exact hinj.comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B F F Ω[A⁄K]).symm.injective

end Conormal

section Exists

variable (K : Type*) [CommRing K] {A B : Type*} [CommRing A] [CommRing B] [Algebra K A]
  [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  (F : Type*) [Field F] [Algebra B F] [Algebra A F] [IsScalarTower A B F]

/-- If a surjection A → B lowers the dimension of the differentials at a point, some element of
the kernel has a nonzero differential at the point. -/
theorem exists_mem_ker_tmul_D_ne_zero (h : Function.Surjective (algebraMap A B))
    [FiniteDimensional F (F ⊗[B] Ω[B⁄K])]
    (hlt : Module.finrank F (F ⊗[B] Ω[B⁄K]) < Module.finrank F (F ⊗[A] Ω[A⁄K])) :
    ∃ t ∈ RingHom.ker (algebraMap A B), (1 : F) ⊗ₜ[A] D K A t ≠ 0 := by
  by_contra hno
  push Not at hno
  have hinj := residueKaehlerMap_injective_of_forall_ker K F h hno
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

end Exists

section AwayCoordinates

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsAffine X]
  {N : ℕ} [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- Functions with independent differentials at a K-point of a smooth affine scheme are étale
coordinates on a basic open around the point. -/
theorem exists_away_formallyEtale_of_differentialsIndependentAt (x : X)
    (χ : Γ(X, ⊤) →ₐ[K] K)
    (hχ : ∀ a, χ a = 0 ↔ a ∈ ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal)
    (u : Fin N → Γ(X, ⊤)) (hu : DifferentialsIndependentAt K χ u) :
    ∃ b : Γ(X, ⊤), χ b ≠ 0 ∧
      (MvPolynomial.aeval (R := K)
        (fun l => algebraMap Γ(X, ⊤) (Localization.Away b) (u l))).toRingHom.FormallyEtale := by
  obtain ⟨c, hxc, hle, hc⟩ :=
    exists_etaleChart_of_differentialsIndependentAt (isAffineOpen_top X) x trivial χ hχ u hu
  obtain ⟨b, hbc, hxb⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := c.U) ⟨x, hxc⟩ trivial
  refine ⟨b, fun h0 => ?_, ?_⟩
  · exact (mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top X) x trivial b).mp hxb
      ((hχ b).mp h0)
  · have := isScalarTower_top_basicOpen (K := K) b
    let φ₁ : MvPolynomial (Fin N) K →ₐ[K] Γ(X, X.basicOpen b) :=
      (sectionOpenRestrictionAlgHom (K := K) hbc).comp c.coords
    have hφ₁ : φ₁.toRingHom.FormallyEtale := formallyEtale_comp _
      (affineOpenRestriction_formallyEtale ⟨c.U, c.isAffine⟩
        ⟨X.basicOpen b, (isAffineOpen_top X).basicOpen b⟩ hbc) _ c.formallyEtale
    let e : Localization.Away b ≃ₐ[Γ(X, ⊤)] Γ(X, X.basicOpen b) :=
      IsLocalization.algEquiv (Submonoid.powers b) _ _
    let eK : Localization.Away b ≃ₐ[K] Γ(X, X.basicOpen b) := e.restrictScalars K
    have heq : MvPolynomial.aeval (R := K)
        (fun l => algebraMap Γ(X, ⊤) (Localization.Away b) (u l)) =
        eK.symm.toAlgHom.comp φ₁ := by
      apply MvPolynomial.algHom_ext
      intro l
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply]
      have h1 : φ₁ (MvPolynomial.X l) = algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b) (u l) := by
        change X.presheaf.map (homOfLE hbc).op (c.coords (MvPolynomial.X l)) = _
        rw [hc l, presheaf_map_map_eq]
        rfl
      rw [h1]
      change _ = e.symm (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b) (u l))
      rw [AlgEquiv.commutes]
    rw [heq]
    exact formallyEtale_comp _ (ringHom_formallyEtale_of_etale _
      (RingHom.Etale.of_bijective eK.symm.bijective)) _ hφ₁

end AwayCoordinates

section Rank

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  {N : ℕ} [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- At a K-point of an affine open of a smooth scheme of relative dimension N, the differentials
of the sections span an N-dimensional space (the map to the differentials of the stalk is
bijective: injective as the stalk is a localization, surjective as the differentials of
sections span). -/
theorem finrank_tmul_kaehler_eq {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ V)
    (χ : Γ(X, V) →ₐ[K] K) (hχ : ∀ a, χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    letI := χ.toRingHom.toAlgebra
    FiniteDimensional K (K ⊗[Γ(X, V)] Ω[Γ(X, V)⁄K]) ∧
      Module.finrank K (K ⊗[Γ(X, V)] Ω[Γ(X, V)⁄K]) = N := by
  letI : Algebra Γ(X, V) K := χ.toRingHom.toAlgebra
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk (⟨x, hx⟩ : V)
  haveI := cartierBaseOpenLocalScalarTower (K := K) x hx
  obtain ⟨ev, hev, -⟩ := exists_stalk_evaluation hV x hx χ hχ
  letI : Algebra (X.presheaf.stalk x) K := ev.toAlgebra
  haveI : IsScalarTower Γ(X, V) (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq fun a => (hev a).symm
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K X N, x ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := N)).symm ▸ Opens.mem_top x)
  have hb := (etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale c x hc)).baseChange K
  haveI : Algebra.FormallySmooth Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (Rₘ := X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have hinj := residueKaehlerMap_injective K (R := Γ(X, V)) (O' := X.presheaf.stalk x) K
  have hsurj : Function.Surjective
      (residueKaehlerMap K (R := Γ(X, V)) (O' := X.presheaf.stalk x) K) := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← span_tmul_D_algebraMap_eq_top K (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact ⟨1 ⊗ₜ D K Γ(X, V) r, residueKaehlerMap_tmul K K 1 r⟩
  let e := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  haveI : FiniteDimensional K (K ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄K]) :=
    Module.Finite.of_basis hb
  haveI : FiniteDimensional K (K ⊗[Γ(X, V)] Ω[Γ(X, V)⁄K]) := Module.Finite.equiv e.symm
  refine ⟨inferInstance, ?_⟩
  rw [e.finrank_eq, Module.finrank_eq_card_basis hb, Fintype.card_fin]

end Rank

end MixedFujita
