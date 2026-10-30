/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartDimension
public import MixedFujita.GeometricSmoothTaylor
public import MixedFujita.BlowUpChartSections
public import MixedFujita.RelativeCanonicalDivisor
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
Affine birational models over an étale chart (step 12, section 6.1 of the manuscript). Let c be
an étale chart of an integral scheme X over a field K, with ring of functions R, and let B be a
domain over K with a K-algebra map ψ : R → B which is injective and birational (every element of B
is a quotient of images of elements of R), and with étale coordinates v : K[u] → B. Then Spec B is
an integral, locally Noetherian scheme, smooth of relative dimension n over K, with a dominant
birational morphism σ to X over K and an étale chart with the coordinates v. If ψ sends the
coordinates of c to the polynomials φ(x_i) in the coordinates v, the function field map sends the
coordinates of c to φ of the coordinates of the new chart. A prime 𝔓 of B over the prime of a point
y of the chart, containing a nonzero v(p₀), gives a codimension-one point e of the model with y in
the closure of σ(e) at which v(p₀) vanishes: a minimal prime of v(p₀) inside 𝔓.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section General

/-- A dominant morphism of integral schemes is birational when, over an affine open of the
source lying over an open of the target, every function is a quotient of pulled back functions. -/
theorem dominantFunctionFieldMap_bijective_of_fractions {X U : Scheme.{u}} [IsIntegral X]
    [IsIntegral U] (σ : U ⟶ X) [IsDominant σ] (V : X.Opens) [Nonempty V] (W : U.Opens)
    (hW : IsAffineOpen W) [Nonempty W] (e : W ≤ σ ⁻¹ᵁ V)
    (h : ∀ b : Γ(U, W), ∃ r s : Γ(X, V), σ.appLE V W e s ≠ 0 ∧
      σ.appLE V W e s * b = σ.appLE V W e r) :
    Function.Bijective (dominantFunctionFieldMap σ).hom := by
  refine ⟨(dominantFunctionFieldMap σ).hom.injective, fun z => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen U W hW
  have hfrac : ∀ b : Γ(U, W), ∃ q : X.functionField,
      (dominantFunctionFieldMap σ).hom q = U.germToFunctionField W b := by
    intro b
    obtain ⟨r, s, hs, hrs⟩ := h b
    have hs' : U.germToFunctionField W (σ.appLE V W e s) ≠ 0 := fun h0 =>
      hs (Scheme.germToFunctionField_injective U W (h0.trans (map_zero _).symm))
    refine ⟨X.germToFunctionField V r / X.germToFunctionField V s, ?_⟩
    rw [map_div₀, dominantFunctionFieldMap_germ σ V W e, dominantFunctionFieldMap_germ σ V W e,
      div_eq_iff hs', ← map_mul, mul_comm, hrs]
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(U, W)) z
  obtain ⟨q₁, hq₁⟩ := hfrac b₁
  obtain ⟨q₂, hq₂⟩ := hfrac b₂
  refine ⟨q₁ / q₂, ?_⟩
  rw [map_div₀, hq₁, hq₂]
  rfl

/-- A function on the spectrum of a ring is invertible at a point exactly when it does not lie in
the prime ideal of the point. -/
theorem spec_germ_isUnit_iff (R : CommRingCat.{u}) (x : Spec R) (b : R) :
    IsUnit ((Spec R).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso R).inv b)) ↔
      b ∉ x.asIdeal := by
  rw [← (Spec R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso R).inv b) x trivial,
    basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen b x

end General

section SpecOver

variable {K : Type u} [Field K] (B : Type u) [CommRing B] [Algebra K B]

/-- The spectrum of an algebra over a field, as a scheme over the field. -/
@[instance_reducible]
noncomputable def specAlgebraOver : (Spec (CommRingCat.of B)).Over (Spec (CommRingCat.of K)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap K B))⟩

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- The base field acts on the global functions of the spectrum through the algebra. -/
theorem specAlgebraOver_algebraMap (k : K) :
    algebraMap K Γ(Spec (CommRingCat.of B), ⊤) k =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap K B k) := by
  change (((Spec (CommRingCat.of B)).baseRingToStructurePresheaf K).app (op ⊤)).hom k = _
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.comp_apply]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K B))) k
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  have h0 := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_eq_app (Spec.map (CommRingCat.ofHom (algebraMap K B))) (U := ⊤))
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k)
  exact h0.trans h.symm

variable {B}

/-- Polynomial coordinates on an algebra, as global coordinates of its spectrum. -/
noncomputable def specAlgebraCoords {n : ℕ} (v : MvPolynomial (Fin n) K →ₐ[K] B) :
    MvPolynomial (Fin n) K →ₐ[K] Γ(Spec (CommRingCat.of B), ⊤) where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.comp v.toRingHom
  commutes' k := by
    change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (v (algebraMap K _ k)) = algebraMap K _ k
    rw [v.commutes, specAlgebraOver_algebraMap]

theorem specAlgebraCoords_apply {n : ℕ} (v : MvPolynomial (Fin n) K →ₐ[K] B)
    (p : MvPolynomial (Fin n) K) :
    specAlgebraCoords v p = (Scheme.ΓSpecIso (CommRingCat.of B)).inv (v p) :=
  rfl

theorem specAlgebraCoords_formallyEtale {n : ℕ} (v : MvPolynomial (Fin n) K →ₐ[K] B)
    (hv : v.toRingHom.FormallyEtale) : (specAlgebraCoords v).toRingHom.FormallyEtale := by
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.FormallyEtale := by
    let _ : Algebra B Γ(Spec (CommRingCat.of B), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toAlgebra
    let e : B ≃ₐ[B] Γ(Spec (CommRingCat.of B), ⊤) :=
      { (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv with
        commutes' := fun _ => rfl }
    exact Algebra.FormallyEtale.of_equiv e
  exact RingHom.FormallyEtale.comp hv hiso

variable (B)

/-- The spectrum of a smooth algebra is smooth over the field. -/
theorem specAlgebraOver_smooth [Algebra.Smooth K B] :
    Smooth (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The spectrum of a smooth domain with n étale coordinates is smooth of relative dimension n
over the field. -/
theorem specAlgebraOver_smoothOfRelativeDimension [IsDomain B] [Algebra.Smooth K B] {n : ℕ}
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.FormallyEtale) :
    SmoothOfRelativeDimension n (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
  have := specAlgebraOver_smooth (K := K) B
  let cU : EtaleChart K (Spec (CommRingCat.of B)) n :=
    ⟨⊤, isAffineOpen_top _, ⟨⟨genericPoint _, trivial⟩⟩, specAlgebraCoords v,
      specAlgebraCoords_formallyEtale v hv⟩
  exact geometricSmoothScheme_relativeDimension n (etaleChart_topologicalKrullDim cU)

end SpecOver

section Morphism

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {V : X.Opens} (hV : IsAffineOpen V)

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- The spectrum of the functions of an affine open maps to the base field through the action of
the field on the functions. -/
theorem affineOpen_fromSpec_over_eq_specMap :
    hV.fromSpec ≫ (X ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, V))) := by
  apply ext_of_isAffine
  have e1 : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    rw [hV.fromSpec_preimage_self]
  have h1 : (hV.fromSpec ≫ (X ↘ Spec (CommRingCat.of K))).appTop =
      (X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [← affineOpen_fromSpec_appLE_self hV e1, Scheme.Hom.appLE_comp_appLE]
    exact (Scheme.Hom.appLE_eq_app _ (U := ⊤)).symm
  have h3 : CommRingCat.ofHom (algebraMap K Γ(X, V)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top := by
    rw [← Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    rfl
  have h2 : (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, V)))).appTop =
      (X ↘ Spec (CommRingCat.of K)).appLE ⊤ V le_top ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of K)).inv, ← Scheme.ΓSpecIso_inv_naturality,
      h3, Category.assoc]
    rfl
  rw [h1, h2]

variable (ψ : Γ(X, V) →ₐ[K] B)

/-- The morphism from the spectrum of an algebra receiving the functions of an affine open. -/
noncomputable def specAlgebraHom : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec

theorem specAlgebraHom_comp_over :
    specAlgebraHom hV ψ ≫ (X ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [specAlgebraHom, Category.assoc, affineOpen_fromSpec_over_eq_specMap, ← Spec.map_comp]
  congr 1
  ext k
  exact ψ.commutes k

theorem specAlgebraHom_isOver : (specAlgebraHom hV ψ).IsOver (Spec (CommRingCat.of K)) :=
  ⟨specAlgebraHom_comp_over hV ψ⟩

theorem specAlgebraHom_top_le :
    (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ specAlgebraHom hV ψ ⁻¹ᵁ V := by
  intro x _
  change hV.fromSpec (Spec.map (CommRingCat.ofHom ψ.toRingHom) x) ∈ (V : Set X)
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

/-- The functions of the affine open pull back to their images in the algebra. -/
theorem specAlgebraHom_appLE (r : Γ(X, V)) :
    (specAlgebraHom hV ψ).appLE V ⊤ (specAlgebraHom_top_le hV ψ) r =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (ψ r) := by
  have h := ConcreteCategory.congr_hom (affineOpen_appLE_Spec_map_fromSpec hV
    (CommRingCat.ofHom ψ.toRingHom) (specAlgebraHom_top_le hV ψ)) r
  rw [CommRingCat.comp_apply] at h
  exact h

/-- A point of the spectrum whose prime ideal contracts to the prime ideal of a point of the
affine open maps to that point. -/
theorem specAlgebraHom_apply_of_comap (x : Spec (CommRingCat.of B)) (y : X) (hy : y ∈ V)
    (h : x.asIdeal.comap ψ = (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    specAlgebraHom hV ψ x = y := by
  have h1 : Spec.map (CommRingCat.ofHom ψ.toRingHom) x = hV.primeIdealOf ⟨y, hy⟩ :=
    PrimeSpectrum.ext h
  change hV.fromSpec (Spec.map (CommRingCat.ofHom ψ.toRingHom) x) = y
  rw [h1, hV.fromSpec_primeIdealOf]

variable [IsIntegral X] [Nonempty V]

/-- The morphism is dominant when the algebra map is injective. -/
theorem specAlgebraHom_isDominant (hψ : Function.Injective ψ) :
    IsDominant (specAlgebraHom hV ψ) := by
  have h1 : IsDominant (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := by
    constructor
    change DenseRange (PrimeSpectrum.comap ψ.toRingHom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot ψ.toRingHom).mp hψ]
    exact bot_le
  have h2 : IsDominant hV.fromSpec := by
    constructor
    rw [DenseRange, hV.range_fromSpec]
    obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty V)
    exact V.isOpen.dense ⟨x, hx⟩
  exact inferInstanceAs (IsDominant (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec))

/-- The morphism is birational when the algebra is a domain and the algebra map is injective and
birational. -/
theorem specAlgebraHom_functionField_bijective [IsDomain B] (hψ : Function.Injective ψ)
    [IsDominant (specAlgebraHom hV ψ)]
    (hbir : ∀ b : B, ∃ r s : Γ(X, V), s ≠ 0 ∧ ψ s * b = ψ r) :
    Function.Bijective (dominantFunctionFieldMap (specAlgebraHom hV ψ)).hom := by
  have : Nonempty (⊤ : (Spec (CommRingCat.of B)).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of B)).inv :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).injective
  refine dominantFunctionFieldMap_bijective_of_fractions _ V ⊤ (isAffineOpen_top _)
    (specAlgebraHom_top_le hV ψ) fun b' => ?_
  obtain ⟨r, s, hs, hrs⟩ := hbir ((Scheme.ΓSpecIso (CommRingCat.of B)).hom b')
  refine ⟨r, s, ?_, ?_⟩
  · rw [specAlgebraHom_appLE]
    intro h0
    exact hs (hψ ((hinj (h0.trans (map_zero _).symm)).trans (map_zero ψ).symm))
  · rw [specAlgebraHom_appLE, specAlgebraHom_appLE, ← hrs, map_mul]
    congr 1
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) b').symm

end Morphism

section Model

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- An affine birational model over an étale chart, with a prime divisor over a given point: the
spectrum of a domain B with étale coordinates which is birational over the ring of the chart. -/
theorem exists_affine_birational_model (c : EtaleChart K X n) {B : Type u} [CommRing B]
    [IsDomain B] [Algebra K B] (ψ : Γ(X, c.U) →ₐ[K] B) (hψ : Function.Injective ψ)
    (hbir : ∀ b : B, ∃ r s : Γ(X, c.U), s ≠ 0 ∧ ψ s * b = ψ r)
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.Etale)
    (φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K)
    (hφ : ∀ p, ψ (c.coords p) = v (φ p)) (y : X) (hy : y ∈ c.U) (𝔓 : Ideal B) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap ψ = (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal)
    (p₀ : MvPolynomial (Fin n) K) (hp₀ : v p₀ ∈ 𝔓) (hp₀0 : v p₀ ≠ 0) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (_ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : U) (he : e ∈ cU.U),
      (∀ p, dominantFunctionFieldAlgHom (K := K) σ (etaleChartFunctionFieldCoords c p) =
        etaleChartFunctionFieldCoords cU (φ p)) ∧
      Order.coheight e = 1 ∧ y ∈ closure ({σ e} : Set X) ∧
      ¬ IsUnit (U.presheaf.germ cU.U e he (cU.coords p₀)) := by
  classical
  -- the algebra is smooth over the field and Noetherian
  let _ : Algebra (MvPolynomial (Fin n) K) B := v.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) B :=
    IsScalarTower.of_algebraMap_eq fun k => (v.commutes k).symm
  have hEt : Algebra.Etale (MvPolynomial (Fin n) K) B := hv
  have : Algebra.Smooth K (MvPolynomial (Fin n) K) := {}
  have hSm : Algebra.Smooth K B := Algebra.Smooth.comp K (MvPolynomial (Fin n) K) B
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have hvfe : v.toRingHom.FormallyEtale :=
    (Algebra.Etale.formallyEtale : Algebra.FormallyEtale (MvPolynomial (Fin n) K) B)
  have : Nonempty c.U := c.nonempty
  -- the model
  let instO : (Spec (CommRingCat.of B)).Over (Spec (CommRingCat.of K)) := specAlgebraOver B
  have hrel := specAlgebraOver_smoothOfRelativeDimension (K := K) B v hvfe
  have hdom := specAlgebraHom_isDominant c.isAffine ψ hψ
  have hover := specAlgebraHom_isOver c.isAffine ψ
  have hbij := specAlgebraHom_functionField_bijective c.isAffine ψ hψ hbir
  let cU : EtaleChart K (Spec (CommRingCat.of B)) n :=
    ⟨⊤, isAffineOpen_top _, ⟨⟨genericPoint _, trivial⟩⟩, specAlgebraCoords v,
      specAlgebraCoords_formallyEtale v hvfe⟩
  -- the prime divisor: a minimal prime of v(p₀) inside 𝔓
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {v p₀} ≤ 𝔓 from (Ideal.span_singleton_le_iff_mem _).mpr hp₀)
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hmem : v p₀ ∈ 𝔮 := h𝔮min.1.2 (Ideal.subset_span rfl)
  let e : Spec (CommRingCat.of B) := ⟨𝔮, h𝔮prime⟩
  let x𝔓 : Spec (CommRingCat.of B) := ⟨𝔓, inferInstance⟩
  refine ⟨Spec (CommRingCat.of B), inferInstance, inferInstance, instO, hrel,
    specAlgebraHom c.isAffine ψ, hdom, hover, hbij, cU, e, trivial, ?_, ?_, ?_, ?_⟩
  · intro p
    change (dominantFunctionFieldMap (specAlgebraHom c.isAffine ψ)).hom
        (X.germToFunctionField c.U (c.coords p)) =
      (Spec (CommRingCat.of B)).germToFunctionField ⊤ (specAlgebraCoords v (φ p))
    rw [dominantFunctionFieldMap_germ _ c.U ⊤ (specAlgebraHom_top_le c.isAffine ψ),
      specAlgebraHom_appLE, hφ]
    rfl
  · rw [← idealHeight_eq_coheight]
    change 𝔮.height = 1
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {v p₀}) 𝔮 h𝔮min
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      rintro rfl
      exact hp₀0 ((Submodule.mem_bot B).mp hmem)
  · have h1 : specAlgebraHom c.isAffine ψ x𝔓 = y :=
      specAlgebraHom_apply_of_comap c.isAffine ψ x𝔓 y hy h𝔓
    have hspec : e ⤳ x𝔓 := (PrimeSpectrum.le_iff_specializes e x𝔓).mp h𝔮le
    have h2 := hspec.map (specAlgebraHom c.isAffine ψ).continuous
    rw [h1] at h2
    exact h2.mem_closure
  · change ¬ IsUnit ((Spec (CommRingCat.of B)).presheaf.germ ⊤ e trivial
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (v p₀)))
    rw [spec_germ_isUnit_iff, not_not]
    exact hmem

end Model

end MixedFujita
