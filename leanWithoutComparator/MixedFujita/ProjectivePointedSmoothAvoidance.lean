/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedGlobalSmooth
public import MixedFujita.FiniteSubmoduleParameterAvoidance
public import MixedFujita.ProjectivePointedFirstOrderAvoidance

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierBaseOpenAlgebra cartierBaseLocalAlgebra cartierBaseGlobalAlgebra
variable {K : Type u} [Field K] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {n : ℕ}
theorem polynomialProjective_pointed_global_smooth_cartierCut
    [CharZero K] [IsAlgClosed K] [IsIntegral Y]
    [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 0 < d)
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (F : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : F.val ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ (∀ y ∈ Z, y ∉ Set.range I.subschemeι) ∧
        Smooth (I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))) := by
  classical
  have hpos : 0 < topologicalKrullDim Y := by rw [hdim]; exact_mod_cast hd
  obtain ⟨k, hxk, F₀, hF₀x, hF₀gen, hF₀Z, _⟩ :=
    polynomialProjective_smooth_positive_dimension_pointed_order_one_finite_avoidance e
      hpos x hx Z hZ hxZ
  let P := polynomialProjectiveVanishingForms 1 (e x)
  have : Module.Free K P := Module.Free.of_divisionRing K P
  have : FiniteDimensional K P := inferInstance
  let ι := ULift.{u} (Fin (Module.finrank K P))
  let b : Module.Basis ι K P := (Module.finBasis K P).reindex Equiv.ulift.symm
  let q : Option Z → Submodule K P := fun z => match z with
    | none => (polynomialProjectiveVanishingForms 1 (e (genericPoint Y))).comap P.subtype
    | some y => (polynomialProjectiveVanishingForms 1 (e y.val)).comap P.subtype
  let F₀' : P := ⟨F₀, hF₀x⟩
  have hq (z : Option Z) : F₀' ∉ q z := by
    cases z with
    | none => exact hF₀gen
    | some y => exact hF₀Z y.val y.property
  let : Fintype Z := hZ.fintype
  obtain ⟨p₀, hp₀, hsmooth⟩ := projectivePointedBasis_general_smooth_hypersurface e he d hdim hd x hx b
  obtain ⟨p₁, hp₁, hguard⟩ := finiteSubmoduleAvoidance_parameter_polynomial
    (K := K) (M := P) b q F₀' hq
  obtain ⟨t, ht⟩ : ∃ t : ι → K, MvPolynomial.aeval t (p₀ * p₁) ≠ 0 := by
    by_contra! ht
    apply mul_ne_zero hp₀ hp₁
    apply MvPolynomial.funext
    intro t
    simpa only [MvPolynomial.aeval_eq_eval, map_zero] using ht t
  have ht' : MvPolynomial.aeval t p₀ ≠ 0 ∧ MvPolynomial.aeval t p₁ ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using ht
  let F' : P := ∑ i, t i • b i
  let F := F'.val
  have hgeneric : F.val ∉ (e (genericPoint Y)).asHomogeneousIdeal := hguard t ht'.2 none
  let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
  refine ⟨F, hgeneric,
    ⟨projectivePullbackCartierIdealPresentation e 1 F.val F.property Nat.zero_lt_one hgeneric⟩,
    ?_, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.range_subschemeι]
    exact (projectivePullbackCartierIdealSheaf_mem_support_iff e 1 F.val F.property
      Nat.zero_lt_one hgeneric x).mpr F'.property
  · intro y hy
    rw [Scheme.IdealSheafData.range_subschemeι]
    intro h
    exact hguard t ht'.2 (some ⟨y, hy⟩)
      ((projectivePullbackCartierIdealSheaf_mem_support_iff e 1 F.val F.property
        Nat.zero_lt_one hgeneric y).mp h)
  · change Smooth (I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K)))
    rw [show I = (projectiveHypersurfaceIdealSheaf F.val 1 F.property).comap e from
      projectivePullbackCartierIdealSheaf_eq_hypersurface_comap e 1 F.val F.property
        Nat.zero_lt_one hgeneric]
    exact hsmooth t ht'.1

end MixedFujita
