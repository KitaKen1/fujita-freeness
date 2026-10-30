/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineSectionsSpecProduct

/-!
A smooth affine chart of a resolution of a prime (step 9). Let R be a finitely generated algebra
over an algebraically closed field K of characteristic zero, 𝔭 a prime of R and χ₀ a K-point of R
on V(𝔭). A proper smooth birational model T of Spec(R/𝔭) (an SNC model of the pair with zero
boundary, through a smooth chart of Spec(R/𝔭)) is surjective; an affine open W of T around a
closed point over χ₀ gives a smooth finitely generated domain B = Γ(W) with a K-algebra map
Φ : R → B whose kernel is 𝔭, a common denominator t ∉ 𝔭 with B ⊆ Φ(R)[1/Φ t], and a K-point of B
over χ₀ (`exists_resolution_chart_of_prime`). Along such a Φ, every K-point χ of R with χ t ≠ 0
that kills 𝔭 extends to a K-point of B (`exists_algHom_comp_eq_of_denominator`); hence K-points of
R dense in V(𝔭) lift to K-points of B dense in Spec B, even inside a basic open
(`eq_zero_of_forall_lift_mem`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Extension

variable {K R B : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing B] [Algebra K B]

/-- A K-point χ of R extends along Φ : R → B when every element of B becomes an image of R after
multiplication by a power of Φ t, χ t ≠ 0 and χ kills the kernel of Φ. -/
theorem exists_algHom_comp_eq_of_denominator (Φ : R →ₐ[K] B) (t : R)
    (ht : ∀ b : B, ∃ (N : ℕ) (r : R), Φ t ^ N * b = Φ r) (χ : R →ₐ[K] K)
    (hker : ∀ r, Φ r = 0 → χ r = 0) (hχt : χ t ≠ 0) :
    ∃ w : B →ₐ[K] K, w.comp Φ = χ := by
  classical
  choose N r hr using ht
  have hpow : ∀ k : ℕ, χ t ^ k ≠ 0 := fun k => pow_ne_zero k hχt
  have key : ∀ (b : B) (N' : ℕ) (r' : R), Φ t ^ N' * b = Φ r' →
      χ r' * χ t ^ N b = χ (r b) * χ t ^ N' := by
    intro b N' r' h'
    have h1 : Φ (r' * t ^ N b) = Φ (r b * t ^ N') := by
      rw [map_mul, map_mul, ← h', map_pow, map_pow, ← hr b]
      ring
    have h2 : χ (r' * t ^ N b - r b * t ^ N') = 0 := hker _ (by rw [map_sub, h1, sub_self])
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, sub_eq_zero] at h2
    exact h2
  let w : B → K := fun b => χ (r b) / χ t ^ N b
  have hw : ∀ (b : B) (N' : ℕ) (r' : R), Φ t ^ N' * b = Φ r' → w b = χ r' / χ t ^ N' := by
    intro b N' r' h'
    have h := key b N' r' h'
    change χ (r b) / χ t ^ N b = χ r' / χ t ^ N'
    rw [div_eq_div_iff (hpow _) (hpow _)]
    linear_combination -h
  refine ⟨
    { toFun := w
      map_one' := by
        rw [hw 1 0 1 (by simp)]
        simp
      map_mul' := by
        intro b b'
        rw [hw (b * b') (N b + N b') (r b * r b') (by rw [map_mul, ← hr b, ← hr b']; ring),
          hw b (N b) (r b) (hr b), hw b' (N b') (r b') (hr b'), map_mul, pow_add]
        field_simp
      map_zero' := by
        rw [hw 0 0 0 (by simp)]
        simp
      map_add' := by
        intro b b'
        rw [hw (b + b') (N b + N b') (r b * t ^ N b' + r b' * t ^ N b)
          (by rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hr b, ← hr b']; ring),
          hw b (N b) (r b) (hr b), hw b' (N b') (r b') (hr b'), map_add, map_mul, map_mul,
          map_pow, map_pow, pow_add]
        field_simp
      commutes' := by
        intro k
        rw [hw (algebraMap K B k) 0 (algebraMap K R k) (by simp), AlgHom.commutes]
        simp }, ?_⟩
  ext r'
  change w (Φ r') = χ r'
  rw [hw (Φ r') 0 r' (by simp)]
  simp

/-- K-points of R killing 𝔭 with I(D) = 𝔭 lift along Φ to K-points of B that are dense in B,
even inside the basic open of a nonzero h. -/
theorem eq_zero_of_forall_lift_mem [IsDomain B] (Φ : R →ₐ[K] B) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hΦ𝔭 : ∀ r ∈ 𝔭, Φ r = 0) (hker : ∀ r, Φ r = 0 → r ∈ 𝔭) (t : R) (ht𝔭 : t ∉ 𝔭)
    (ht : ∀ b : B, ∃ (N : ℕ) (r : R), Φ t ^ N * b = Φ r) (D : Set (R →ₐ[K] K))
    (hD𝔭 : ∀ χ ∈ D, ∀ r ∈ 𝔭, χ r = 0) (hD : ∀ r, (∀ χ ∈ D, χ r = 0) → r ∈ 𝔭) {h : B}
    (hh : h ≠ 0) {f : B} (hf : ∀ w : B →ₐ[K] K, w h ≠ 0 → w.comp Φ ∈ D → w f = 0) : f = 0 := by
  obtain ⟨N, s, hs⟩ := ht (f * h)
  have hΦt : Φ t ≠ 0 := fun h0 => ht𝔭 (hker t h0)
  -- the numerator vanishes on D
  have hsD : ∀ χ ∈ D, χ (s * t) = 0 := by
    intro χ hχ
    by_cases hχt : χ t = 0
    · rw [map_mul, hχt, mul_zero]
    · obtain ⟨w, hw⟩ := exists_algHom_comp_eq_of_denominator Φ t ht χ
        (fun r hr => hD𝔭 χ hχ r (hker r hr)) hχt
      have hwΦ : ∀ r, w (Φ r) = χ r := fun r => congrArg (fun φ : R →ₐ[K] K => φ r) hw
      have hval : χ s = w (Φ t) ^ N * (w f * w h) := by
        rw [← hwΦ, ← hs, map_mul, map_mul, map_pow]
      by_cases hwh : w h = 0
      · rw [map_mul, hval, hwh, mul_zero, mul_zero, zero_mul]
      · rw [map_mul, hval, hf w hwh (hw ▸ hχ), zero_mul, mul_zero, zero_mul]
  have hst : s * t ∈ 𝔭 := hD _ hsD
  have hs𝔭 : s ∈ 𝔭 := (Ideal.IsPrime.mem_or_mem ‹_› hst).resolve_right ht𝔭
  rw [hΦ𝔭 s hs𝔭] at hs
  have hfh : f * h = 0 := (mul_eq_zero.mp hs).resolve_left (pow_ne_zero N hΦt)
  exact (mul_eq_zero.mp hfh).resolve_right hh

end Extension

section KPoints

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- Two K-points with the same zeros are equal. -/
theorem algHom_eq_of_forall_eq_zero_iff (φ φ' : R →ₐ[K] K) (h : ∀ r, φ r = 0 ↔ φ' r = 0) :
    φ = φ' := by
  ext r
  have h1 : φ' (r - algebraMap K R (φ' r)) = 0 := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have h2 := (h _).mpr h1
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h2
  exact h2

end KPoints

section Chart

variable {K : Type u} [Field K]

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

/-- The map of sections of a morphism over K, as a map of K-algebras. -/
def appLEAlgHom {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of K))]
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) →ₐ[K] Γ(X, V) where
  toRingHom := (f.appLE U V e).hom
  commutes' k := by
    have h : (Y.baseRingToStructurePresheaf K).app (op U) ≫ f.appLE U V e =
        (X.baseRingToStructurePresheaf K).app (op V) := by
      rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
        Scheme.baseRingToStructurePresheaf_app_eq_appLE, Category.assoc,
        Scheme.Hom.appLE_comp_appLE]
      simp only [HomIsOver.comp_over]
    exact ConcreteCategory.congr_hom h k

variable [IsAlgClosed K] [CharZero K]

/-- A smooth affine chart of a resolution of V(𝔭) through a K-point χ₀ on it: a smooth finitely
generated domain B with a K-algebra map Φ : R → B of kernel 𝔭, a common denominator t ∉ 𝔭 of the
elements of B, and a K-point of B over χ₀. -/
theorem exists_resolution_chart_of_prime {R : Type u} [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (𝔭 : Ideal R) [𝔭.IsPrime] (χ₀ : R →ₐ[K] K)
    (h₀ : ∀ r ∈ 𝔭, χ₀ r = 0) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B)
      (_ : Algebra.FiniteType K B) (d : ℕ)
      (_ : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B))))
      (Φ : R →ₐ[K] B) (t : R), (∀ r ∈ 𝔭, Φ r = 0) ∧ (∀ r, Φ r = 0 → r ∈ 𝔭) ∧ t ∉ 𝔭 ∧
      (∀ b : B, ∃ (N : ℕ) (r : R), Φ t ^ N * b = Φ r) ∧
      ∃ w₀ : B →ₐ[K] K, w₀.comp Φ = χ₀ := by
  classical
  -- the integral affine scheme of R/𝔭
  let Q := R ⧸ 𝔭
  let S := Spec (CommRingCat.of Q)
  have : LocallyOfFiniteType (S ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K Q)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : QuasiCompact (S ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated (S ↘ Spec (CommRingCat.of K)) := inferInstance
  let χq : Q →ₐ[K] K := Ideal.Quotient.liftₐ 𝔭 χ₀ h₀
  let s₀ : S := specAlgHomPoint χq
  -- a smooth chart of S and a proper smooth birational model
  obtain ⟨-, -, -, d, c, -⟩ := exists_closedPoint_etaleChart (K := K) (W := S) Set.univ
    isOpen_univ ⟨s₀, trivial⟩
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, -, -, -, -⟩ :=
    exists_proper_snc_model c (1 : S.functionFieldˣ) 1 0
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth d _
  -- ρ is surjective; a closed point of T over s₀ and an affine open around it
  have hsurj : Function.Surjective ρ := by
    have hclosed : IsClosed (Set.range ρ) := (Scheme.Hom.isClosedMap ρ).isClosed_range
    have hdense : Dense (Set.range ρ) := hdom.denseRange
    intro s
    have : s ∈ Set.range ρ := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
      trivial
    exact this
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace (T ↘ Spec (CommRingCat.of K))
  obtain ⟨t₁, ht₁⟩ := hsurj s₀
  obtain ⟨t₀, ht₀F, ht₀c⟩ := nonempty_inter_closedPoints (Z := ρ ⁻¹' {s₀}) ⟨t₁, ht₁⟩
    ((specAlgHomPoint_isClosed χq).preimage ρ.continuous).isLocallyClosed
  obtain ⟨_, ⟨W, hW, rfl⟩, ht₀W, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t₀) isOpen_univ
  have : Nonempty W := ⟨⟨t₀, ht₀W⟩⟩
  have ht₀ : ρ t₀ = s₀ := ht₀F
  have ht₀closed : IsClosed ({t₀} : Set T) := ht₀c
  -- the sections over W
  have hFT : Algebra.FiniteType K Γ(T, W) := smooth_affineOpen_finiteType (n := d) hW
  have hsm : SmoothOfRelativeDimension d
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(T, W)))) :=
    smoothOfRelativeDimension_spec_sections hW
  -- the map Φ : R → Γ(T, W)
  have e : W ≤ ρ ⁻¹ᵁ (⊤ : S.Opens) := fun x _ => trivial
  let ψS : Q →ₐ[K] Γ(S, ⊤) :=
    { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
      commutes' := fun k => (specAlgebraOver_algebraMap Q k).symm }
  let Φ : R →ₐ[K] Γ(T, W) := (appLEAlgHom ρ ⊤ W e).comp (ψS.comp (Ideal.Quotient.mkₐ K 𝔭))
  have hΦ : ∀ r, Φ r = ρ.appLE ⊤ W e
      ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv (Ideal.Quotient.mk 𝔭 r)) := fun r => rfl
  have hinj : Function.Injective (ρ.appLE ⊤ W e) := by
    intro a b hab
    apply S.germToFunctionField_injective ⊤
    apply (dominantFunctionFieldMap ρ).hom.injective
    rw [dominantFunctionFieldMap_germ ρ ⊤ W e a, dominantFunctionFieldMap_germ ρ ⊤ W e b, hab]
  have hker : ∀ r, Φ r = 0 → r ∈ 𝔭 := by
    intro r hr
    rw [hΦ] at hr
    have h1 := hinj (hr.trans (map_zero _).symm)
    have h2 : Ideal.Quotient.mk 𝔭 r = 0 := by
      have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).hom h1
      simpa using h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hΦ𝔭 : ∀ r ∈ 𝔭, Φ r = 0 := by
    intro r hr
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]
  -- every section over W has a denominator from R
  have hfrac : ∀ b : Γ(T, W), ∃ (a s : R), s ∉ 𝔭 ∧ Φ s * b = Φ a := by
    intro b
    have : IsFractionRing Γ(S, ⊤) S.functionField :=
      functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
    obtain ⟨q, hq⟩ := hρ.2 (T.germToFunctionField W b)
    obtain ⟨a', s', hs', hq'⟩ := IsFractionRing.div_surjective (A := Γ(S, ⊤)) q
    have hs'0 : s' ≠ 0 := nonZeroDivisors.ne_zero hs'
    have hgs' : S.germToFunctionField ⊤ s' ≠ 0 := fun h0 =>
      hs'0 (S.germToFunctionField_injective ⊤ (h0.trans (map_zero _).symm))
    have hq2 : q * S.germToFunctionField ⊤ s' = S.germToFunctionField ⊤ a' := by
      rw [← hq']
      change algebraMap Γ(S, ⊤) S.functionField a' / algebraMap Γ(S, ⊤) S.functionField s' *
        algebraMap Γ(S, ⊤) S.functionField s' = algebraMap Γ(S, ⊤) S.functionField a'
      exact div_mul_cancel₀ _ hgs'
    have hq3 := congrArg (dominantFunctionFieldMap ρ).hom hq2
    rw [map_mul, dominantFunctionFieldMap_germ ρ ⊤ W e s',
      dominantFunctionFieldMap_germ ρ ⊤ W e a'] at hq3
    have hq4 : (dominantFunctionFieldMap ρ).hom q = T.germToFunctionField W b := hq
    rw [hq4, ← map_mul] at hq3
    have hb : ρ.appLE ⊤ W e s' * b = ρ.appLE ⊤ W e a' := by
      have := T.germToFunctionField_injective W hq3
      rw [mul_comm] at this
      exact this
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom a')
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom s')
    have hinv : ∀ x : Γ(S, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Q)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom x) = x :=
      fun x => Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of Q)) x
    refine ⟨a, s, fun hs𝔭 => hs'0 ?_, ?_⟩
    · have h0 : (Scheme.ΓSpecIso (CommRingCat.of Q)).hom s' = 0 := by
        rw [← hs]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hs𝔭
      rw [← hinv s', h0, map_zero]
    · rw [hΦ, hΦ, hs, ha, hinv, hinv]
      exact hb
  choose a s hs𝔭 hab using hfrac
  obtain ⟨G, hG⟩ := hFT.out
  let t : R := ∏ b ∈ G, s b
  have ht𝔭 : t ∉ 𝔭 := by
    intro h
    obtain ⟨b, -, hsb⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hs𝔭 b hsb
  have hgen : ∀ b ∈ G, ∃ r, Φ t * b = Φ r := by
    intro b hb
    refine ⟨(∏ b' ∈ G.erase b, s b') * a b, ?_⟩
    have htb : t = (∏ b' ∈ G.erase b, s b') * s b := (Finset.prod_erase_mul _ _ hb).symm
    rw [htb, map_mul, map_mul, mul_assoc, hab b]
  have hden : ∀ x : Γ(T, W), ∃ (N : ℕ) (r : R), Φ t ^ N * x = Φ r := by
    intro x
    have hx : x ∈ Algebra.adjoin K (G : Set Γ(T, W)) := by
      rw [hG]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨r, hr⟩ := hgen x hx
      exact ⟨1, r, by rw [pow_one]; exact hr⟩
    | algebraMap k =>
      exact ⟨0, algebraMap K R k, by rw [pow_zero, one_mul, AlgHom.commutes]⟩
    | add x y _ _ hx hy =>
      obtain ⟨N, r, hr⟩ := hx
      obtain ⟨N', r', hr'⟩ := hy
      refine ⟨N + N', r * t ^ N' + r' * t ^ N, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hr, ← hr', pow_add]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨N, r, hr⟩ := hx
      obtain ⟨N', r', hr'⟩ := hy
      refine ⟨N + N', r * r', ?_⟩
      rw [map_mul, ← hr, ← hr', pow_add]
      ring
  -- the K-point of the closed point over χ₀
  have hmax : (hW.primeIdealOf ⟨t₀, ht₀W⟩).asIdeal.IsMaximal :=
    hW.primeIdealOf_isMaximal_of_isClosed ⟨t₀, ht₀W⟩ ht₀closed
  let w₀ : Γ(T, W) →ₐ[K] K :=
    closedPointEvaluation (K := K) (hW.primeIdealOf ⟨t₀, ht₀W⟩).asIdeal
  have hw₀ : w₀.comp Φ = χ₀ := by
    apply algHom_eq_of_forall_eq_zero_iff
    intro r
    change w₀ (Φ r) = 0 ↔ χ₀ r = 0
    rw [closedPointEvaluation_eq_zero_iff (K := K), ← not_iff_not,
      ← mem_basicOpen_iff_notMem_primeIdealOf hW t₀ ht₀W, hΦ, Scheme.basicOpen_appLE]
    change t₀ ∈ W ∧ ρ t₀ ∈ S.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv
      (Ideal.Quotient.mk 𝔭 r)) ↔ ¬ χ₀ r = 0
    rw [basicOpen_eq_of_affine, ht₀]
    change t₀ ∈ W ∧ Ideal.Quotient.mk 𝔭 r ∉ RingHom.ker χq.toRingHom ↔ ¬ χ₀ r = 0
    rw [RingHom.mem_ker]
    exact ⟨fun h => h.2, fun h => ⟨ht₀W, h⟩⟩
  exact ⟨Γ(T, W), inferInstance, inferInstance, inferInstance, hFT, d, hsm, Φ, t, hΦ𝔭, hker,
    ht𝔭, hden, w₀, hw₀⟩

end Chart

end MixedFujita
