/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessStandardInputs

/-!
A semiample Cartier divisor of Iitaka dimension zero is principal (step 16; the case κ(D) = 0 of
§9.2).

Let X be an integral projective variety over an algebraically closed field K and D a Cartier
divisor all of whose sufficiently large multiples are globally generated, with κ(D) = 0, that is
h⁰(j D) bounded and positive infinitely often.

* If a multiple q D had two linearly independent sections s₀, s, the ratio t of their rational
  functions would not be a constant. Since K is algebraically closed, an element of the function
  field algebraic over K is a constant (`mem_range_of_isIntegral_of_isAlgClosed`), so t is
  transcendental and its powers are linearly independent. The products s^a s₀^(N − a) then give
  N + 1 linearly independent sections of N q D, against the bound on h⁰.
* So h⁰(q D) ≤ 1 for large q; every section is a multiple of one nonzero section s₀, which by
  global generation has a unit local coefficient at every point. Then the inverse of its rational
  function is a local equation of q D everywhere (`isLocalEquationAt_of_eq_unit_mul`), and q D is
  principal.
* With q and q + 1, D itself is principal
  (`principal_of_eventually_globallyGenerated_of_iitakaZero`).

Hence the case κ = 0 of `SemiampleContractionStatement` is a theorem, and the statement reduces to
its case κ ≥ 1 (`SemiampleContractionPositiveStatement`, `semiampleContraction_of_positive`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology Polynomial
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

section Algebra

/-- Over an algebraically closed field, an element of an extension field which is integral is in
the image of the base field. -/
theorem mem_range_of_isIntegral_of_isAlgClosed {k L : Type*} [Field k] [Field L] [IsAlgClosed k]
    [Algebra k L] {t : L} (ht : IsIntegral k t) : t ∈ Set.range (algebraMap k L) := by
  have h := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible ht)
  have hq := minpoly.monic ht
  have h0 : aeval t (minpoly k t) = 0 := minpoly.aeval k t
  rw [eq_X_add_C_of_degree_eq_one h, hq.leadingCoeff, C_1, one_mul, aeval_add, aeval_X,
    aeval_C, add_eq_zero_iff_eq_neg] at h0
  exact ⟨-(minpoly k t).coeff 0, by rw [map_neg]; exact h0.symm⟩

/-- The powers of a transcendental element are linearly independent. -/
theorem linearIndependent_pow_of_transcendental {k L : Type*} [Field k] [Field L] [Algebra k L]
    {t : L} (ht : Transcendental k t) : LinearIndependent k fun n : ℕ => t ^ n := by
  have hinj := transcendental_iff_injective.mp ht
  have h := (Polynomial.basisMonomials k).linearIndependent.map'
    (aeval t : k[X] →ₐ[k] L).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  convert h using 1
  funext n
  simp [Polynomial.coe_basisMonomials, aeval_monomial]

end Algebra

section LocalEquation

variable {X : Scheme.{u}} [IsIntegral X]

/-- A local equation multiplied by the inverse of a unit of the local ring is a local equation. -/
theorem isLocalEquationAt_of_eq_unit_mul {D : CartierDivisor X} {x : X} {f g : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) (u : (X.presheaf.stalk x)ˣ)
    (hfg : (f : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField u * g) :
    D.IsLocalEquationAt x g := by
  obtain ⟨V, hxV, a, ha⟩ := X.presheaf.exists_germ_eq
    ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hxW : x ∈ X.basicOpen a := (X.mem_basicOpen a x hxV).mpr (by rw [ha]; exact Units.isUnit _)
  have : Nonempty (X.basicOpen a : X.Opens) := ⟨⟨x, hxW⟩⟩
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  have h1 := isLocalEquationAt_regularUnit_mul hf (X.basicOpen a) hxW hu.unit
  have heq : regularUnitToFunctionField X (X.basicOpen a) hu.unit * f = g := by
    apply Units.ext
    have h2 : ((regularUnitToFunctionField X (X.basicOpen a) hu.unit : X.functionFieldˣ) :
        X.functionField) =
        X.germToFunctionField (X.basicOpen a)
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) := by
      rw [regularUnitToFunctionField_apply, Units.coe_map, IsUnit.unit_spec]
      rfl
    rw [Units.val_mul, h2, germToFunctionField_restrict X (X.basicOpen_le a) a,
      ← AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hxV a, ha, hfg,
      ← mul_assoc, ← map_mul,
      Units.inv_mul, map_one, one_mul]
  rw [← heq]
  exact h1

end LocalEquation

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

omit [IsAlgClosed K] in
/-- The local coefficient of a scalar multiple of a section. -/
theorem cartierLocalCoefficient_smul_base (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (c : K) (s : Γ(D.sheaf, ⊤)) :
    cartierLocalCoefficient D x f hf (c • s) =
      algebraMap K (X.presheaf.stalk x) c * cartierLocalCoefficient D x f hf s := by
  rw [LinearMap.map_smul_of_tower, Algebra.smul_def]

omit [IsAlgClosed K] in
/-- The rational function of a scalar multiple of a section. -/
theorem cartierSectionRational_smul_base (D : CartierDivisor X) (c : K) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionRational D (c • s) =
      algebraMap K X.functionField c * cartierSectionRational D s := by
  rw [LinearMap.map_smul_of_tower, Algebra.smul_def]

omit [IsAlgClosed K] in
/-- Products of powers of two sections of E are sections of the multiples of E. -/
theorem pow_mul_pow_mem_cartierSectionSpace (E : CartierDivisor X) (s₁ s₂ : Γ(E.sheaf, ⊤))
    (a b : ℕ) :
    cartierSectionRational E s₁ ^ a * cartierSectionRational E s₂ ^ b ∈
      cartierSectionSpace K ((a + b) • E) := by
  rw [add_nsmul]
  refine ⟨cartierSectionProduct (a • E) (b • E) (cartierSectionPower E s₁ a)
    (cartierSectionPower E s₂ b), ?_⟩
  change cartierSectionRational (a • E + b • E) _ = _
  rw [cartierSectionProduct_rational, cartierSectionPower_rational, cartierSectionPower_rational]

/-- A semiample Cartier divisor of Iitaka dimension zero on an integral projective variety over an
algebraically closed field is principal. -/
theorem principal_of_eventually_globallyGenerated_of_iitakaZero {n : ℕ}
    (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n)
    (hH : ∃ H : CartierDivisor X, CartierIsAmpleProj K H) (D : CartierDivisor X)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hk : CartierIitakaDimension K D 0) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  classical
  obtain ⟨H, hH⟩ := hH
  obtain ⟨q₀, hq₀⟩ := hgg
  obtain ⟨-, C, hC⟩ := hk
  have hfin : ∀ E : CartierDivisor X, FiniteDimensional K Γ(E.sheaf, ⊤) := fun E =>
    cartier_finiteDimensional_sections_of_ample hn hn1 hH E
  -- at most one independent section of q D for large q
  have hle1 : ∀ q, q₀ ≤ q → Module.finrank K Γ((q • D).sheaf, ⊤) ≤ 1 := by
    intro q hq
    by_contra hlt
    push Not at hlt
    have := hfin (q • D)
    obtain ⟨s₀, hs₀⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hq₀ q hq)
    obtain ⟨s, hind⟩ := exists_linearIndependent_pair_of_one_lt_finrank hlt hs₀
    have hne := (LinearIndependent.pair_iff' hs₀).mp hind
    set g₀ := cartierSectionRational (q • D) s₀ with hg₀
    set g := cartierSectionRational (q • D) s with hg
    have hg₀0 : g₀ ≠ 0 := fun h => hs₀ (cartierSectionRational_injective _
      (h.trans (map_zero _).symm))
    set t := g / g₀ with ht
    have htr : Transcendental K t := by
      intro halg
      obtain ⟨c, hc⟩ := mem_range_of_isIntegral_of_isAlgClosed halg.isIntegral
      apply hne c
      apply cartierSectionRational_injective (q • D)
      rw [cartierSectionRational_smul_base, hc, ← hg, ← hg₀, ht, div_mul_cancel₀ _ hg₀0]
    -- N + 1 independent sections of N q D
    have hlow : ∀ N : ℕ, N + 1 ≤ Module.finrank K Γ(((N * q) • D).sheaf, ⊤) := by
      intro N
      have hND : (N * q) • D = (N + 0) • (q • D) := by rw [add_zero, mul_nsmul']
      have := hfin ((N * q) • D)
      have hmem : ∀ a : Fin (N + 1), g ^ (a : ℕ) * g₀ ^ (N - a) ∈
          cartierSectionSpace K ((N * q) • D) := by
        intro a
        have h := pow_mul_pow_mem_cartierSectionSpace (K := K) (q • D) s s₀ a (N - a)
        rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp a.2), ← mul_nsmul'] at h
      have hval : ∀ a : Fin (N + 1), g ^ (a : ℕ) * g₀ ^ (N - a) = t ^ (a : ℕ) * g₀ ^ N := by
        intro a
        have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.mp a.2
        rw [ht, div_pow, ← pow_sub_mul_pow g₀ ha]
        field_simp
      have hli0 : LinearIndependent K fun a : Fin (N + 1) => t ^ (a : ℕ) * g₀ ^ N := by
        have h := (linearIndependent_pow_of_transcendental htr).comp (fun a : Fin (N + 1) =>
          (a : ℕ)) Fin.val_injective
        have hinj : Function.Injective (LinearMap.mulRight K (g₀ ^ N)) := fun y z hyz =>
          mul_right_cancel₀ (pow_ne_zero N hg₀0) hyz
        exact h.map' (LinearMap.mulRight K (g₀ ^ N)) (LinearMap.ker_eq_bot.mpr hinj)
      have hli : LinearIndependent K fun a : Fin (N + 1) =>
          (⟨g ^ (a : ℕ) * g₀ ^ (N - a), hmem a⟩ : cartierSectionSpace K ((N * q) • D)) := by
        apply LinearIndependent.of_comp (cartierSectionSpace K ((N * q) • D)).subtype
        convert hli0 using 1
        funext a
        exact hval a
      have : FiniteDimensional K (cartierSectionSpace K ((N * q) • D)) := by
        unfold cartierSectionSpace
        infer_instance
      have hcard := hli.fintype_card_le_finrank
      rwa [Fintype.card_fin, finrank_cartierSectionSpace] at hcard
    obtain ⟨N, hN⟩ := exists_nat_gt C
    have h1 := hC (N * q)
    have h2 := hlow N
    rw [pow_zero, mul_one] at h1
    have : ((N + 1 : ℕ) : ℝ) ≤ C := le_trans (by exact_mod_cast h2) h1
    push_cast at this
    linarith
  -- q D is principal for large q
  have hprin : ∀ q, q₀ ≤ q → ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ := by
    intro q hq
    have := hfin (q • D)
    obtain ⟨s₀, hs₀⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hq₀ q hq)
    have hspan : Submodule.span K {s₀} = ⊤ := by
      have h1 : Module.finrank K (Submodule.span K {s₀}) = 1 := finrank_span_singleton hs₀
      have h2 : Module.finrank K Γ((q • D).sheaf, ⊤) = 1 :=
        le_antisymm (hle1 q hq) (h1 ▸ Submodule.finrank_le _)
      apply Submodule.eq_top_of_finrank_eq
      rw [h1, h2]
    have hmul : ∀ s : Γ((q • D).sheaf, ⊤), ∃ c : K, c • s₀ = s := fun s =>
      Submodule.mem_span_singleton.mp (hspan ▸ Submodule.mem_top)
    have hunit : ∀ (x : X) (f : X.functionFieldˣ) (hf : (q • D).IsLocalEquationAt x f),
        IsUnit (cartierLocalCoefficient (q • D) x f hf s₀) := by
      intro x f hf
      obtain ⟨s, hs⟩ := hq₀ q hq x
      obtain ⟨c, rfl⟩ := hmul s
      rw [cartierLocalCoefficient_smul_base] at hs
      have hu := isUnit_of_mul_isUnit_right hs
      obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (q • D) x f _ hf
        (Classical.choose_spec ((q • D).exists_isLocalEquationAt x))
      rw [hv s₀]
      exact v.isUnit.mul hu
    refine ⟨(cartierSectionUnit (q • D) s₀ hs₀)⁻¹, ?_⟩
    apply cartierDivisor_eq_of_isLocalEquationAt
    intro x
    obtain ⟨f, hf⟩ := (q • D).exists_isLocalEquationAt x
    refine ⟨(cartierSectionUnit (q • D) s₀ hs₀)⁻¹, ?_,
      CartierDivisor.isLocalEquationAt_principalCartierDivisor x _⟩
    refine isLocalEquationAt_of_eq_unit_mul hf (hunit x f hf).unit ?_
    have hr : cartierSectionRational (q • D) s₀ ≠ 0 := fun h => hs₀
      (cartierSectionRational_injective _ (h.trans (map_zero _).symm))
    rw [IsUnit.unit_spec, cartierLocalCoefficient_image, Units.val_inv_eq_inv_val,
      cartierSectionUnit_val, mul_assoc, mul_inv_cancel₀ hr, mul_one]
  obtain ⟨φ₁, h₁⟩ := hprin (q₀ + 1) (by omega)
  obtain ⟨φ₀, h₀⟩ := hprin q₀ le_rfl
  refine ⟨φ₁ * φ₀⁻¹, ?_⟩
  have hD : D = (q₀ + 1) • D - q₀ • D := by
    rw [add_nsmul, one_nsmul]
    abel
  rw [hD, h₁, h₀, principalCartierDivisor_mul, principalCartierDivisor_inv]
  abel

/-- The contraction of a semiample divisor, for κ(D) ≥ 1 only: on a normal projective variety, if
every sufficiently large multiple of D is globally generated and κ(D) = k ≥ 1, there are a
contraction f : X → Y onto a normal projective variety of dimension k and an ample H on Y with
D ∼ f*H. -/
def SemiampleContractionPositiveStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ D : CartierDivisor X, (∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) →
      ∀ k : ℕ, CartierIitakaDimension K D k → 1 ≤ k →
        ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
          (_ : Y.Over (Spec (CommRingCat.of K)))
          (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))) (f : X ⟶ Y) (_ : IsDominant f)
          (_ : f.IsOver (Spec (CommRingCat.of K))) (H : CartierDivisor Y) (ψ : X.functionFieldˣ),
          topologicalKrullDim Y = k ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          CodimOneChartCovered k K Y ∧ (∀ V : Y.Opens, Function.Bijective (f.app V).hom) ∧
          CartierIsAmpleProj K H ∧ D = cartierPullback f H + principalCartierDivisor X ψ

/-- The contraction of a semiample divisor from its case κ ≥ 1: the case κ = 0 is proved. -/
theorem semiampleContraction_of_positive (h : SemiampleContractionPositiveStatement.{u}) :
    SemiampleContractionStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH D hgg k hk
  refine ⟨fun hk0 => ?_, fun hk1 => h K X n hdim hn hnorm hcov hH D hgg k hk hk1⟩
  subst hk0
  exact principal_of_eventually_globallyGenerated_of_iitakaZero hdim hn hH D hgg hk

/-- F2 from K-NF, the base point free theorem, the contraction of a semiample divisor for κ ≥ 1,
Kodaira's lemma, the perturbation of §9.3 and Ambro's canonical bundle formula. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_positiveInputs
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionPositiveStatement.{u}) (hkl : KodairaLemmaStatement.{u})
    (hpert : KltPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_standardInputs hKNF hbpf
    (semiampleContraction_of_positive hsa) hkl hpert hamb

end MixedFujita
