/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogDeligneIllusieInequality
public import MixedFujita.CanonicalTwistedForms

/-!
Kawamata–Viehweg vanishing from the logarithmic Deligne–Illusie inequality (step 10, R2).

**Top degree.** On a simple normal crossing chart the logarithmic `n`-forms at a point are
`f_E⁻¹ Ω^n_{X,x}`, where `f_E` is a local equation of `E = Σ_k E_k`. The top wedge of the
logarithmic basis is `Π_{j log} y_j⁻¹` times the top wedge of the coordinate basis, and
`f_E` is a unit times `Π_{j log} y_j`. So `Ω^n_X(log E)(N) = Ω^n_X(N + E)` as subsheaves of the
rational forms (`logFormsSheaf_top_eq`).

**Iteration.** The logarithmic Deligne–Illusie inequality goes from `M` to `p • M + Σ_k r_k • E_k`
with `0 ≤ r_k < p`. Starting from `L − E`, it reaches every `p^e • L − Σ_k D_k • E_k` with
`1 ≤ D_k ≤ p^e`: take `D'_k = ⌈D_k / p⌉` and `r_k = p D'_k − D_k`
(`logHodgeCount_le_of_logDeligneIllusie`).

**Vanishing.** Let `H = m L − Σ_k a_k • E_k` be ample with `0 ≤ a_k < m`, and write
`p^e = q m + s`. With `D_k = q a_k + 1` we get `p^e • L − Σ_k D_k • E_k = q • H + (s • L − E)`.
Serre vanishing for the finitely many sheaves `Ω^b(log E)(s • L − E)`, `s < m`, `b ≤ n`, kills the
right-hand side in total degrees `> n` for `e ≫ 0`. Hence `H^j(Ω^n(log E)(L − E)) = 0` for
`j ≥ 1`, and `Ω^n(log E)(L − E) = Ω^n(L) ≅ O(K_X + L)` (check 423) gives
`H^j(O(K_X + L)) = 0` (`canonical_vanishing_of_logDeligneIllusie`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

/-- **The exterior powers of a basis rescaled by units.** -/
theorem basisExteriorPower_unitsSMul_apply {I R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [LinearOrder I] (b : Module.Basis I R M) (w : I → Rˣ) (d : ℕ)
    (s : Set.powersetCard I d) :
    (b.unitsSMul w).exteriorPower d s =
      (∏ i, (w (Set.powersetCard.ofFinEmbEquiv.symm s i) : R)) • b.exteriorPower d s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family]
  have h : (⇑(b.unitsSMul w) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) =
      fun i => (w (Set.powersetCard.ofFinEmbEquiv.symm s i) : R) •
        b (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
    funext i
    rw [Function.comp_apply, Module.Basis.unitsSMul_apply, Units.smul_def]
  rw [h, AlternatingMap.map_smul_univ]
  rfl

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Chart

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))

/-- The top wedge of the logarithmic basis. -/
theorem logChartFormsBasis_top_apply (t : Set.powersetCard (Fin n) n) :
    logChartFormsBasis c σ n t =
      (∏ j, (logChartWeight c σ j : X.functionField)) • chartFormsBasis c n t := by
  change ((etaleChartBasis c).unitsSMul (logChartWeight c σ)).exteriorPower n t = _
  rw [basisExteriorPower_unitsSMul_apply]
  congr 1
  exact Fintype.prod_bijective _
    (Finite.injective_iff_bijective.mp (Set.powersetCard.ofFinEmbEquiv.symm t).injective) _ _
    (fun _ => rfl)

theorem logChartFormsBasis_top_repr (ω : RationalForms K X n) (t : Set.powersetCard (Fin n) n) :
    (logChartFormsBasis c σ n).repr ω t =
      (∏ j, (logChartWeight c σ j : X.functionField))⁻¹ * (chartFormsBasis c n).repr ω t := by
  have hb : logChartFormsBasis c σ n =
      (chartFormsBasis c n).unitsSMul (fun _ => ∏ j, logChartWeight c σ j) := by
    refine Module.Basis.eq_of_apply_eq fun t => ?_
    rw [Module.Basis.unitsSMul_apply, logChartFormsBasis_top_apply, Units.smul_def, Units.coe_prod]
  rw [hb, Module.Basis.repr_unitsSMul, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val,
    Units.coe_prod]

/-- **The product of the logarithmic weights is the inverse of the product of the component
equations.** -/
theorem prod_logChartWeight_mul_prod_sncChartComponentEquation
    (hσ : ∀ i j a, σ i = some a → σ j = some a → i = j) :
    (∏ j, (logChartWeight c σ j : X.functionField)) *
      ∏ k, (sncChartComponentEquation c σ k : X.functionField) = 1 := by
  have h1 : ∏ j, (logChartWeight c σ j : X.functionField) =
      ∏ j ∈ logSetOf σ, ((etaleChartCoordinateRationalUnit c j : X.functionField))⁻¹ := by
    rw [logSetOf, Finset.prod_filter]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [logChartWeight]
    split_ifs <;> simp [Units.val_inv_eq_inv_val]
  have h2 : ∏ k, (sncChartComponentEquation c σ k : X.functionField) =
      ∏ j ∈ logSetOf σ, (etaleChartCoordinateRationalUnit c j : X.functionField) := by
    rw [← Finset.prod_filter_of_ne (p := fun k => (σ k).isSome = true) (fun k _ hk => by
      by_contra h
      apply hk
      rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      rw [sncChartComponentEquation, h, Option.elim_none, Units.val_one])]
    refine Finset.prod_bij (fun k hk => (σ k).get (Finset.mem_filter.mp hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      exact (mem_logSetOf σ _).mpr ⟨k, (Option.some_get _).symm⟩
    · intro k₁ hk₁ k₂ hk₂ h
      exact hσ k₁ k₂ _ (Option.some_get _).symm (by rw [h]; exact (Option.some_get _).symm)
    · intro j hj
      obtain ⟨k, hk⟩ := (mem_logSetOf σ j).mp hj
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hk]; rfl⟩, ?_⟩
      simp only [hk, Option.get_some]
    · intro k hk
      have h := Option.some_get (Finset.mem_filter.mp hk).2
      rw [sncChartComponentEquation]
      conv_lhs => rw [← h]
      rfl
  rw [h1, h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => inv_mul_cancel₀ (Units.ne_zero _)

end Chart

theorem mem_range_algebraMap_unit_mul_iff (x : X) (v : (X.presheaf.stalk x)ˣ)
    (a : X.functionField) :
    algebraMap (X.presheaf.stalk x) X.functionField (v : X.presheaf.stalk x) * a ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      a ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨((v⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) * b, ?_⟩
    rw [map_mul, hb, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rintro ⟨b, rfl⟩
    exact ⟨(v : X.presheaf.stalk x) * b, map_mul _ _ _⟩

theorem isLocalEquationAt_sum_prod {r : ℕ} (E : Fin r → CartierDivisor X) {x : X}
    {h : Fin r → X.functionFieldˣ} (hh : ∀ k, (E k).IsLocalEquationAt x (h k)) :
    (∑ k, E k).IsLocalEquationAt x (∏ k, h k) := by
  have : ∀ T : Finset (Fin r), (∑ k ∈ T, E k).IsLocalEquationAt x (∏ k ∈ T, h k) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.prod_empty]
      exact CartierDivisor.isLocalEquationAt_zero x
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (hh a).mul ih
  exact this Finset.univ

section SNC

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

include hnorm hinj hξ hEc in
/-- **Logarithmic `n`-forms at a point are `f_E⁻¹ Ω^n_{X,x}`.** -/
theorem mem_logFormsLattice_top_iff (hsnc : IsSNCFamily K n ξ) (x : X) {f : X.functionFieldˣ}
    (hf : (∑ k, E k).IsLocalEquationAt x f) (ω : RationalForms K X n) :
    ω ∈ logFormsLattice K E x n ↔
      (f : X.functionField) • ω ∈ LinearMap.range (stalkFormsMap K n x) := by
  obtain ⟨c, σ, hxc, hc⟩ := hsnc x
  choose h hh u hu using fun k =>
    exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation hnorm ξ hinj hξ E hEc c σ hc x
      hxc k
  have hF := isLocalEquationAt_sum_prod E hh
  rw [smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf hF,
    mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hxc n ω,
    mem_range_stalkFormsMap_iff c n x hxc]
  have hprod : ((∏ k, h k : X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField ((∏ k, u k : (X.presheaf.stalk x)ˣ) :
        X.presheaf.stalk x) * (∏ j, (logChartWeight c σ j : X.functionField))⁻¹ := by
    rw [Units.coe_prod, Finset.prod_congr rfl (fun k _ => hu k), Finset.prod_mul_distrib,
      Units.coe_prod, map_prod]
    congr 1
    exact (eq_inv_of_mul_eq_one_right
      (prod_logChartWeight_mul_prod_sncChartComponentEquation c σ hc.1))
  refine forall_congr' fun t => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, logChartFormsBasis_top_repr, hprod, mul_assoc,
    mem_range_algebraMap_unit_mul_iff]

include hnorm hinj hξ hEc in
/-- **Top-degree logarithmic forms with poles bounded by `N` are the `n`-forms with poles bounded
by `N + E`.** -/
theorem logFormsSections_top_eq (hsnc : IsSNCFamily K n ξ) (N : CartierDivisor X) (U : X.Opens) :
    logFormsSections K E N n U = twistedFormsSections K (N + ∑ k, E k) n U := by
  ext s
  constructor
  · intro hs x hx f' hf'
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := N.exists_isLocalEquationAt x
    obtain ⟨g, hg⟩ := (∑ k, E k).exists_isLocalEquationAt x
    rw [smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf' (hf.mul hg), Units.val_mul,
      mul_comm, mul_smul]
    exact (mem_logFormsLattice_top_iff hnorm ξ hinj hξ E hEc hsnc x hg _).mp (hs x hx f hf)
  · intro hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨g, hg⟩ := (∑ k, E k).exists_isLocalEquationAt x
    refine (mem_logFormsLattice_top_iff hnorm ξ hinj hξ E hEc hsnc x hg _).mpr ?_
    have h := hs x hx _ (hf.mul hg)
    rwa [Units.val_mul, mul_comm, mul_smul] at h

include hnorm hinj hξ hEc in
/-- **`Ω^n_X(log E)(N) = Ω^n_X(N + E)`.** -/
theorem logFormsSheaf_top_eq (hsnc : IsSNCFamily K n ξ) (N : CartierDivisor X) :
    logFormsSheaf K E N n = twistedFormsSheaf K (N + ∑ k, E k) n := by
  have h : logFormsSubmodule K E N n = twistedFormsSubmodule K (N + ∑ k, E k) n :=
    SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U =>
      logFormsSections_top_eq hnorm ξ hinj hξ E hEc hsnc N U.unop)
  unfold logFormsSheaf twistedFormsSheaf
  rw [h]

end SNC

section Iteration

variable {r : ℕ} (E : Fin r → CartierDivisor X)

theorem logTwist_succ_eq (L : CartierDivisor X) (p e : ℕ) (D D' rr : Fin r → ℕ)
    (h : ∀ k, D k + rr k = p * D' k) :
    p • (p ^ e • L - ∑ k, D' k • E k) + ∑ k, rr k • E k = p ^ (e + 1) • L - ∑ k, D k • E k := by
  rw [smul_sub, smul_smul, ← pow_succ', Finset.smul_sum]
  have h2 : ∀ k, p • D' k • E k = D k • E k + rr k • E k := fun k => by
    rw [smul_smul, ← add_smul, h k]
  rw [Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_add_distrib]
  abel

/-- The predecessor in the iteration: `D'_k = ⌈D_k / p⌉`, `r_k = p D'_k − D_k`. -/
theorem exists_logTwist_pred (p e d : ℕ) (hp : 1 ≤ p) (h1 : 1 ≤ d) (h2 : d ≤ p ^ (e + 1)) :
    ∃ d' rr, 1 ≤ d' ∧ d' ≤ p ^ e ∧ rr < p ∧ d + rr = p * d' := by
  obtain ⟨q, hq⟩ : ∃ q, q = (d + p - 1) / p := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (d + p - 1) % p := ⟨_, rfl⟩
  have hdiv : p * q + t = d + p - 1 := by rw [hq, ht]; exact Nat.div_add_mod _ _
  have htp : t < p := by rw [ht]; exact Nat.mod_lt _ (by omega)
  have hpe : p ^ (e + 1) = p * p ^ e := pow_succ' p e
  refine ⟨q, p * q - d, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, mul_zero, zero_add] at hdiv
      omega
    · exact h0
  · have hlt : p * q < p * (p ^ e + 1) := by
      rw [mul_add, mul_one]
      generalize p * q = a at hdiv ⊢
      generalize p * p ^ e = b at hpe ⊢
      omega
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)
  · generalize p * q = a at hdiv ⊢
    omega
  · generalize p * q = a at hdiv ⊢
    omega

/-- **Iterating the logarithmic Deligne–Illusie inequality** from `L − E` to every
`p^e • L − Σ_k D_k • E_k` with `1 ≤ D_k ≤ p^e`. -/
theorem logHodgeCount_le_of_logDeligneIllusie (L : CartierDivisor X) (p : ℕ) (hp : 1 ≤ p)
    (d m : ℕ)
    (hDI : ∀ (e : ℕ) (D rr : Fin r → ℕ), (∀ k, rr k < p) →
      LogDeligneIllusieInequality K E (p ^ e • L - ∑ k, D k • E k) p rr d m)
    (e : ℕ) (D : Fin r → ℕ) (hD : ∀ k, 1 ≤ D k ∧ D k ≤ p ^ e) :
    logHodgeCount K E (L - ∑ k, E k) d m ≤ logHodgeCount K E (p ^ e • L - ∑ k, D k • E k) d m := by
  induction e generalizing D with
  | zero =>
    have hD1 : ∀ k, D k = 1 := fun k => by
      have := hD k
      rw [pow_zero] at this
      omega
    have h : p ^ 0 • L - ∑ k, D k • E k = L - ∑ k, E k := by
      rw [pow_zero, one_smul]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hD1 k, one_smul]
    rw [h]
  | succ e ih =>
    choose D' rr hD'1 hD'2 hrr hsum using fun k => exists_logTwist_pred p e (D k) hp (hD k).1 (hD k).2
    have h1 := ih D' fun k => ⟨hD'1 k, hD'2 k⟩
    have h2 := hDI e D' rr hrr
    unfold LogDeligneIllusieInequality at h2
    rw [logTwist_succ_eq E L p e D D' rr hsum] at h2
    exact h1.trans h2

end Iteration

section Vanishing

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hsnc : IsSNCFamily K n ξ)

include hnorm hinj hξ hEc hsnc in
/-- **Serre vanishing kills the logarithmic dimension count in total degrees `m > n`** for the
twists of finitely many divisors by large multiples of an ample divisor. -/
theorem exists_logHodgeCount_eq_zero (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (F : ℕ → CartierDivisor X) (S m : ℕ) (hm : n < m) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ s < S, logHodgeCount K E (q • H + F s) n m = 0 := by
  choose m₀ hm₀ using fun sb : ℕ × ℕ =>
    logFormsSheaf_serreVanishing hnorm ξ hinj hξ hEc hsnc H hH (F sb.1) sb.2
  refine ⟨∑ s ∈ Finset.range S, ∑ b ∈ Finset.range (n + 1), m₀ (s, b),
    fun q hq s hs => Finset.sum_eq_zero fun i hi => ?_⟩
  have hq' : m₀ (s, i) ≤ q :=
    le_trans (le_trans (Finset.single_le_sum (f := fun b => m₀ (s, b)) (fun _ _ => Nat.zero_le _) hi)
      (Finset.single_le_sum (f := fun s => ∑ b ∈ Finset.range (n + 1), m₀ (s, b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hs))) hq
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  obtain ⟨j, hj⟩ : ∃ j, m - i = j + 1 := ⟨m - i - 1, by omega⟩
  rw [hj]
  have := hm₀ (s, i) q hq' j
  exact Module.finrank_zero_of_subsingleton

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
include hnorm hinj hξ hEc hsnc in
/-- **Kawamata–Viehweg vanishing from the logarithmic Deligne–Illusie inequality**: if
`m • L − Σ_k a_k • E_k` is ample with `0 ≤ a_k < m` and the logarithmic Deligne–Illusie
inequality holds for the twists `p^e • L − Σ_k D_k • E_k` and `0 ≤ r_k < p` in every total degree
`> n`, then `H^j(O(K_X + L)) = 0` for `j ≥ 1`. -/
theorem canonical_vanishing_of_logDeligneIllusie [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (p : ℕ)
    (hp : 2 ≤ p) (L : CartierDivisor X) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (a : Fin r → ℕ)
    (ha : ∀ k, a k < m₀) (hamp : CartierIsAmpleProj K (m₀ • L - ∑ k, a k • E k))
    (hDI : ∀ (e : ℕ) (D rr : Fin r → ℕ), (∀ k, rr k < p) → ∀ m, n < m →
      LogDeligneIllusieInequality K E (p ^ e • L - ∑ k, D k • E k) p rr n m)
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + L).sheaf j) := by
  obtain ⟨q₀, hq₀⟩ := exists_logHodgeCount_eq_zero hnorm ξ hinj hξ E hEc hsnc
    (m₀ • L - ∑ k, a k • E k) hamp (fun s => s • L - ∑ k, E k) m₀ (n + j) (by omega)
  obtain ⟨e, he⟩ : ∃ e, m₀ * (q₀ + 1) ≤ p ^ e :=
    ⟨m₀ * (q₀ + 1), (Nat.lt_pow_self (by omega : 1 < p)).le⟩
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ e / m₀ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = p ^ e % m₀ := ⟨_, rfl⟩
  have hdiv : m₀ * q + s = p ^ e := by rw [hq, hs]; exact Nat.div_add_mod _ _
  have hsm : s < m₀ := by rw [hs]; exact Nat.mod_lt _ (by omega)
  have hqq : q₀ + 1 ≤ q := by
    rw [hq]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact he)
  have hD : ∀ k, 1 ≤ q * a k + 1 ∧ q * a k + 1 ≤ p ^ e := fun k => by
    refine ⟨by omega, ?_⟩
    have h1 : q * a k ≤ q * (m₀ - 1) := Nat.mul_le_mul_left q (by have := ha k; omega)
    rw [Nat.mul_sub_one] at h1
    have hB : q ≤ q * m₀ := Nat.le_mul_of_pos_right q (by omega)
    rw [← hdiv, mul_comm m₀ q]
    generalize q * a k = A at h1 ⊢
    generalize q * m₀ = B at h1 hB ⊢
    omega
  have hle := logHodgeCount_le_of_logDeligneIllusie E L p (by omega) n (n + j)
    (fun e D rr hrr => hDI e D rr hrr (n + j) (by omega)) e (fun k => q * a k + 1) hD
  have hdivisor : p ^ e • L - ∑ k, (q * a k + 1) • E k =
      q • (m₀ • L - ∑ k, a k • E k) + (s • L - ∑ k, E k) := by
    rw [← hdiv, add_smul, smul_sub, smul_smul, Finset.smul_sum, mul_comm m₀ q]
    simp only [smul_smul, add_smul, one_smul, Finset.sum_add_distrib]
    abel
  rw [hdivisor, hq₀ q (by omega) s hsm] at hle
  have h0 := Nat.eq_zero_of_le_zero hle
  have hterm := (Finset.sum_eq_zero_iff.mp h0) n (Finset.mem_range.mpr (by omega))
  rw [show n + j - n = j by omega] at hterm
  have := logFormsSheaf_cohomology_finite hnorm ξ hinj hξ E hEc hsnc (L - ∑ k, E k) n j
  have hsub := Module.finrank_zero_iff.mp hterm
  rw [logFormsSheaf_top_eq hnorm ξ hinj hξ E hEc hsnc, sub_add_cancel] at hsub
  let e' := ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X j).mapIso
    (canonicalTwistIso c₀ hcover L)).addCommGroupIsoToAddEquiv
  exact @Equiv.subsingleton _ _ e'.toEquiv hsub

end Vanishing

end MixedFujita
