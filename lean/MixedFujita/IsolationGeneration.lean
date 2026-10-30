/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationModelNefBig
public import MixedFujita.CartierPositivityPullback
public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.EtaleChartDimension
public import MixedFujita.SNCComponentCartier

/-!
Section 6 of the manuscript as one statement: from the data of the minimizer and
Kawamata–Viehweg vanishing as a hypothesis, the Cartier divisor P is generated at x (step 12).

Let π : X → V be a proper birational morphism from a smooth proper variety X with a simple normal
crossing family to a normal scheme V, B the boundary on X, P a Cartier divisor of V and
A_X = d π*P − (d(K_X + div f₀) + B). Suppose that A_X is big with finite-dimensional sections of
its multiples, that the multiples of m₀ A_X are globally generated, and that the divisors D_i are
effective, supported on the family and linearly equivalent to j A_X with m₀ dividing j. Given the
data of the minimizer over the closed point x of V (a positive vector c and a profile q with
c · q = 1 in the polytope of a point over x, the inequality (24) and the point-centre property
over x, and the budget d j Σ c_i < 1), the Kawamata–Viehweg statement implies that P has a global
section generating it at x.

The statement is proved once, for a decomposition d π*P − (d(K_X + div f₀) + B) = L_X + N_X with
the D_i linearly equivalent to j L_X, from a vanishing hypothesis for divisors of the form
"nef and big plus a multiple of the pullback of N_X". For N_X = 0 this hypothesis is the
Kawamata–Viehweg statement; for N_X with nef pullbacks it is its sum form (the case needed for
S-NF, where P = K_X + A + N).

The integers of section 6.3 are chosen explicitly: with c⁰_i = α_i/β, u = m₀ Σ (M/q⁰_i)(j/m₀),
H = β d u + 1 and η = 1/(H + 1), one takes m' = (H + 1) β M, p_i = M d H α_i, w = β d and
e₁ = m' − j Σ p_i − w u ≥ 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

/-- The integers of section 6.3: for positive rational c_i with d j Σ c_i < 1 and natural numbers
M ≥ 1, u, there are 0 < η < 1 and natural numbers m' ≥ 1, p_i, w, e₁ ≥ 1 with
p_i = m' d (1 − η) c_i, w = m' d η / M and e₁ + j Σ p_i + w u = m'. -/
theorem exists_isolation_integers {N : ℕ} (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 < c₁ i)
    (hrat : ∀ i, ∃ x : ℚ, c₁ i = (x : ℝ)) (Mn : ℕ) (hMn : 1 ≤ Mn) (d : ℕ) (hd : 1 ≤ d) (j u : ℕ)
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c₁ i < 1) :
    ∃ (η : ℝ) (m' : ℕ) (p : Fin N → ℕ) (w e₁ : ℕ), 0 < η ∧ η < 1 ∧ 1 ≤ m' ∧ 1 ≤ e₁ ∧
      (∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i)) ∧
      (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)) ∧ e₁ + j * ∑ i, p i + w * u = m' := by
  choose x hx using hrat
  have hx0 : ∀ i, 0 ≤ x i := fun i => by
    have h := (hc₁ i).le
    rw [hx i] at h
    exact_mod_cast h
  obtain ⟨β, α, hβ, hα⟩ := exists_common_denominator_nat x hx0
  have hαR : ∀ i, (α i : ℝ) = (β : ℝ) * c₁ i := fun i => by
    rw [hx i]
    exact_mod_cast hα i
  have hβpos : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  -- the budget in natural numbers
  have hbud : d * j * ∑ i, α i < β := by
    have hsum : ∑ i, (α i : ℝ) = (β : ℝ) * ∑ i, c₁ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hαR i
    have h1 : ((d * j : ℕ) : ℝ) * ∑ i, (α i : ℝ) < (β : ℝ) := by
      rw [hsum]
      calc ((d * j : ℕ) : ℝ) * ((β : ℝ) * ∑ i, c₁ i)
          = (β : ℝ) * (((d * j : ℕ) : ℝ) * ∑ i, c₁ i) := by ring
        _ < (β : ℝ) * 1 := mul_lt_mul_of_pos_left hbudget hβpos
        _ = (β : ℝ) := mul_one _
    exact_mod_cast h1
  obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
  have ht : d * j * ∑ i, α i ≤ b' := by omega
  -- the choices
  let H : ℕ := (b' + 1) * d * u + 1
  let m' : ℕ := (H + 1) * (b' + 1) * Mn
  let p : Fin N → ℕ := fun i => Mn * d * H * α i
  let w : ℕ := (b' + 1) * d
  have hsum : j * ∑ i, p i = Mn * H * (d * j * ∑ i, α i) := by
    change j * ∑ i, Mn * d * H * α i = Mn * H * (d * j * ∑ i, α i)
    rw [← Finset.mul_sum]
    ring
  have hkey : j * ∑ i, p i + w * u + 1 ≤ m' := by
    rw [hsum]
    have h1 : Mn * H * (d * j * ∑ i, α i) ≤ Mn * H * b' := Nat.mul_le_mul_left _ ht
    have h2 : H ≤ Mn * H := Nat.le_mul_of_pos_left H hMn
    have h3 : m' = Mn * H * b' + Mn * H + (Mn * b' + Mn) := by
      change (H + 1) * (b' + 1) * Mn = Mn * H * b' + Mn * H + (Mn * b' + Mn)
      ring
    have h4 : w * u + 1 = H := by
      change (b' + 1) * d * u + 1 = (b' + 1) * d * u + 1
      rfl
    rw [h3]
    omega
  have hHpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hMnpos : (0 : ℝ) < (Mn : ℝ) := by exact_mod_cast hMn
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by
    have : 1 ≤ H := Nat.le_add_left 1 _
    exact_mod_cast this
  refine ⟨1 / ((H : ℝ) + 1), m', p, w, m' - (j * ∑ i, p i + w * u), by positivity, ?_, by omega,
    by omega, fun i => ?_, ?_, by omega⟩
  · rw [div_lt_one hHpos]
    linarith
  · change ((Mn * d * H * α i : ℕ) : ℝ) = (((H + 1) * (b' + 1) * Mn : ℕ) : ℝ) * (d : ℝ) *
      ((1 - 1 / ((H : ℝ) + 1)) * c₁ i)
    have h1 : (1 : ℝ) - 1 / ((H : ℝ) + 1) = (H : ℝ) / ((H : ℝ) + 1) := by
      field_simp
      ring
    have h2 := hαR i
    push_cast at h2 ⊢
    rw [h1, h2]
    field_simp
  · change (((b' + 1) * d : ℕ) : ℝ) = (((H + 1) * (b' + 1) * Mn : ℕ) : ℝ) * (d : ℝ) *
      (1 / ((H : ℝ) + 1) / (Mn : ℝ))
    push_cast
    field_simp

section Generation

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X V : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral V] [IsLocallyNoetherian V]

/-- Section 6 as one statement, with the vanishing as a hypothesis: on a smooth proper simple
normal crossing model π : X → V of a normal scheme V, with
d π*P − (d(K_X + div f₀) + B) = L_X + N_X, L_X big with finite-dimensional sections of its
multiples, the multiples of m₀ L_X globally generated and the D_i linearly equivalent to j L_X
with m₀ dividing j, the data of the minimizer over the closed point x (c, q, the polytope
membership, the inequality (24), the point-centre property and the budget d j Σ c_i < 1) give a
global section of P generating it at x, provided H¹(T, O(Q)) = 0 on smooth proper models
ρ : T → X whenever m (Q − K_T) − Σ a_k E_k = D₁ + m' ρ*N_X with a_k < m and D₁ nef and big. -/
theorem exists_section_generating_of_minimizer_data_of_vanishing
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hjm₀ : m₀ ∣ j)
    (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • LX))
    (hLbig : CartierIsBig K LX) (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • LX).sheaf, ⊤))
    (y : X) (hy : π y = x) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set V), InSNCProfilePolytope ξ d B Dv q p →
      ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set V)).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ π ⁻¹' ({x} : Set V))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1)
    (hvan : ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
      [T.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
      [IsProper (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
      [ρ.IsOver (Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r' : ℕ) (ξT : Fin r' → T),
      Function.Injective ξT → (∀ k, Order.coheight (ξT k) = 1) → IsSNCFamily K n ξT →
      ∀ E : Fin r' → CartierDivisor T,
        (∀ (k : Fin r') (z : CodimensionOnePoint T),
          cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0) →
      ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r' → ℕ, (∀ k, a k < m) →
      ∀ (D₁ : CartierDivisor T) (m' : ℕ),
        m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + m' • cartierPullback ρ NX →
        CartierIsNef K D₁ → CartierIsBig K D₁ →
        Subsingleton (Scheme.Modules.Cohomology Q.sheaf 1)) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u = f * g := by
  have hΦ : IsClosed (π ⁻¹' ({x} : Set V)) := hx.preimage π.continuous
  obtain ⟨c₁, q₀, Mn, nn, hc₁, hc₁rat, hq₀, hq₀rat, hc₁q₀, hbud₁, hMn, hI, hnn, hAeff, T, hTi, hTo,
    hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r', ξT, Gc, hGc, hinjT, hξT, hsncT, hTB, hTD, hTG,
    hGcI, hgg, hS⟩ := exists_isolation_model ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hDeff hD
      (π ⁻¹' ({x} : Set V)) hΦ y hy hc hcq hqy hpolyΦ hcentre (Nat.cast_nonneg (d * j)) hbudget
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hpropT : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  -- the member divisors of the family of T
  obtain ⟨E, hE, -, hEc⟩ := exists_snc_component_cartier ξT hξT hsncT
  -- the multiple u of A_X
  obtain ⟨j', rfl⟩ := hjm₀
  let U : ℕ := ∑ i, nn i * j'
  have hGG : CartierIsGloballyGenerated (cartierPullback ρ ((m₀ * U) • LX) - Gc) := by
    refine (hgg ((m₀ * U) • LX) fun k => ?_).1
    obtain ⟨h, hh⟩ := hDlin k.1
    have hle : nn k.1 * j' ≤ U :=
      Finset.single_le_sum (f := fun i => nn i * j') (fun i _ => Nat.zero_le _)
        (Finset.mem_univ k.1)
    obtain ⟨V', hV'⟩ : ∃ V', V' + nn k.1 * j' = U := ⟨U - nn k.1 * j', Nat.sub_add_cancel hle⟩
    have heq : (m₀ * U) • LX - nn k.1 • Dv k.1 =
        (V' * m₀) • LX + principalCartierDivisor X (h⁻¹ ^ nn k.1) := by
      rw [hh, principalCartierDivisor_power, principalCartierDivisor_inv, ← hV']
      module
    rw [heq]
    exact cartierIsGloballyGenerated_principal_shift _ _ (hLgg V')
  -- the integers of section 6.3
  obtain ⟨η, m', p, w, e₁, hη0, hη1, hm', he₁pos, hp, hw, he₁⟩ :=
    exists_isolation_integers c₁ hc₁ hc₁rat Mn hMn d hd (m₀ * j') (m₀ * U) hbud₁
  obtain ⟨S, hSne, hSprop, hSmeet⟩ := hS η hη0 hη1
  -- positivity of ρ*L_X
  have hLnef : CartierIsNef K (cartierPullback ρ LX) :=
    cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul ρ LX m₀ hm₀
      (by simpa using hLgg 1)
  have hdim : topologicalKrullDim T = topologicalKrullDim X :=
    (etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim c₀).symm
  have hLbigT : CartierIsBig K (cartierPullback ρ LX) :=
    cartierIsBig_cartierPullback hnormX hnormT ρ hρ hdim hLbig
  have hLfinT : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤) :=
    fun k => by
      rw [← cartierPullback_nsmul]
      exact finiteDimensional_sections_cartierPullback hnormX ρ hρ (k • LX) (hLfin k)
  exact isolation_model_exists_section_generating_of_vanishing ρ hρ hnormV π hπ P x hx
    c₀ f₀ d hd B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc hTB hTD Gc hGc hTG c₁
    (fun i => (hc₁ i).le) Mn η hη0.le hη1.le S hSne (fun k hk => (hSprop k hk).1)
    (fun k hk => (hSprop k hk).2) hSmeet LX NX hLN (m₀ * j') hDlin m' hm' p w (m₀ * U) e₁ hp hw he₁
    he₁pos hLnef hLbigT hLfinT hGG
    (fun a halt D₁ hdec hnef hbig => hvan T ρ cT r' ξT hinjT hξT hsncT E hEc _ (m' * d)
      (Nat.mul_pos hm' hd) a halt D₁ m' hdec hnef hbig)

/-- Section 6 as one statement, with Kawamata–Viehweg vanishing as a hypothesis: on a smooth
proper simple normal crossing model π : X → V of a normal scheme V, the data of the minimizer over
the closed point x (c, q, the polytope membership, the inequality (24), the point-centre property
and the budget d j Σ c_i < 1), together with A_X = d π*P − (d(K_X + div f₀) + B) big with
finite-dimensional sections of its multiples, the multiples of m₀ A_X globally generated and the
D_i linearly equivalent to j A_X with m₀ dividing j, give a global section of P generating it
at x. -/
theorem exists_section_generating_of_minimizer_data
    (hKV : KawamataViehwegVanishingSNC K n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (AX : CartierDivisor X)
    (hAX : AX = d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B))
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • AX + principalCartierDivisor X h)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hjm₀ : m₀ ∣ j)
    (hAgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • AX))
    (hAbig : CartierIsBig K AX) (hAfin : ∀ k : ℕ, FiniteDimensional K Γ((k • AX).sheaf, ⊤))
    (y : X) (hy : π y = x) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set V), InSNCProfilePolytope ξ d B Dv q p →
      ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set V)).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ π ⁻¹' ({x} : Set V))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u = f * g := by
  refine exists_section_generating_of_minimizer_data_of_vanishing hnormV π hπ P x hx ξ hinj hξ
    hsnc c₀ f₀ d hd B hB hb hBexc Dv hDeff hD AX 0 (by rw [add_zero]; exact hAX.symm) j hDlin m₀
    hm₀ hjm₀ hAgg hAbig hAfin y hy hc hcq hqy hpolyΦ hcentre hbudget ?_
  intro T _ _ _ _ _ ρ _ _ cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁ m' hdec hnef hbig
  rw [cartierPullback_zero, smul_zero, add_zero] at hdec
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha (by rw [hdec]; exact hnef)
    (by rw [hdec]; exact hbig)

/-- Section 6 as one statement with a nef summand, with the sum form of Kawamata–Viehweg vanishing
as a hypothesis: as the preceding statement, with
d π*P − (d(K_X + div f₀) + B) = L_X + N_X, the hypotheses on L_X in place of A_X, and N_X having
nef pullback to every model over X. -/
theorem exists_section_generating_of_minimizer_data_nef
    (hKV : KawamataViehwegVanishingSNCSum K n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hjm₀ : m₀ ∣ j)
    (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • LX))
    (hLbig : CartierIsBig K LX) (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • LX).sheaf, ⊤))
    (hNnef : ∀ (T : Scheme.{u}) [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] (ρ : T ⟶ X)
      [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))],
      CartierIsNef K (cartierPullback ρ NX))
    (y : X) (hy : π y = x) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set V), InSNCProfilePolytope ξ d B Dv q p →
      ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set V)).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ π ⁻¹' ({x} : Set V))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u = f * g := by
  refine exists_section_generating_of_minimizer_data_of_vanishing hnormV π hπ P x hx ξ hinj hξ
    hsnc c₀ f₀ d hd B hB hb hBexc Dv hDeff hD LX NX hLN j hDlin m₀ hm₀ hjm₀ hLgg hLbig hLfin y hy
    hc hcq hqy hpolyΦ hcentre hbudget ?_
  intro T _ _ _ _ _ ρ _ _ cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁ m' hdec hnef hbig
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁ (m' • cartierPullback ρ NX) hdec hnef
    hbig (cartierIsNef_nsmul (hNnef T ρ) m')

end Generation

end MixedFujita
