/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationModelLifting
public import MixedFujita.NormalCartierCoefficientExt
public import MixedFujita.CartierFiniteProducts
public import Mathlib.Tactic.Module

/-!
The numerical identity (30) of section 6.3 of the manuscript on the isolation model (step 12).

On the isolation model ρ : T → X put Q = ρ*π*P − ⌊Γ⌋ with Γ = B_T + Ψ. The manuscript uses

  Q − (K_T + {Γ}) = ρ*A − Ψ ≡ (b − (1 − η) m Σ c_i − η u/M) ρ*L + (η/M)(u ρ*L − G),

where A = P − (K + B) ≡ b L + N and the D_i are linearly equivalent to multiples of L. Here it is
proved with denominators cleared. Let d π*P − (d(K_X + div f₀) + B) = L_X + N_X as Cartier
divisors of X, let D_i be linearly equivalent to j L_X, and let m' ≥ 1, p_i, w, u, e₁ be natural
numbers with

  p_i = m' d (1 − η) c_i,   w = m' d η / M,   e₁ + j Σ p_i + w u = m'.

Then m' d Γ has integral coefficients, there are natural numbers a_k < m' d (the coefficients of
m' d {Γ}) and

  m' d (Q − K_T) − Σ a_k E_k = e₁ ρ*L_X + w (ρ*(u L_X) − G) + m' ρ*N_X + (a principal divisor).

For K-NF one takes N_X = 0; for S-NF, where P = K_X + A + N, one takes L_X and N_X the pullbacks
of A and N.

The proof compares coefficients on the normal scheme T: the crepant boundary, the ρ*D_i and G are
supported on the family, hence are integral combinations of the member divisors E_k.
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

/-- The identity of section 6.3 in an abelian group: from the decomposition of ⌊Γ⌋ and {Γ}, the
crepant formula, the decomposition of A into L and N and the linear equivalences of the D_i. -/
theorem floorDivisor_group_identity {G : Type*} [AddCommGroup G]
    (PT F KT A' LT NT Gc U₀ HP BT SD RD : G) (d e₁ j sp w u : ℕ)
    (h1 : ((e₁ + j * sp + w * u) * d) • F + A' = (e₁ + j * sp + w * u) • BT + SD + w • Gc)
    (h2 : d • (KT + U₀) + BT = RD) (h3 : LT + NT = d • PT - RD) (h4 : SD = (j * sp) • LT + HP) :
    ((e₁ + j * sp + w * u) * d) • (PT - F - KT) - A' =
      e₁ • LT + w • (u • LT - Gc) + (e₁ + j * sp + w * u) • NT +
        (((e₁ + j * sp + w * u) * d) • U₀ - HP) := by
  have hBT : BT = RD - d • (KT + U₀) := eq_sub_of_add_eq' h2
  have hA' : A' = (e₁ + j * sp + w * u) • BT + SD + w • Gc -
      ((e₁ + j * sp + w * u) * d) • F := eq_sub_of_add_eq' h1
  have hRD : RD = d • PT - (LT + NT) := by
    rw [h3]
    abel
  rw [hA', hBT, h4, hRD]
  module

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T V : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral V] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

omit [IsLocallyNoetherian X] in
/-- The numerical identity (30) with denominators cleared. On the isolation model, with
d π*P − (d(K_X + div f₀) + B) = L_X + N_X, the D_i linearly equivalent to j L_X, and natural
numbers p_i = m' d (1 − η) c_i, w = m' d η / M, e₁ + j Σ p_i + w u = m', there are natural numbers
a_k < m' d with m' d (ρ*π*P − ⌊Γ⌋ − K_T) − Σ a_k E_k equal to
e₁ ρ*L_X + w (ρ*(u L_X) − G) + m' ρ*N_X up to a principal divisor. -/
theorem isolation_model_floor_divisor_linear_equivalence
    (π : X ⟶ V) [IsDominant π] (P : CartierDivisor V)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T)
    (hinjT : Function.Injective ξT) (E : Fin r' → CartierDivisor T)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (Mn : ℕ) (η : ℝ) (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') :
    ∃ a : Fin r' → ℕ, (∀ k, a k < m' * d) ∧ ∃ f : T.functionFieldˣ,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k =
        e₁ • cartierPullback ρ LX + w • (cartierPullback ρ (u • LX) - Gc) +
          m' • cartierPullback ρ NX + principalCartierDivisor T f := by
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t =>
    smooth_stalk_isIntegrallyClosed (K := K) t
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm'pos : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast hm'
  have hmpos : (0 : ℝ) < (m' : ℝ) * (d : ℝ) := mul_pos hm'pos hdpos
  generalize hBT : crepantBoundaryCartier ρ hρ c₀ f₀ d
    (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT etaleCharts_cover =
    BT at hTB ⊢
  -- the integral coefficients of m' d Γ
  let I : Fin r' → ℤ := fun k => (m' : ℤ) * cartierCoefficient BT (ξT k) +
    ∑ i, (p i : ℤ) * cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) +
    (w : ℤ) * cartierCoefficient Gc (ξT k)
  have hI : ∀ k, (m' : ℝ) * (d : ℝ) * isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k) = (I k : ℝ) := by
    intro k
    have h1 : ∑ i, (p i : ℝ) * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) =
        (m' : ℝ) * (d : ℝ) * ((1 - η) *
          ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp i]
      ring
    change (m' : ℝ) * (d : ℝ) * ((cartierCoefficient BT (ξT k) : ℝ) / d +
        ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ))) =
      (((m' : ℤ) * cartierCoefficient BT (ξT k) +
        ∑ i, (p i : ℤ) * cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) +
        (w : ℤ) * cartierCoefficient Gc (ξT k) : ℤ) : ℝ)
    push_cast
    rw [h1, hw]
    field_simp
    ring
  have hfl1 : ∀ k, ((m' * d : ℕ) : ℤ) * ⌊isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ ≤ I k := by
    intro k
    have h := mul_le_mul_of_nonneg_left (Int.floor_le (isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k))) hmpos.le
    rw [hI k] at h
    exact_mod_cast h
  have hfl2 : ∀ k, I k < ((m' * d : ℕ) : ℤ) * ⌊isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ + ((m' * d : ℕ) : ℤ) := by
    intro k
    have h := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k))) hmpos
    rw [hI k, mul_add, mul_one] at h
    exact_mod_cast h
  let a : Fin r' → ℕ := fun k => (I k - ((m' * d : ℕ) : ℤ) * ⌊isolationGammaCoefficient d BT
    (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋).toNat
  have ha : ∀ k, ((a k : ℕ) : ℤ) = I k - ((m' * d : ℕ) : ℤ) * ⌊isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ := fun k =>
    Int.toNat_of_nonneg (sub_nonneg.mpr (hfl1 k))
  have halt : ∀ k, a k < m' * d := by
    intro k
    have h1 := ha k
    have h2 := hfl2 k
    omega
  -- the supported divisors are combinations of the member divisors
  have hstar : ∑ k, I k • E k =
      m' • BT + ∑ i, p i • cartierPullback ρ (Dv i) + w • Gc := by
    apply cartierDivisor_eq_of_forall_coefficient_eq hnormT
    intro z
    have hrhs : cartierCoefficient (m' • BT + ∑ i, p i • cartierPullback ρ (Dv i) + w • Gc)
        (z : T) = (m' : ℤ) * cartierCoefficient BT (z : T) +
          ∑ i, (p i : ℤ) * cartierCoefficient (cartierPullback ρ (Dv i)) (z : T) +
          (w : ℤ) * cartierCoefficient Gc (z : T) := by
      rw [cartierCoefficient_add, cartierCoefficient_add, cartierCoefficient_nsmul,
        cartierCoefficient_sum, cartierCoefficient_nsmul]
      congr 2
      exact Finset.sum_congr rfl fun i _ => cartierCoefficient_nsmul _ _ _
    rw [hrhs]
    rcases cartierCoefficient_member_combination ξT hinjT E hEc I z with ⟨k, hzk, hco⟩ | ⟨hz, hco⟩
    · rw [hco, hzk]
    · rw [hco, hTB z hz, hTG z hz, mul_zero, mul_zero, add_zero, zero_add]
      exact (Finset.sum_eq_zero fun i _ => by rw [hTD i z hz, mul_zero]).symm
  have h1 : (m' * d) • (∑ k, ⌊isolationGammaCoefficient d BT
      (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k) + ∑ k, a k • E k =
      m' • BT + ∑ i, p i • cartierPullback ρ (Dv i) + w • Gc := by
    rw [← hstar, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hIk : I k = ((m' * d : ℕ) : ℤ) * ⌊isolationGammaCoefficient d BT
        (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ + ((a k : ℕ) : ℤ) := by
      rw [ha k]
      ring
    rw [hIk, add_smul, natCast_zsmul, mul_smul ((m' * d : ℕ) : ℤ), natCast_zsmul]
  -- the crepant formula, the divisor A and the linear equivalences
  have h2 : d • (smoothCanonicalDivisor cT +
      principalCartierDivisor T (crepantPullbackFormUnit ρ hρ c₀ f₀ cT)) + BT =
      cartierPullback ρ (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) := by
    rw [← hBT]
    exact crepantBoundaryCartier_smooth_recombine ρ hρ c₀ f₀ d _ cT
  have h3 : cartierPullback ρ LX + cartierPullback ρ NX =
      d • cartierPullback ρ (cartierPullback π P) -
      cartierPullback ρ (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) := by
    rw [← cartierPullback_add, ← hLN, cartierPullback_sub, cartierPullback_nsmul]
  choose h hh using hDlin
  let h' : Fin N → T.functionFieldˣ := fun i =>
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (h i)
  have hDT : ∀ i, cartierPullback ρ (Dv i) =
      j • cartierPullback ρ LX + principalCartierDivisor T (h' i) := fun i => by
    rw [hh i, cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal]
  have h4 : ∑ i, p i • cartierPullback ρ (Dv i) = (j * ∑ i, p i) • cartierPullback ρ LX +
      ∑ i, p i • principalCartierDivisor T (h' i) := by
    rw [mul_comm, Finset.sum_mul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDT i, smul_add, mul_smul]
  subst he₁
  refine ⟨a, halt, crepantPullbackFormUnit ρ hρ c₀ f₀ cT ^ ((e₁ + j * ∑ i, p i + w * u) * d) *
    (∏ i, h' i ^ p i)⁻¹, ?_⟩
  rw [principalCartierDivisor_mul, principalCartierDivisor_power, principalCartierDivisor_inv,
    principalCartierDivisor_weighted_prod, cartierPullback_nsmul ρ LX u, ← sub_eq_add_neg]
  exact floorDivisor_group_identity _ _ _ _ _ _ _ _ _ _ _ _ d e₁ j (∑ i, p i) w u h1 h2 h3 h4

end Model

end MixedFujita
