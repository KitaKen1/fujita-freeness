/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationModelNumerical
public import MixedFujita.CartierBigOperations
public import MixedFujita.KawamataViehwegStatement
public import MixedFujita.PrincipalizedGlobalGeneration

/-!
The numerical statement (27) of section 6.3 of the manuscript on the isolation model, and the
generation of P with Kawamata–Viehweg vanishing as a hypothesis (step 12).

With the notation of the identity (30) (IsolationModelNumerical), suppose that e₁ ≥ 1, that ρ*L_X
is nef and big with finite-dimensional spaces of sections of its multiples, that G is effective
and that ρ*(u L_X) − G is globally generated. Then

  m' d (Q − K_T) − Σ a_k E_k = D₁ + m' ρ*N_X,   D₁ ~ e₁ ρ*L_X + w (ρ*(u L_X) − G),

with D₁ nef and big: nef as a sum of nef divisors, big because e₁ ρ*L_X is big and the second
summand has a nonzero section; the sections of its multiples embed into those of multiples of
ρ*L_X, by multiplication with the section of the effective divisor k w G. Hence a vanishing
H¹(T, O(Q)) = 0 for divisors of this form gives, by the lifting on the isolation model, that P is
generated at x. For N_X = 0 the vanishing is the Kawamata–Viehweg statement; for a nef N_X it is
its sum form.
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
/-- The numerical statement (27) and (30) with denominators cleared: on the isolation model there
are natural numbers a_k < m' d and a nef and big divisor D₁ such that
m' d (ρ*π*P − ⌊Γ⌋ − K_T) − Σ a_k E_k = D₁ + m' ρ*N_X. -/
theorem isolation_model_floor_divisor_nef_big
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
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (Mn : ℕ) (η : ℝ) (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') (he₁pos : 1 ≤ e₁)
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hLbig : CartierIsBig K (cartierPullback ρ LX))
    (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc)) :
    ∃ a : Fin r' → ℕ, (∀ k, a k < m' * d) ∧ ∃ D₁ : CartierDivisor T,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + m' • cartierPullback ρ NX ∧
      CartierIsNef K D₁ ∧ CartierIsBig K D₁ := by
  obtain ⟨a, halt, f, hEq⟩ := isolation_model_floor_divisor_linear_equivalence ρ hρ π P c₀ f₀ d
    hd B Dv cT ξT hinjT E hEc hTB hTD Gc hTG c₁ Mn η LX NX hLN j hDlin m' hm' p w u e₁ hp hw he₁
  refine ⟨a, halt, e₁ • cartierPullback ρ LX + w • (cartierPullback ρ (u • LX) - Gc) +
    principalCartierDivisor T f, ?_, ?_, ?_⟩
  · rw [hEq]
    abel
  · exact (cartierIsNef_add_principal_iff f).mpr (cartierIsNef_add (cartierIsNef_nsmul hLnef e₁)
      (cartierIsNef_nsmul (cartierIsGloballyGenerated_isNef hGG) w))
  · apply cartierIsBig_add_principal
    obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isGloballyGenerated _ hGG
    refine cartierIsBig_add_of_section (cartierIsBig_nsmul hLbig e₁ he₁pos hLfin)
      (cartierSectionPower _ t w) (cartierSectionPower_ne_zero _ t ht w) fun k => ?_
    obtain ⟨tG, htG⟩ := exists_section_ne_zero_of_isEffective ((k * w) • Gc)
      (cartier_nsmul_isEffective Gc hGc (k * w))
    refine finiteDimensional_of_eq_add_of_section (K := K) _ ((k * w) • Gc)
      ((k * (e₁ + w * u)) • cartierPullback ρ LX) ?_ tG htG (hLfin _)
    rw [cartierPullback_nsmul ρ LX u]
    module

variable [IsLocallyNoetherian V] [IsProper ρ]

/-- Sections 6.1 to 6.3 on a given isolation model, with the vanishing as a hypothesis in the form
produced by the numerical statement: if H¹(T, O(Q)) = 0 whenever
m' d (Q − K_T) − Σ a_k E_k = D₁ + m' ρ*N_X with a_k < m' d and D₁ nef and big, then the Cartier
divisor P of V has a global section generating it at x. -/
theorem isolation_model_exists_section_generating_of_vanishing
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1)
    (E : Fin r' → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (S : Set (Fin r')) (hS : S.Nonempty) (hSx : ∀ k ∈ S, π (ρ (ξT k)) = x)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') (he₁pos : 1 ≤ e₁)
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hLbig : CartierIsBig K (cartierPullback ρ LX))
    (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc))
    (hvan : ∀ a : Fin r' → ℕ, (∀ k, a k < m' * d) → ∀ D₁ : CartierDivisor T,
      (m' * d) • (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k -
          smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + m' • cartierPullback ρ NX →
      CartierIsNef K D₁ → CartierIsBig K D₁ →
      Subsingleton (Scheme.Modules.Cohomology
        (cartierPullback ρ (cartierPullback π P) -
          ∑ k, ⌊isolationGammaCoefficient d (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT
            etaleCharts_cover) (fun i => cartierPullback ρ (Dv i)) c₁ η Mn Gc (ξT k)⌋ • E k).sheaf 1)) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u' : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u' = f * g := by
  obtain ⟨a, halt, D₁, hdec, hnef, hbig⟩ := isolation_model_floor_divisor_nef_big ρ hρ π P c₀ f₀ d
    hd B Dv cT ξT hinjT E hEc hTB hTD Gc hGc hTG c₁ Mn η LX NX hLN j hDlin m' hm' p w u e₁ hp hw
    he₁ he₁pos hLnef hLbig hLfin hGG
  exact isolation_model_exists_section_generating ρ hρ hnormV π hπ P x hx c₀ f₀ d hd B hBexc Dv
    hDeff cT ξT hinjT hξT E hE hEc Gc hGc c₁ hc₁ Mn η hη0 hη1 S hS hSx hSeq hSmeet
    (hvan a halt D₁ hdec hnef hbig)

variable [IsProper (T ↘ Spec (CommRingCat.of K))]

/-- Sections 6.1 to 6.3 on a given isolation model, with Kawamata–Viehweg vanishing as a
hypothesis: on an isolation model ρ : T → X over the proper birational π : X → V (V normal), with
the set S of sections 6.1 and 6.2 over the closed point x, the linear equivalences D_i ~ j A_X for
A_X = d π*P − (d(K_X + div f₀) + B), natural numbers p_i = m' d (1 − η) c_i, w = m' d η / M and
e₁ ≥ 1 with e₁ + j Σ p_i + w u = m', ρ*A_X nef and big with finite-dimensional sections of its
multiples and ρ*(u A_X) − G globally generated, the Cartier divisor P of V has a global section
generating it at x. -/
theorem isolation_model_exists_section_generating_of_kawamataViehweg
    (hKV : KawamataViehwegVanishingSNC K n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1) (hsncT : IsSNCFamily K n ξT)
    (E : Fin r' → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (S : Set (Fin r')) (hS : S.Nonempty) (hSx : ∀ k ∈ S, π (ρ (ξT k)) = x)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (AX : CartierDivisor X)
    (hAX : AX = d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B))
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • AX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') (he₁pos : 1 ≤ e₁)
    (hAnef : CartierIsNef K (cartierPullback ρ AX)) (hAbig : CartierIsBig K (cartierPullback ρ AX))
    (hAfin : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ AX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • AX) - Gc)) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u' : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u' = f * g := by
  refine isolation_model_exists_section_generating_of_vanishing ρ hρ hnormV π hπ P x hx c₀ f₀ d hd
    B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc hTB hTD Gc hGc hTG c₁ hc₁ Mn η hη0 hη1 S hS hSx hSeq
    hSmeet AX 0 (by rw [add_zero]; exact hAX.symm) j hDlin m' hm' p w u e₁ hp hw he₁ he₁pos hAnef
    hAbig hAfin hGG fun a halt D₁ hdec hnef hbig => ?_
  rw [cartierPullback_zero, smul_zero, add_zero] at hdec
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc _ (m' * d) (Nat.mul_pos hm' hd) a halt
    (by rw [hdec]; exact hnef) (by rw [hdec]; exact hbig)

/-- Sections 6.1 to 6.3 on a given isolation model with a nef summand, with the sum form of
Kawamata–Viehweg vanishing as a hypothesis: as the preceding statement, with
d π*P − (d(K_X + div f₀) + B) = L_X + N_X, the D_i linearly equivalent to j L_X, the positivity
hypotheses on ρ*L_X, and ρ*N_X nef. -/
theorem isolation_model_exists_section_generating_of_kawamataViehwegSum
    (hKV : KawamataViehwegVanishingSNCSum K n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (π : X ⟶ V) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (P : CartierDivisor V) (x : V) (hx : IsClosed ({x} : Set V))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient B (z : X))
    {N : ℕ} (Dv : Fin N → CartierDivisor X) (hDeff : ∀ i, (Dv i).IsEffective)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1) (hsncT : IsSNCFamily K n ξT)
    (E : Fin r' → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
    (hEc : ∀ (k : Fin r') (z : CodimensionOnePoint T),
      cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT → cartierCoefficient Gc (t : T) = 0)
    (c₁ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (Mn : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (S : Set (Fin r')) (hS : S.Nonempty) (hSx : ∀ k ∈ S, π (ρ (ξT k)) = x)
    (hSeq : ∀ k ∈ S,
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d)
    (hSmeet : ∀ t : CodimensionOnePoint T,
      (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
      (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k'))
    (LX NX : CartierDivisor X)
    (hLN : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) = LX + NX)
    (j : ℕ) (hDlin : ∀ i, ∃ h : X.functionFieldˣ, Dv i = j • LX + principalCartierDivisor X h)
    (m' : ℕ) (hm' : 1 ≤ m') (p : Fin N → ℕ) (w u e₁ : ℕ)
    (hp : ∀ i, (p i : ℝ) = (m' : ℝ) * (d : ℝ) * ((1 - η) * c₁ i))
    (hw : (w : ℝ) = (m' : ℝ) * (d : ℝ) * (η / (Mn : ℝ)))
    (he₁ : e₁ + j * ∑ i, p i + w * u = m') (he₁pos : 1 ≤ e₁)
    (hLnef : CartierIsNef K (cartierPullback ρ LX)) (hLbig : CartierIsBig K (cartierPullback ρ LX))
    (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback ρ LX).sheaf, ⊤))
    (hGG : CartierIsGloballyGenerated (cartierPullback ρ (u • LX) - Gc))
    (hNnef : CartierIsNef K (cartierPullback ρ NX)) :
    ∃ (g : V.functionField) (f : V.functionFieldˣ) (u' : (V.presheaf.stalk x)ˣ),
      (rationalFunctionsEquiv (X := V) ⊤).symm g ∈ P.sections ⊤ ∧ P.IsLocalEquationAt x f ∧
      algebraMap (V.presheaf.stalk x) V.functionField u' = f * g := by
  refine isolation_model_exists_section_generating_of_vanishing ρ hρ hnormV π hπ P x hx c₀ f₀ d hd
    B hBexc Dv hDeff cT ξT hinjT hξT E hE hEc hTB hTD Gc hGc hTG c₁ hc₁ Mn η hη0 hη1 S hS hSx hSeq
    hSmeet LX NX hLN j hDlin m' hm' p w u e₁ hp hw he₁ he₁pos hLnef hLbig hLfin hGG
    fun a halt D₁ hdec hnef hbig => ?_
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc _ (m' * d) (Nat.mul_pos hm' hd) a halt D₁
    (m' • cartierPullback ρ NX) hdec hnef hbig (cartierIsNef_nsmul hNnef m')

end MixedFujita
