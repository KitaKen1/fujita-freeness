/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessReduction

/-!
The statement for §9.2–9.4 of F2 from three separate inputs (steps 16 and 17).

`KltContractionBaseStatement` packages three steps of the manuscript. Here each is stated on its
own, in the form in which it is a known theorem, and the package is derived from them
(`kltContractionBase_of_inputs`):

* `NefContractionStatement` (§9.2: the base point free theorem for klt pairs, the Stein
  factorization of the morphism of a free multiple of D, and the descent of D): if κ(D) = 0 then
  D is principal; if κ(D) = k ≥ 1 there are a contraction f : X → Y (f_* O_X = O_Y, written as
  bijectivity of f on the sections over every open set) onto a normal projective variety of
  dimension k and an ample H on Y with D ∼ f*H.
* `KodairaPerturbationStatement` (§9.3: Kodaira's lemma for the nef and big a D − (K_X + Δ) and a
  small perturbation of the boundary by a general member): there is a klt pair (X, Δ') with
  effective boundary and K_X + Δ' ∼_ℚ (a − ε) D with ε > 0, that is r' (K_X + Δ') = u D + div ψ
  with u < r' a.
* `AmbroContractionStatement` (§9.4: Ambro's canonical bundle formula): for a contraction
  f : X → Y between normal projective varieties and a klt pair (X, Δ') with effective boundary
  and K_X + Δ' ∼_ℚ (u/r') f*H, there is a klt pair (Y, B_Y) with effective boundary and
  K_Y + B_Y ∼_ℚ (u/r') H, that is t r' (K_Y + B_Y) = t u H + div φ.

Hence F2 follows from K-NF and these three statements
(`linearEffectiveFreeness_of_kawamataNumericalFreeness_of_inputs`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- §9.2 of the manuscript (the base point free theorem for klt pairs, the Stein factorization of
the morphism of a free multiple of D, and the descent of D itself): under the hypotheses of F2,
if κ(D) = 0 then D is principal, and if κ(D) = k ≥ 1 there are a contraction f : X → Y
(f_* O_X = O_Y) onto a normal projective variety of dimension k (with the codimension-one points
in étale charts) and an ample Cartier divisor H on Y with D ∼ f*H. -/
def NefContractionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, CartierIsNef K D → ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∀ k : ℕ, CartierIitakaDimension K D k →
        (k = 0 → ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ) ∧
        (1 ≤ k → ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
          (_ : Y.Over (Spec (CommRingCat.of K)))
          (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))) (f : X ⟶ Y) (_ : IsDominant f)
          (_ : f.IsOver (Spec (CommRingCat.of K))) (H : CartierDivisor Y) (ψ : X.functionFieldˣ),
          topologicalKrullDim Y = k ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          CodimOneChartCovered k K Y ∧ (∀ V : Y.Opens, Function.Bijective (f.app V).hom) ∧
          CartierIsAmpleProj K H ∧ D = cartierPullback f H + principalCartierDivisor X ψ)

/-- §9.3 of the manuscript (Kodaira's lemma for a D − (K_X + Δ) and a small perturbation of the
boundary by a general member of a multiple of an ample class): on a normal projective klt pair
(X, Δ) with effective boundary, if a D − (K_X + Δ) is nef and big there is a klt pair (X, Δ') with
effective boundary and r' (K_X + Δ') = u D + div ψ for natural numbers u < r' a, that is
K_X + Δ' ∼_ℚ (a − ε) D with ε > 0. -/
def KodairaPerturbationStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∃ (f₁ : X.functionFieldˣ) (r' : ℕ) (_ : 1 ≤ r') (D'' : CartierDivisor X) (u : ℕ)
        (ψ : X.functionFieldˣ),
        LogPairBoundaryEffective c₀ f₁ r' D'' ∧ LogPairIsKlt c₀ f₁ r' D'' ∧
        D'' = u • D + principalCartierDivisor X ψ ∧ u < r' * a

/-- §9.4 of the manuscript (Ambro's canonical bundle formula): for a contraction f : X → Y
(f_* O_X = O_Y) between normal projective varieties and a klt pair (X, Δ') with effective boundary
and r' (K_X + Δ') = u f*H + div ψ, there is a klt pair (Y, B_Y) with effective boundary and
t r' (K_Y + B_Y) = t u H + div φ for some t ≥ 1, that is K_Y + B_Y ∼_ℚ (u/r') H. -/
def AmbroContractionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₁ : X.functionFieldˣ) (r' : ℕ), 1 ≤ r' →
    ∀ D'' : CartierDivisor X, LogPairBoundaryEffective c₀ f₁ r' D'' → LogPairIsKlt c₀ f₁ r' D'' →
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
      [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (k : ℕ),
      topologicalKrullDim Y = k → 1 ≤ k →
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered k K Y →
      (∃ H₁ : CartierDivisor Y, CartierIsAmpleProj K H₁) →
      ∀ (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))],
        (∀ V : Y.Opens, Function.Bijective (f.app V).hom) →
      ∀ (H : CartierDivisor Y) (u : ℕ) (ψ : X.functionFieldˣ),
        D'' = u • cartierPullback f H + principalCartierDivisor X ψ →
        ∃ (cY : EtaleChart K Y k) (fY : Y.functionFieldˣ) (t : ℕ) (_ : 1 ≤ t)
          (DY : CartierDivisor Y) (φ : Y.functionFieldˣ),
          LogPairBoundaryEffective cY fY (t * r') DY ∧ LogPairIsKlt cY fY (t * r') DY ∧
          DY = (t * u) • H + principalCartierDivisor Y φ

/-- The statement for §9.2–9.4 from the three separate inputs. -/
theorem kltContractionBase_of_inputs (hnef : NefContractionStatement.{u})
    (hkod : KodairaPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    KltContractionBaseStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnefT hbigT
    k hk
  obtain ⟨h0, hpos⟩ := hnef K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnefT
    hbigT k hk
  refine ⟨h0, fun hkpos => ?_⟩
  obtain ⟨Y, _, _, _, _, f, _, _, H, ψ, hdimY, hnormY, hcovY, hcontr, hH, hDf⟩ := hpos hkpos
  obtain ⟨f₁, r', hr', D'', u, ψ'', heff'', hklt'', hD'', hu⟩ :=
    hkod K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnefT hbigT
  have hD''f : D'' = u • cartierPullback f H + principalCartierDivisor X (ψ ^ u * ψ'') := by
    rw [hD'', hDf, smul_add, principalCartierDivisor_mul, principalCartierDivisor_power, add_assoc]
  obtain ⟨cY, fY, t, ht, DY, φ, heffY, hkltY, hDY⟩ :=
    hamb K X n hdim hn hnorm hcov hH₀ c₀ f₁ r' hr' D'' heff'' hklt'' Y k hdimY hkpos hnormY hcovY
      ⟨H, hH⟩ f hcontr H u (ψ ^ u * ψ'') hD''f
  have hlt : t * u < t * r' * a := by
    rw [mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left hu (by omega)
  exact ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, f, inferInstance,
    inferInstance, H, ψ, cY, fY, t * r', Nat.mul_le_mul ht hr', DY, t * u, φ, hdimY, hnormY,
    hcovY, hH, hDf, heffY, hkltY, hDY, hlt⟩

/-- F2 from K-NF and the three inputs of §9.2–9.4. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_inputs
    (hKNF : KawamataNumericalFreeness.{u}) (hnef : NefContractionStatement.{u})
    (hkod : KodairaPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness hKNF
    (kltContractionBase_of_inputs hnef hkod hamb)

/-- F2 from the Kawamata–Viehweg statement, the existence of the data of the minimizer for klt
pairs and the three inputs of §9.2–9.4. -/
theorem linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData_of_inputs
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hmin : KltMinimizerDataStatement.{u}) (hnef : NefContractionStatement.{u})
    (hkod : KodairaPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData hKV hmin
    (kltContractionBase_of_inputs hnef hkod hamb)

end MixedFujita
