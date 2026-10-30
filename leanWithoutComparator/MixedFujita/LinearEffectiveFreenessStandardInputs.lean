/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessInputs

/-!
The inputs of §9.2 and §9.3 of F2 split into textbook statements (steps 16 and 17).

* `NefContractionStatement` (§9.2) follows from
  - `KltBasePointFreeStatement`: the base point free theorem for klt pairs (Kawamata–Shokurov):
    if D is nef and a D − (K_X + Δ) is nef and big, then q D is globally generated for all large
    q; and
  - `SemiampleContractionStatement`: a Cartier divisor all of whose large multiples are globally
    generated is principal when κ(D) = 0, and when κ(D) = k ≥ 1 it is linearly equivalent to the
    pullback of an ample divisor by a contraction onto a normal projective variety of dimension k
    (the Stein factorization of the morphism of a free multiple, and the descent of D by two
    consecutive multiples).
* `KodairaPerturbationStatement` (§9.3) follows from
  - `KodairaLemmaStatement`: for a big Cartier divisor T and an ample H on a normal projective
    variety, m T − H has a nonzero section for some m ≥ 1 (Kodaira's lemma); and
  - `KltPerturbationStatement`: given such a decomposition of m (a D − (K_X + Δ)), there is a klt
    pair (X, Δ') with K_X + Δ' ∼_ℚ (a − ε) D, ε > 0 (a small multiple of the effective part and
    a general member of a multiple of an ample class added to the boundary).

Hence F2 follows from K-NF, these four statements and `AmbroContractionStatement`.
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

/-- The base point free theorem for klt pairs (Kawamata–Shokurov): on a normal projective klt
pair (X, Δ) with effective boundary, if D is a nef Cartier divisor and a D − (K_X + Δ) is nef and
big for an integer a ≥ 1, then q D is globally generated for every sufficiently large q. -/
def KltBasePointFreeStatement : Prop :=
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
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)

/-- The contraction of a semiample divisor: on a normal projective variety, if every sufficiently
large multiple of a Cartier divisor D is globally generated, then D is principal when κ(D) = 0,
and when κ(D) = k ≥ 1 there are a contraction f : X → Y (f_* O_X = O_Y) onto a normal projective
variety of dimension k (with the codimension-one points in étale charts) and an ample Cartier
divisor H on Y with D ∼ f*H. -/
def SemiampleContractionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ D : CartierDivisor X, (∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) →
      ∀ k : ℕ, CartierIitakaDimension K D k →
        (k = 0 → ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ) ∧
        (1 ≤ k → ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
          (_ : Y.Over (Spec (CommRingCat.of K)))
          (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))) (f : X ⟶ Y) (_ : IsDominant f)
          (_ : f.IsOver (Spec (CommRingCat.of K))) (H : CartierDivisor Y) (ψ : X.functionFieldˣ),
          topologicalKrullDim Y = k ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          CodimOneChartCovered k K Y ∧ (∀ V : Y.Opens, Function.Bijective (f.app V).hom) ∧
          CartierIsAmpleProj K H ∧ D = cartierPullback f H + principalCartierDivisor X ψ)

/-- Kodaira's lemma: on a normal projective variety, for a big Cartier divisor T and an ample
Cartier divisor H, some m T − H with m ≥ 1 has a nonzero global section. -/
def KodairaLemmaStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ T H : CartierDivisor X, CartierIsBig K T → CartierIsAmpleProj K H →
      ∃ (m : ℕ) (_ : 1 ≤ m) (s : Γ((m • T - H).sheaf, ⊤)), s ≠ 0

/-- The perturbation of §9.3: on a normal projective klt pair (X, Δ) with effective boundary,
if a D − (K_X + Δ) is nef and big and m (a D − (K_X + Δ)) − H has a nonzero section for an ample
H and m ≥ 1, then there is a klt pair (X, Δ') with effective boundary and
r' (K_X + Δ') = u D + div ψ for natural numbers u < r' a. -/
def KltPerturbationStatement : Prop :=
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
      ∀ (m : ℕ), 1 ≤ m → ∀ H : CartierDivisor X, CartierIsAmpleProj K H →
      ∀ s : Γ((m • ((r * a) • D - D') - H).sheaf, ⊤), s ≠ 0 →
        ∃ (f₁ : X.functionFieldˣ) (r' : ℕ) (_ : 1 ≤ r') (D'' : CartierDivisor X) (u : ℕ)
          (ψ : X.functionFieldˣ),
          LogPairBoundaryEffective c₀ f₁ r' D'' ∧ LogPairIsKlt c₀ f₁ r' D'' ∧
          D'' = u • D + principalCartierDivisor X ψ ∧ u < r' * a

/-- §9.2 from the base point free theorem and the contraction of a semiample divisor. -/
theorem nefContraction_of_basePointFree_of_semiampleContraction
    (hbpf : KltBasePointFreeStatement.{u}) (hsa : SemiampleContractionStatement.{u}) :
    NefContractionStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig k
    hk
  exact hsa K X n hdim hn hnorm hcov hH₀ D
    (hbpf K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig) k hk

/-- §9.3 from Kodaira's lemma and the perturbation. -/
theorem kodairaPerturbation_of_kodairaLemma_of_kltPerturbation
    (hkl : KodairaLemmaStatement.{u}) (hpert : KltPerturbationStatement.{u}) :
    KodairaPerturbationStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig
  obtain ⟨H, hH⟩ := hH₀
  obtain ⟨m, hm, s, hs⟩ := hkl K X n hdim hn hnorm ⟨H, hH⟩ ((r * a) • D - D') H hbig hH
  exact hpert K X n hdim hn hnorm hcov ⟨H, hH⟩ c₀ f₀ r hr D' heff hklt D a ha hnef hbig m hm H hH
    s hs

/-- F2 from K-NF, the base point free theorem, the contraction of a semiample divisor, Kodaira's
lemma, the perturbation of §9.3 and Ambro's canonical bundle formula. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_standardInputs
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionStatement.{u}) (hkl : KodairaLemmaStatement.{u})
    (hpert : KltPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_inputs hKNF
    (nefContraction_of_basePointFree_of_semiampleContraction hbpf hsa)
    (kodairaPerturbation_of_kodairaLemma_of_kltPerturbation hkl hpert) hamb

/-- F2 from the Kawamata–Viehweg statement, the existence of the data of the minimizer for klt
pairs, and the five inputs of §9.2–9.4. -/
theorem linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData_of_standardInputs
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hmin : KltMinimizerDataStatement.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionStatement.{u}) (hkl : KodairaLemmaStatement.{u})
    (hpert : KltPerturbationStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_standardInputs
    (kawamataNumericalFreeness_of_kawamataViehweg_of_minimizerData hKV hmin) hbpf hsa hkl hpert
    hamb

end MixedFujita
