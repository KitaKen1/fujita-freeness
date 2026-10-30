/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FormalConjecturesUtil

/-!
# Fujita's freeness conjecture

For a smooth complex projective variety of dimension $n$ and an ample Cartier divisor $L$,
$K_X+mL$ is globally generated for $m\ge n+1$.
This is Fujita's freeness conjecture [Fu87]; the mixed variant is the problem in [CKMS24, §1.2].

*References:*
- [Fu87] T. Fujita, *On polarized manifolds whose adjoint bundles are not semipositive* (1987).
  https://doi.org/10.2969/aspm/01010167
- [CKMS24] J. Chen, A. Küronya, Y. Mustopa and J. Stix,
  *Convex Fujita numbers are not determined by the fundamental group*,
  arXiv:2301.06367v2 (2024), §1.2.
  https://arxiv.org/html/2301.06367v2#S1.SS2
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Fujita

/-- Cartier divisors represented by compatible local equations. -/
noncomputable def CartierDivisor (X : Scheme.{0}) [IsIntegral X] :
    AddSubgroup (X → Additive X.functionFieldˣ) :=
  let units (x : X) : Subgroup X.functionFieldˣ :=
    (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom).range
  { carrier D := ∀ x, ∃ U : X.Opens, x ∈ U ∧
      ∀ y ∈ U, (D y).toMul / (D x).toMul ∈ units y
    zero_mem' := by
      intro x
      exact ⟨⊤, Opens.mem_top x, fun y _ => by simp⟩
    add_mem' := by
      intro D E hD hE x
      obtain ⟨U, hxU, hU⟩ := hD x
      obtain ⟨V, hxV, hV⟩ := hE x
      refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun y hy => ?_⟩
      simpa only [Pi.add_apply, toMul_add, mul_div_mul_comm] using
        (units y).mul_mem (hU y hy.1) (hV y hy.2)
    neg_mem' := by
      intro D hD x
      obtain ⟨U, hxU, hU⟩ := hD x
      refine ⟨U, hxU, fun y hy => ?_⟩
      simpa only [Pi.neg_apply, toMul_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using
        (units y).inv_mem (hU y hy) }

def sectionSpace {X : Scheme.{0}} [IsIntegral X] (D : CartierDivisor X) :
    Set X.functionField :=
  {f | ∀ x, f * ((D.1 x).toMul : X.functionField) ∈
    (algebraMap (X.presheaf.stalk x) X.functionField).range}

def GloballyGenerated {X : Scheme.{0}} [IsIntegral X] (D : CartierDivisor X) : Prop :=
  ∀ x, ∃ f : sectionSpace D, ∃ u : (X.presheaf.stalk x)ˣ,
    algebraMap (X.presheaf.stalk x) X.functionField u = f.1 * (D.1 x).toMul

/-- Ampleness via affine nonvanishing loci of positive powers. -/
def Ample {X : Scheme.{0}} [IsIntegral X] (D : CartierDivisor X) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (m : ℕ) (_ : 1 ≤ m) (f : sectionSpace (m • D))
    (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X,
      y ∈ U ↔ ∃ u : (X.presheaf.stalk y)ˣ,
        algebraMap (X.presheaf.stalk y) X.functionField u = f.1 * ((m • D).1 y).toMul

/-- Nefness via ampleness of $A+mD$ for every ample $A$ and $m\ge0$. -/
def Nef {X : Scheme.{0}} [IsIntegral X] (D : CartierDivisor X) : Prop :=
  ∀ A : CartierDivisor X, Ample A → ∀ m : ℕ, Ample (A + m • D)

noncomputable instance functionFieldAlgebra {X : Scheme.{0}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] : Algebra ℂ X.functionField :=
  (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X ↘ Spec (.of ℂ)).appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _)).hom).toAlgebra

/-- The canonical divisor in the rational differential basis $b$. -/
def IsCanonical {X : Scheme.{0}} [IsIntegral X] [X.Over (Spec (CommRingCat.of ℂ))]
    {n : ℕ} (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (K : CartierDivisor X) : Prop :=
  ∀ x : X, Submodule.span (X.presheaf.stalk x)
    (Set.range fun a : Fin n → X.presheaf.stalk x =>
      b.det (fun i => KaehlerDifferential.D ℂ X.functionField
        (algebraMap (X.presheaf.stalk x) X.functionField (a i)))) =
    Submodule.span (X.presheaf.stalk x) {((K.1 x).toMul : X.functionField)⁻¹}

/-- Fujita's freeness conjecture [Fu87]: $K_X+mL$ is globally generated for $m\ge n+1$. -/
@[category research open, AMS 14]
theorem fujita (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (K : CartierDivisor X) (hK : IsCanonical b K)
    (L : CartierDivisor X) (hL : Ample L) (m : ℕ) (hm : n + 1 ≤ m) :
    GloballyGenerated (K + m • L) := by
  sorry

namespace variants

/-- The mixed variant [CKMS24, §1.2], allowing a nef summand. -/
@[category research open, AMS 14]
theorem mixed (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (b : Module.Basis (Fin n) X.functionField Ω[X.functionField⁄ℂ])
    (K : CartierDivisor X) (hK : IsCanonical b K)
    (s : ℕ) (hs : n + 1 ≤ s) (L : Fin s → CartierDivisor X)
    (hL : ∀ i, Ample (L i)) (N : CartierDivisor X) (hN : Nef N) :
    GloballyGenerated (K + ∑ i, L i + N) := by
  sorry

end variants

end Fujita
