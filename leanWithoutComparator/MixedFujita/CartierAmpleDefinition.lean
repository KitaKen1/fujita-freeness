/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierAmpleTransfer

/-!
Statement-level definitions for the manuscript. A Cartier divisor on an integral scheme over a
field is ample (in the projective sense) if a positive multiple is linearly equivalent to the
hyperplane divisor of an actual closed immersion into polynomial projective space over the base
field, cut by a degree-one form avoiding the generic point; this is the usual characterization
of ample line bundles on projective schemes. A Cartier divisor is globally generated if at every
point some actual global section has a unit local coefficient. On a smooth integral scheme over
an algebraically closed field, the multiplicity half of Lemma 1 holds for every ample divisor:
one constant bounds the order of every nonzero section of j A, j ≥ 1, by c j at every closed
point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Ampleness in the projective sense: a positive multiple is linearly equivalent to the
hyperplane divisor of an actual closed immersion over the base field. -/
def CartierIsAmpleProj (A : CartierDivisor Y) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (n : ℕ) (e : Y ⟶ polynomialProjectiveScheme n K) (_ : IsClosedImmersion e)
    (_ : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal) (f : Y.functionFieldˣ),
    m • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y f

variable {K} in
/-- Global generation: at every point some actual global section has a unit local
coefficient. -/
def CartierIsGloballyGenerated (D : CartierDivisor Y) : Prop :=
  ∀ x : Y, ∃ s : Γ(D.sheaf, ⊤),
    IsUnit (cartierLocalCoefficient D x (Classical.choose (D.exists_isLocalEquationAt x))
      (Classical.choose_spec (D.exists_isLocalEquationAt x)) s)

/-- The multiplicity half of Lemma 1 for an ample divisor on a smooth variety. -/
theorem cartierIsAmpleProj_vanishingOrder_le [IsAlgClosed K]
    [Smooth (Y ↘ Spec (CommRingCat.of K))] {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
      ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
        cartierSectionVanishingOrder (j • A) x s ≤ ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨m, hm, n, e, _, he, g, hg, hggen, f, hmA⟩ := hA
  exact cartierMultiple_vanishingOrder_le e g hg hggen he hn hd A hm f hmA

end MixedFujita
