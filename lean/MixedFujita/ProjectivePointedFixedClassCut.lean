/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePullbackFixedClass
public import MixedFujita.ProjectivePointedCartierCut

/-!
One reference divisor is fixed before the closed point and finite avoidance
set are chosen. Its actual module sheaf has nonzero global sections whose
actual effective Cartier zero cuts satisfy the point conditions. This
does not assert smooth or integral cuts, Bertini flags, or cohomology windows.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Nontrivial Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

theorem polynomialProjective_closedImmersion_pointed_referenceSection
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    let J := projectivePullbackHomogeneousCartier e 1 g hg Nat.zero_lt_one hggen
    ∃ (s : Γ(J.sheaf, ⊤)) (hs : s ≠ 0),
      let I := effectiveCartierIdealSheaf (cartierSectionZeroDivisor J s hs)
        (cartierSectionZeroDivisor_isEffective J s hs)
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  obtain ⟨f, hfgen, hcut⟩ :=
    polynomialProjective_closedImmersion_pointed_effectiveCartierCut e x hx Z hZ hxZ
  let s := projectivePullbackHomogeneousReferenceSection e k 1 f.val f.property g hg
    Nat.zero_lt_one hfgen hggen
  have hs : s ≠ 0 := projectivePullbackHomogeneousReferenceSection_ne_zero e k 1 f.val
    f.property g hg Nat.zero_lt_one hfgen hggen
  refine ⟨s, hs, ?_⟩
  have hz : cartierSectionZeroDivisor
      (projectivePullbackHomogeneousCartier e 1 g hg Nat.zero_lt_one hggen) s hs =
        projectivePullbackHomogeneousCartier e 1 f.val f.property Nat.zero_lt_one hfgen :=
    projectivePullbackHomogeneousReferenceSection_zeroDivisor e k 1 f.val
      f.property g hg Nat.zero_lt_one hfgen hggen
  have hI : effectiveCartierIdealSheaf
      (cartierSectionZeroDivisor
        (projectivePullbackHomogeneousCartier e 1 g hg Nat.zero_lt_one hggen) s hs)
      (cartierSectionZeroDivisor_isEffective _ s hs) =
        projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hfgen := by
    dsimp only [projectivePullbackCartierIdealSheaf]
    congr 1
  exact hI.symm ▸ hcut

include e in
theorem polynomialProjective_closedImmersion_exists_fixedClass_pointedCartierSections :
    ∃ J : CartierDivisor Y, J.IsEffective ∧
      ∀ (x : Y), IsClosed {x} → ∀ (Z : Set Y), Z.Finite → x ∉ Z →
        ∃ (s : Γ(J.sheaf, ⊤)) (hs : s ≠ 0),
          let I := effectiveCartierIdealSheaf (cartierSectionZeroDivisor J s hs)
            (cartierSectionZeroDivisor_isEffective J s hs)
          Nonempty (InvertibleIdealPresentation I) ∧
            x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k, ⟨⟨genericPoint Y, hk⟩⟩⟩
  have hg : MvPolynomial.X k ∉ (e (genericPoint Y)).asHomogeneousIdeal := hk
  refine ⟨projectivePullbackHomogeneousCartier e 1 (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one hg,
    projectivePullbackHomogeneousCartier_isEffective e 1 (MvPolynomial.X k)
      (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one hg, ?_⟩
  intro x hx Z hZ hxZ
  exact polynomialProjective_closedImmersion_pointed_referenceSection e j _
    (MvPolynomial.isHomogeneous_X K k) hg x hx Z hZ hxZ

end MixedFujita
