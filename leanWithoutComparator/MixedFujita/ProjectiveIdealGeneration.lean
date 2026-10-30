/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveCharts
public import Hironaka.Scheme.Modules.IdealSheafFinite
public import SGA.Foundations.Cohomology.Extension
public import SGA.Foundations.Cohomology.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Finite global generators after twisting the ideal of a blow-up centre. For a closed immersion
of an integral locally Noetherian scheme into polynomial projective space, the pushforward of
the centre ideal is quasi-coherent and finite on every standard chart. Serre's section-extension
argument supplies finitely many global sections of its sufficiently large twists. The chart
finiteness and quasi-coherence certificates are constructed from the ideal and the immersion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (I : X.IdealSheafData)

/-- The ideal module is quasi-coherent, by its finite-presentation datum. -/
theorem ideal_toModules_isQuasicoherent : I.toModules.IsQuasicoherent := by
  obtain ⟨σ, hσ⟩ := I.isFinitePresentation_toModules.exists_quasicoherentData
  exact σ.isQuasicoherent

/-- The pushforward ideal is finite on each standard affine chart of projective space. -/
theorem projective_pushforward_ideal_chart_finite (i : Fin n) :
    Module.Finite Γ(polynomialProjectiveScheme n K, projectiveSpace.topStd (Fin n) K i)
      Γ((Scheme.Modules.pushforward e).obj I.toModules,
        projectiveSpace.topStd (Fin n) K i) := by
  let U := projectiveSpace.topStd (Fin n) K i
  have hU : IsAffineOpen U := projectiveSpace.isAffineOpen_topStd (σ := Fin n) (A := K) i
  have hV : IsAffineOpen (e ⁻¹ᵁ U) := hU.preimage e
  let V : X.affineOpens := ⟨e ⁻¹ᵁ U, hV⟩
  let R := Γ(polynomialProjectiveScheme n K, U)
  let S := Γ(X, e ⁻¹ᵁ U)
  letI : Algebra R S := (e.app U).hom.toAlgebra
  have hS : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) (e.app_surjective U hU)
  have : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian V
  have hM : Module.Finite S Γ(I.toModules, e ⁻¹ᵁ U) :=
    Module.Finite.equiv (I.toModulesSectionsEquiv V).symm
  letI : Module R Γ(I.toModules, e ⁻¹ᵁ U) := Module.compHom _ (e.app U).hom
  change Module.Finite R Γ(I.toModules, e ⁻¹ᵁ U)
  have hTower : IsScalarTower R S Γ(I.toModules, e ⁻¹ᵁ U) := by
    constructor
    intro r s m
    change (e.app U r * s) • m = e.app U r • (s • m)
    exact mul_smul _ _ _
  exact Module.Finite.trans S Γ(I.toModules, e ⁻¹ᵁ U)

/-- All sufficiently large twists of the pushforward centre ideal have finitely many global
generators on every standard chart. No cohomology or generation certificate is supplied. -/
theorem exists_generating_projective_ideal_twist_sections :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ (J : Type u) (_ : Fintype J)
      (s : J → Γ((projectiveSpace.twistingBundle (Fin n) K).twist
        ((Scheme.Modules.pushforward e).obj I.toModules) d, ⊤)),
      ∀ i : Fin n,
        Submodule.span Γ(polynomialProjectiveScheme n K, projectiveSpace.topStd (Fin n) K i)
          (Set.range fun j => ((projectiveSpace.twistingBundle (Fin n) K).twist
            ((Scheme.Modules.pushforward e).obj I.toModules) d).presheaf.map
              (homOfLE le_top : projectiveSpace.topStd (Fin n) K i ⟶ ⊤).op (s j)) = ⊤ := by
  classical
  obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
  have : Nonempty (Fin n) := ⟨i⟩
  have := ideal_toModules_isQuasicoherent I
  have := CohomologyAux.isQuasicoherent_pushforward e I.toModules
  exact projectiveSpace.exists_generating_twist_sections
    ((Scheme.Modules.pushforward e).obj I.toModules) (projective_pushforward_ideal_chart_finite e I)

end MixedFujita
