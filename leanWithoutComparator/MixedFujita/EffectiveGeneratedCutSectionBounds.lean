/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PulledNegativeCartierSectionBounds
public import MixedFujita.CartierCutEuler
public import MixedFujita.ClosedImmersionCohomology
public import MixedFujita.CohomologyOneSectionLifting

/-! 実有効生成切断の全反復損失上界と有限非消滅判定。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Actual coherent global sections are finite over every proper field source. -/
theorem proper_coherent_moduleSections_finite
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] (M : X.Modules) [M.IsCoherent] :
    Module.Finite K Γ(M, ⊤) := by
  let := proper_coherent_cohomology_finite K M 0
  exact Module.Finite.equiv (Scheme.Modules.cohomologyZeroBaseLinearEquiv K X M)


/-- Exactness alone bounds the middle dimension by the sum of the outer
dimensions; surjectivity of the second map is not required. -/
theorem linearMap_finrank_middle_le_add_of_exact
    {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    [FiniteDimensional K V] [FiniteDimensional K W] [FiniteDimensional K Z]
    (f : V →ₗ[K] W) (g : W →ₗ[K] Z) (h : Function.Exact f g) :
    Module.finrank K W ≤ Module.finrank K V + Module.finrank K Z := by
  have hker : g.ker = f.range := LinearMap.exact_iff.mp h
  have hd := g.finrank_range_add_finrank_ker
  have h₁ : Module.finrank K g.range ≤ Module.finrank K Z := Submodule.finrank_le _
  have h₂ : Module.finrank K g.ker ≤ Module.finrank K V := by
    rw [hker]
    exact LinearMap.finrank_range_le f
  omega


/-- Proper coherent section dimensions are subadditive in an ACTUAL
short exact sequence, without H1 vanishing or a supplied section lift. -/
theorem proper_shortExact_moduleSections_finrank_le
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    Module.finrank K Γ(S.X₂, ⊤) ≤ Module.finrank K Γ(S.X₁, ⊤) + Module.finrank K Γ(S.X₃, ⊤) := by
  let := proper_coherent_moduleSections_finite K S.X₁
  let := proper_coherent_moduleSections_finite K S.X₂
  let := proper_coherent_moduleSections_finite K S.X₃
  exact linearMap_finrank_middle_le_add_of_exact
    (moduleHomGlobalSectionsBaseLinearMap K S.f) (moduleHomGlobalSectionsBaseLinearMap K S.g)
    (Scheme.Modules.exact_sections hS)


/-- The actual Cartier cut carries its canonical structure over the
same field, so its actual global sections have the specified scalar action. -/
@[instance_reducible]
noncomputable def effectiveCartierCutOverField
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (G : CartierDivisor X) (hG : G.IsEffective) :
    (effectiveCartierIdealSheaf G hG).subscheme.Over (Spec (CommRingCat.of K)) :=
  ⟨(effectiveCartierIdealSheaf G hG).subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩

attribute [local instance] effectiveCartierCutOverField


/-- Removing one actual effective Cartier cut loses at most the actual
dimension of the pulled coefficient's sections on the nonreduced cut. -/
theorem proper_effectiveCartierCut_moduleSections_finrank_le
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D G : CartierDivisor X) (hG : G.IsEffective) :
    Module.finrank K Γ(D.sheaf, ⊤) ≤ Module.finrank K Γ((D - G).sheaf, ⊤) +
      Module.finrank K Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj D.sheaf, ⊤) := by
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let M := (Scheme.Modules.pullback i).obj D.sheaf
  let : SheafOfModules.isInvertible Y M := cartierPullbackSheaf_isInvertible D i
  let : M.IsCoherent := invertible_module_isCoherent M
  let S := cartierCutShortComplex D G hG
  let : S.X₁.IsCoherent := by
    change (D - G).sheaf.IsCoherent
    let := (D - G).isInvertible_sheaf
    exact invertible_module_isCoherent _
  let : S.X₂.IsCoherent := by
    change D.sheaf.IsCoherent
    let := D.isInvertible_sheaf
    exact invertible_module_isCoherent _
  let : S.X₃.IsCoherent := CohomologyAux.isCoherent_pushforward_of_isClosedImmersion i M
  have h := proper_shortExact_moduleSections_finrank_le K (cartierCutShortComplex_shortExact D G hG)
  have hthird : Module.finrank K Γ(S.X₃, ⊤) = Module.finrank K Γ(M, ⊤) := by
    rw [← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections K,
      ← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections K]
    exact (closedImmersionCohomologyBaseLinearEquiv K i M 0).finrank_eq
  change Module.finrank K Γ(D.sheaf, ⊤) ≤ Module.finrank K Γ((D - G).sheaf, ⊤) +
    Module.finrank K Γ(S.X₃, ⊤) at h
  rw [hthird] at h
  exact h


/-- A single cut-section count bounds the TOTAL loss after removing any
number of generated effective cuts. The actual cut retains its nilpotents. -/
theorem proper_effective_generated_cut_moduleSections_total_loss_le
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D G : CartierDivisor X) (hG : G.IsEffective) (hgen : CartierIsGloballyGenerated G) (j : ℕ) :
    Module.finrank K Γ(D.sheaf, ⊤) ≤ Module.finrank K Γ((D - j • G).sheaf, ⊤) +
      j * Module.finrank K Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj D.sheaf, ⊤) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  induction j with
  | zero =>
    have he : D - (0 : ℕ) • G = D := by simp
    rw [he, zero_mul, add_zero]
  | succ j ih =>
    have hstep := proper_effectiveCartierCut_moduleSections_finrank_le K (D - j • G) G hG
    have hcut := proper_cartierPulled_negative_twist_sections_le K i G hgen D j
    dsimp only [i, Y, effectiveCartierCutOverField] at hcut
    have he : D - j • G - G = D - (j + 1) • G := by module
    rw [he] at hstep
    rw [Nat.succ_mul]
    omega


/-- A strict finite section-count inequality gives an ACTUAL nonzero
section of the original difference; no positivity or vanishing axiom is used. -/
theorem proper_exists_nonzero_section_sub_generated_cut_of_count_lt
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D G : CartierDivisor X) (hG : G.IsEffective) (hgen : CartierIsGloballyGenerated G) (j : ℕ)
    (hcount : j * Module.finrank K Γ((Scheme.Modules.pullback
      (effectiveCartierIdealSheaf G hG).subschemeι).obj D.sheaf, ⊤) < Module.finrank K Γ(D.sheaf, ⊤)) :
    ∃ s : Γ((D - j • G).sheaf, ⊤), s ≠ 0 := by
  let := proper_cartier_sections_finite K (D - j • G)
  have h := proper_effective_generated_cut_moduleSections_total_loss_le K D G hG hgen j
  have hpos : 0 < Module.finrank K Γ((D - j • G).sheaf, ⊤) := by omega
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

end MixedFujita
