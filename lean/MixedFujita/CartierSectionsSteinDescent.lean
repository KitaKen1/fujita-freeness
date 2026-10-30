/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.CartierGlobalGenerationFiniteFamily
public import MixedFujita.ProjectiveCartierPullbackComposition
public import MixedFujita.ProjectiveHyperplaneSGAAmpleness
public import MixedFujita.NormalSteinFactorization
public import MixedFujita.FiniteProjectiveCartierAmpleness

/-!
Descend an actual globally generated Cartier divisor through the Stein factor of its existing
polynomial-Proj section morphism. The target divisor is an explicit coordinate hyperplane cut,
and its actual Cartier pullback differs from the source divisor by a constructed principal
divisor. The same target is normal and proper, the hyperplane divisor is effective and globally
generated, and both its SGA presentation and its actual projective-embedding Cartier class are ample
by the finite map to projective space.
This concerns a free divisor (hence an individual free multiple); common-target descent from
different multiples and target dimension remain open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

theorem cartierSections_exists_normal_stein_descended_divisor (D : CartierDivisor X)
    {r : ℕ} (t : Fin r → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin r)
    (hne : ∀ β, t (idx β) ≠ 0)
    (hcover : (⨆ β, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤)
    (β₀ : ι) (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K))) (g : X ⟶ Y) (_ : IsDominant g)
      (h : Y ⟶ polynomialProjectiveScheme r K) (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsFinite h ∧ g ≫ h = cartierSectionsMap K D t idx hne hcover ∧
      h ≫ polynomialProjectiveToBase r K = Y ↘ Spec (CommRingCat.of K) ∧
      g ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) ∧
      (∀ V : Y.Opens, Function.Bijective (g.app V).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsProper (Y ↘ Spec (CommRingCat.of K)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ (cartierSGALineBundle H).IsAmple ∧ CartierIsAmpleProj K H ∧
      D = cartierPullback g H + principalCartierDivisor X φ := by
  let ψ := cartierSectionsMap K D t idx hne hcover
  have : IsProper ψ := cartierSectionsMap_isProper (K := K) D t idx hne hcover
  have := polynomialProjectiveToBase_isProper r K
  have : IsLocallyNoetherian (polynomialProjectiveScheme r K) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveToBase r K)
  obtain ⟨Y, hY, hYN, g, hgd, h, hg, hh, he, happ, hconn, hnormY⟩ :=
    properMap_exists_normal_stein_factorization ψ hnorm
  letI := hY
  letI := hYN
  letI := hgd
  letI := hg
  letI := hh
  letI : Y.Over (Spec (CommRingCat.of K)) := ⟨h ≫ polynomialProjectiveToBase r K⟩
  have hψgen : MvPolynomial.X (idx β₀) ∉ (ψ (genericPoint X)).asHomogeneousIdeal := by
    have := cartierSectionsMap_coordinateOpen_nonempty (K := K) D t idx hne hcover (idx β₀) (hne β₀)
    change genericPoint X ∈ projectivePullbackCoordinateOpen ψ (idx β₀)
    exact genericPoint_mem _
  have hhgen : MvPolynomial.X (idx β₀) ∉ (h (genericPoint Y)).asHomogeneousIdeal := by
    have hept : h (genericPoint Y) = ψ (genericPoint X) := by
      calc
        _ = h (g (genericPoint X)) := by rw [dominant_map_genericPoint g]
        _ = (g ≫ h) (genericPoint X) := rfl
        _ = ψ (genericPoint X) := congrArg (fun a => a (genericPoint X)) he
    rwa [hept]
  let H := projectiveHyperplaneCartier h (MvPolynomial.X (idx β₀))
    (MvPolynomial.isHomogeneous_X K (idx β₀)) hhgen
  let φ := (cartierSectionUnit D (t (idx β₀)) (hne β₀))⁻¹
  have hpY : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (h ≫ polynomialProjectiveToBase r K)
    infer_instance
  refine ⟨Y, hY, hYN, inferInstance, g, hgd, h, H, φ, hg, hh, he, rfl, ?_,
    happ, hconn, hnormY, hpY, ?_, ?_, ?_, ?_, ?_⟩
  · change g ≫ h ≫ polynomialProjectiveToBase r K = _
    rw [← Category.assoc, he]
    exact cartierSectionsMap_over (K := K) D t idx hne hcover
  · exact projectivePullbackHomogeneousCartier_isEffective h 1 _ _ one_pos hhgen
  · exact projectiveHyperplaneCartier_globallyGenerated h _ _ hhgen
  · exact projectiveHyperplaneCartier_sga_isAmple_of_finite h _ _ hhgen
  · exact projectiveHyperplaneCartier_isAmpleProj_of_finite h _ _ hhgen rfl
  · change D = cartierPullback g
      (projectiveHyperplaneCartier h _ (MvPolynomial.isHomogeneous_X K (idx β₀)) hhgen) +
        principalCartierDivisor X φ
    rw [cartierPullback_projectiveHyperplaneCartier]
    simpa only [he] using cartierSectionsMap_hyperplane (K := K) D t idx hne hcover β₀ hψgen

/-- Ordinary global generation constructs the finite linear system, normal Stein factor and
explicit descended Cartier divisor, with actual linear equivalence D ~ g*H. -/
theorem cartierGloballyGenerated_exists_normal_stein_descended_divisor (D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (r : ℕ), 0 < r ∧ ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K))) (g : X ⟶ Y) (_ : IsDominant g)
      (h : Y ⟶ polynomialProjectiveScheme r K) (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsFinite h ∧
      h ≫ polynomialProjectiveToBase r K = Y ↘ Spec (CommRingCat.of K) ∧
      g ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) ∧
      (∀ V : Y.Opens, Function.Bijective (g.app V).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsProper (Y ↘ Spec (CommRingCat.of K)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ (cartierSGALineBundle H).IsAmple ∧ CartierIsAmpleProj K H ∧
      D = cartierPullback g H + principalCartierDivisor X φ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  obtain ⟨r, t, ht⟩ := cartierIsGloballyGenerated_exists_fin_basePointFree D hD
  let ι := ULift.{u} {i : Fin r // t i ≠ 0}
  let idx : ι → Fin r := fun β => β.down.val
  have hne : ∀ β : ι, t (idx β) ≠ 0 := fun β => β.down.property
  have hcover : (⨆ β : ι, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := ht x
    have hx : x ∈ cartierSectionNonvanishingOpen D (t i) :=
      (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D (t i) x _ _).mpr hi
    have hti : t i ≠ 0 := (cartierSectionNonvanishingOpen_nonempty_iff D (t i)).mp ⟨⟨x, hx⟩⟩
    exact Opens.mem_iSup.mpr ⟨ULift.up ⟨i, hti⟩, hx⟩
  obtain ⟨β₀, -⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top (genericPoint X)))
  have hr : 0 < r := (Nat.zero_le (idx β₀).val).trans_lt (idx β₀).isLt
  obtain ⟨Y, hY, hYN, hYO, g, hgd, h, H, φ, hg, hh, -, hbase, hgbase,
    happ, hconn, hnormY, hp, heff, hgg, hamp, hproj, hdesc⟩ :=
    cartierSections_exists_normal_stein_descended_divisor (K := K) D t idx hne hcover β₀ hnorm
  exact ⟨r, hr, Y, hY, hYN, hYO, g, hgd, h, H, φ, hg, hh, hbase, hgbase,
    happ, hconn, hnormY, hp, heff, hgg, hamp, hproj, hdesc⟩

end MixedFujita
