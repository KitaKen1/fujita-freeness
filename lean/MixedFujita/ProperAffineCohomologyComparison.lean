/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACohomologyComparison
public import SGA.Foundations.Cohomology.LerayTransfer
public import MixedFujita.ProperCartierCohomology

/-! 実affine順像と元加群の全次数実コホモロジー加法同型。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The actual cohomology of an affine pushforward is that of the
original source, via the existing finite affine Cech comparison. -/
noncomputable def properAffineCohomologyAddEquiv
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (j : Y ⟶ X) [IsAffineHom j] (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Scheme.Modules.Cohomology M q ≃+
      Scheme.Modules.Cohomology ((Scheme.Modules.pushforward j).obj M) q := by
  classical
  apply Classical.choice
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (X ↘ Spec (CommRingCat.of K))
  let : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward j M
  obtain ⟨n, U, hcov, hU⟩ := CohomologyAux.exists_cechCover X
  exact ⟨(sgaCohomologyLinearEquiv M q).toAddEquiv.symm.trans
    ((CohomologyAux.pushforwardHAddEquiv j M U hcov hU
      (fun x p => M.H'_subsingleton_of_isAffineOpen ((hU x).preimage j) p) q).trans
        (sgaCohomologyLinearEquiv ((Scheme.Modules.pushforward j).obj M) q).toAddEquiv)⟩

end MixedFujita
