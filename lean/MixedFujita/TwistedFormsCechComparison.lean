/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedCechDeRhamTotal
public import MixedFujita.TwistedFormsTensor
public import MixedFujita.SGACohomologyComparison
public import SGA.Foundations.Cohomology.AffineOpenVanishing

/-!
Čech cohomology of `Ω^b_X(E)` (step 10).

On a quasi-compact scheme covered by étale charts, finitely many charts cover
(`exists_finite_etaleChart_cover`). For a finite affine open cover of a scheme with affine diagonal
(e.g. separated), the Čech cohomology of the quasi-coherent sheaf `Ω^b_X(E)` (check-419) computes
its sheaf cohomology (`twistedFormsSheaf_nonempty_cechHomologyIso`, SGA's comparison theorem), and
so agrees additively with the cohomology of the Kawamata–Viehweg statements
(`twistedFormsSheaf_nonempty_cechHomologyAddEquiv`). These identify the rows of the Čech–de Rham
double complex (check-425) with the cohomology of the sheaves `Ω^b_X(p • D)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

omit [IsIntegral X] in
/-- **Finitely many étale charts cover a quasi-compact scheme covered by étale charts.** -/
theorem exists_finite_etaleChart_cover [CompactSpace X]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) :
    ∃ (N : ℕ) (c : Fin N → EtaleChart K X n), ⨆ i, (c i).U = ⊤ := by
  have hcov : (⋃ c : EtaleChart K X n, ((c.U : X.Opens) : Set X)) = Set.univ := by
    rw [← Opens.coe_iSup, hcover, Opens.coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun c : EtaleChart K X n => (c.U : Set X))
    (fun c => c.U.isOpen) hcov.ge
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, ?_⟩
  refine top_unique fun x _ => ?_
  have hx : x ∈ ⋃ c ∈ t, ((c.U : X.Opens) : Set X) := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion] at hx
  obtain ⟨c, hc, hxc⟩ := hx
  rw [Opens.mem_iSup]
  exact ⟨t.equivFin ⟨c, hc⟩, by simpa using hxc⟩

/-- **The Čech cohomology of `Ω^b_X(E)` is its sheaf cohomology** for a finite affine cover of a
scheme with affine diagonal. -/
theorem twistedFormsSheaf_nonempty_cechHomologyIso
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) (q : ℕ) :
    Nonempty ((TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K E b).presheaf).homology q ≅
      AddCommGrpCat.of ((twistedFormsSheaf K E b).H q)) := by
  have := (isCoherent_twistedFormsSheaf hcover E b).isQuasicoherent
  exact Scheme.Modules.nonempty_cechHomologyIso_H (twistedFormsSheaf K E b) 𝒰 h𝒰 hcov q

/-- The Čech cohomology of `Ω^b_X(E)` is additively the cohomology of the Kawamata–Viehweg
statements. -/
theorem twistedFormsSheaf_nonempty_cechHomologyAddEquiv
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) (q : ℕ) :
    Nonempty ((TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K E b).presheaf).homology q ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K E b) q) := by
  obtain ⟨e⟩ := twistedFormsSheaf_nonempty_cechHomologyIso hcover E b 𝒰 h𝒰 hcov q
  exact ⟨e.addCommGroupIsoToAddEquiv.trans
    (sgaCohomologyLinearEquiv (twistedFormsSheaf K E b) q).toAddEquiv⟩

end MixedFujita
