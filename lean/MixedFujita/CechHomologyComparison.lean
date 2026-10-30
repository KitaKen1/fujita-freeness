/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierCechBaseChange
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import MixedFujita.SGACohomologyComparison
public import SGA.Foundations.Cohomology.AffineOpenVanishing
public import SGA.Foundations.Cohomology.LerayTransfer
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base

/-!
Čech cohomology as a module over the base ring (step 10, R4).

The homology of a cochain complex of abelian groups is the explicit quotient of cocycles by
coboundaries (`homologyExplicitAddEquiv`), naturally in chain maps
(`homologyExplicitAddEquiv_naturality`, through a `LeftHomologyMapData` between the explicit left
homology data). For an `𝒪_X`-module `M` on a scheme over `Spec R` and finitely many opens, SGA's
explicit Čech cohomology is the cohomology `homologyAt` of the `R`-linear Čech differential
(`cechExplicitHomologyAddEquiv`), and the base ring acts as the global function it defines
(`cechExplicitHomologyAddEquiv_smul`). With SGA's Leray comparison this makes Čech cohomology
`R`-linearly sheaf cohomology for a finite affine cover of a scheme with affine diagonal
(`cechHomologyAtCohomologyLinearEquiv`): it is finitely generated when the sheaf cohomology is
(`finite_cechHomologyAt`), the Čech complex is exact exactly where the sheaf cohomology vanishes
(`exact_cechDₗ_iff_subsingleton_cohomology`), and the global sections are Čech `H⁰`
(`cechAugmentationLinear_bijective`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Explicit

variable {K L : CochainComplex AddCommGrpCat.{u} ℕ}

/-- The explicit homology of a cochain complex of abelian groups in degree `i + 1`: cocycles
modulo coboundaries. -/
abbrev explicitHomology (K : CochainComplex AddCommGrpCat.{u} ℕ) (i : ℕ) : Type u :=
  AddMonoidHom.ker (K.d (i + 1) (i + 2)).hom ⧸
    AddMonoidHom.range (K.sc' i (i + 1) (i + 2)).abToCycles

/-- **The homology is the explicit homology.** -/
noncomputable def homologyExplicitAddEquiv (K : CochainComplex AddCommGrpCat.{u} ℕ) (i : ℕ) :
    K.homology (i + 1) ≃+ explicitHomology K i :=
  ((K.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)) ≪≫
    (K.sc' i (i + 1) (i + 2)).abLeftHomologyData.homologyIso).addCommGroupIsoToAddEquiv

/-- The map on cocycles induced by a chain map. -/
noncomputable def explicitCyclesMap (φ : K ⟶ L) (i : ℕ) :
    AddMonoidHom.ker (K.d (i + 1) (i + 2)).hom →+ AddMonoidHom.ker (L.d (i + 1) (i + 2)).hom :=
  ((φ.f (i + 1)).hom.comp (AddMonoidHom.ker (K.d (i + 1) (i + 2)).hom).subtype).codRestrict _
    fun z => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
        ← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply,
        (AddMonoidHom.mem_ker).mp z.2, map_zero]

theorem explicitCyclesMap_apply_coe (φ : K ⟶ L) (i : ℕ)
    (z : AddMonoidHom.ker (K.d (i + 1) (i + 2)).hom) :
    (explicitCyclesMap φ i z : L.X (i + 1)) = φ.f (i + 1) z :=
  rfl

/-- **The map on explicit homology induced by a chain map.** -/
noncomputable def explicitHomologyMap (φ : K ⟶ L) (i : ℕ) :
    explicitHomology K i →+ explicitHomology L i :=
  QuotientAddGroup.map _ _ (explicitCyclesMap φ i) (by
    rintro _ ⟨b, rfl⟩
    refine ⟨φ.f i b, ?_⟩
    apply Subtype.ext
    rw [ShortComplex.abToCycles_apply_coe, explicitCyclesMap_apply_coe,
      ShortComplex.abToCycles_apply_coe]
    exact (ConcreteCategory.comp_apply _ _ b).symm.trans
      ((congrArg (fun f => (ConcreteCategory.hom f) b) (φ.comm i (i + 1))).trans
        (ConcreteCategory.comp_apply _ _ b)))

theorem explicitHomologyMap_mk (φ : K ⟶ L) (i : ℕ)
    (z : AddMonoidHom.ker (K.d (i + 1) (i + 2)).hom) :
    explicitHomologyMap φ i (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (explicitCyclesMap φ i z) :=
  rfl

/-- Naturality of the identification of `K.homology (i + 1)` with the homology of
`K.X i ⟶ K.X (i + 1) ⟶ K.X (i + 2)`. -/
theorem homologyIsoShort_naturality_apply (φ : K ⟶ L) (i : ℕ) (x : K.homology (i + 1)) :
    (L.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).hom
        (HomologicalComplex.homologyMap φ (i + 1) x) =
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' _ _ i (i + 1) (i + 2)).map φ)
        ((K.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).hom x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  congr 1
  simp only [HomologicalComplex.homologyIsoSc', ShortComplex.homologyMapIso_hom,
    HomologicalComplex.homologyMap, ← ShortComplex.homologyMap_comp]
  congr 1

/-- The explicit left homology data are natural in chain maps. -/
noncomputable def explicitLeftHomologyMapData (φ : K ⟶ L) (i : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' _ _ i (i + 1) (i + 2)).map φ)
      (K.sc' i (i + 1) (i + 2)).abLeftHomologyData (L.sc' i (i + 1) (i + 2)).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (explicitCyclesMap φ i)
  φH := AddCommGrpCat.ofHom (explicitHomologyMap φ i)
  commi := by
    ext z
    rfl
  commf' := by
    ext b
    apply Subtype.ext
    simp only [ShortComplex.abLeftHomologyData_f', ConcreteCategory.comp_apply,
      AddCommGrpCat.hom_ofHom, HomologicalComplex.shortComplexFunctor'_map_τ₁]
    exact ((ConcreteCategory.comp_apply _ _ b).symm.trans
      ((congrArg (fun f => (ConcreteCategory.hom f) b) (φ.comm i (i + 1))).trans
        (ConcreteCategory.comp_apply _ _ b))).symm
  commπ := by
    ext z
    rfl

/-- **The explicit homology is natural in chain maps.** -/
theorem homologyExplicitAddEquiv_naturality (φ : K ⟶ L) (i : ℕ) (x : K.homology (i + 1)) :
    homologyExplicitAddEquiv L i (HomologicalComplex.homologyMap φ (i + 1) x) =
      explicitHomologyMap φ i (homologyExplicitAddEquiv K i x) := by
  have h2 := ConcreteCategory.congr_hom
    ((explicitLeftHomologyMapData φ i).homologyMap_comm)
    ((K.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).hom x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  change (L.sc' i (i + 1) (i + 2)).abLeftHomologyData.homologyIso.hom
      ((L.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).hom
        (HomologicalComplex.homologyMap φ (i + 1) x)) =
    explicitHomologyMap φ i ((K.sc' i (i + 1) (i + 2)).abLeftHomologyData.homologyIso.hom
      ((K.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).hom x))
  rw [homologyIsoShort_naturality_apply]
  exact h2

end Explicit

section Exactness

variable {R : Type*} [CommRing R] {C : ℕ → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)

/-- **A complex is exact at `C^{q+1}` exactly when its cohomology there vanishes.** -/
theorem exact_iff_subsingleton_homologyAt (q : ℕ) :
    Function.Exact (d q) (d (q + 1)) ↔ Subsingleton (homologyAt d hd q) := by
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with
    | H z =>
      induction b using Submodule.Quotient.induction_on with
      | H w =>
        rw [Submodule.Quotient.eq]
        obtain ⟨c, hc⟩ := (h (z - w).1).mp (LinearMap.mem_ker.mp (z - w).2)
        exact ⟨c, Subtype.ext hc⟩
  · intro hs y
    constructor
    · intro hy
      have hmem : (Submodule.mkQ (LinearMap.range (cycleRestrict d hd q))
          (⟨y, LinearMap.mem_ker.mpr hy⟩ : LinearMap.ker (d (q + 1)))) = 0 := Subsingleton.elim _ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, rfl⟩
      rw [← LinearMap.comp_apply, hd q, LinearMap.zero_apply]

end Exactness

section Cech

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))]
  (M : X.Modules) {n : ℕ} (U : Fin n → X.Opens)

attribute [local instance] sectionsRingModule

/-- **The cocycles of SGA's Čech complex are those of the `R`-linear Čech differential.** -/
noncomputable def cechCyclesAddEquiv (i : ℕ) :
    AddMonoidHom.ker ((TopCat.Presheaf.cechComplex U M.presheaf).d (i + 1) (i + 2)).hom ≃+
      LinearMap.ker (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U
        (i + 1)) where
  toFun z := ⟨z.1, (TopCat.Presheaf.cechComplex_d_apply U M.presheaf (i + 1) z.1).symm.trans z.2⟩
  invFun z := ⟨z.1, (TopCat.Presheaf.cechComplex_d_apply U M.presheaf (i + 1) z.1).trans z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **SGA's explicit Čech cohomology is the cohomology of the `R`-linear Čech differential.** -/
noncomputable def cechExplicitHomologyAddEquiv (i : ℕ) :
    explicitHomology (TopCat.Presheaf.cechComplex U M.presheaf) i ≃+
      homologyAt (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U)
        (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul R M) U) i :=
  QuotientAddGroup.congr _ _ (cechCyclesAddEquiv R M U i) (by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      refine ⟨b, Subtype.ext ?_⟩
      change TopCat.Presheaf.cechD U M.presheaf i b =
        (((TopCat.Presheaf.cechComplex U M.presheaf).sc' i (i + 1) (i + 2)).abToCycles b).1
      rw [ShortComplex.abToCycles_apply_coe]
      exact (TopCat.Presheaf.cechComplex_d_apply U M.presheaf i b).symm
    · rintro ⟨b, rfl⟩
      refine ⟨((TopCat.Presheaf.cechComplex U M.presheaf).sc' i (i + 1) (i + 2)).abToCycles b,
        ⟨b, rfl⟩, Subtype.ext ?_⟩
      change (((TopCat.Presheaf.cechComplex U M.presheaf).sc' i (i + 1) (i + 2)).abToCycles b).1 =
        TopCat.Presheaf.cechD U M.presheaf i b
      rw [ShortComplex.abToCycles_apply_coe]
      exact TopCat.Presheaf.cechComplex_d_apply U M.presheaf i b)

/-- **The base ring acts on Čech cohomology as the global function it defines.** -/
theorem cechExplicitHomologyAddEquiv_smul (i : ℕ) (r : R)
    (x : explicitHomology (TopCat.Presheaf.cechComplex U M.presheaf) i) :
    cechExplicitHomologyAddEquiv R M U i
        (explicitHomologyMap (TopCat.Presheaf.cechComplexMap U
          (M.smulHom (Scheme.Modules.baseRingToGlobalSections R X r)).hom) i x) =
      r • cechExplicitHomologyAddEquiv R M U i x := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [explicitHomologyMap_mk]
    change Submodule.Quotient.mk (cechCyclesAddEquiv R M U i (explicitCyclesMap _ i z)) =
      r • Submodule.Quotient.mk (cechCyclesAddEquiv R M U i z)
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    funext x
    change (M.smulHom (Scheme.Modules.baseRingToGlobalSections R X r)).hom.app
        (op (TopCat.Presheaf.cechOpen U x)) (z.1 x) = r • z.1 x
    rw [Scheme.Modules.smulHom_app_apply, sectionsRing_smul_def,
      Scheme.baseRingToStructurePresheaf_app]
    rfl

/-- **Čech cohomology as an `R`-module is sheaf cohomology**, for a finite affine cover of a scheme
with affine diagonal and a quasi-coherent module. -/
noncomputable def cechHomologyAtCohomologyLinearEquiv
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (i : ℕ) :
    homologyAt (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U)
        (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul R M) U) i ≃ₗ[R]
      Scheme.Modules.Cohomology M (i + 1) where
  toAddEquiv := (cechExplicitHomologyAddEquiv R M U i).symm.trans
    ((homologyExplicitAddEquiv _ i).symm.trans
      ((M.cechHomologyLinearEquiv U (i + 1) (Scheme.Modules.isAffineOpen_cechOpen hU)).toAddEquiv.trans
        ((CohomologyAux.H'CongrOpens M (i + 1) hcov).toAddEquiv.trans
          (sgaCohomologyLinearEquiv M (i + 1)).toAddEquiv)))
  map_smul' r h := by
    set y := (homologyExplicitAddEquiv (TopCat.Presheaf.cechComplex U M.presheaf) i).symm
      ((cechExplicitHomologyAddEquiv R M U i).symm h) with hy
    have hnat := homologyExplicitAddEquiv_naturality
      (K := TopCat.Presheaf.cechComplex U M.presheaf) (L := TopCat.Presheaf.cechComplex U M.presheaf)
      (TopCat.Presheaf.cechComplexMap U
        (M.smulHom (Scheme.Modules.baseRingToGlobalSections R X r)).hom) i y
    have hsm := cechExplicitHomologyAddEquiv_smul R M U i r
      (homologyExplicitAddEquiv (TopCat.Presheaf.cechComplex U M.presheaf) i y)
    have key : (homologyExplicitAddEquiv _ i).symm ((cechExplicitHomologyAddEquiv R M U i).symm
        (r • h)) = Scheme.Modules.baseRingToGlobalSections R X r • y := by
      apply (homologyExplicitAddEquiv _ i).injective
      apply (cechExplicitHomologyAddEquiv R M U i).injective
      rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      symm
      calc cechExplicitHomologyAddEquiv R M U i (homologyExplicitAddEquiv _ i
            (Scheme.Modules.baseRingToGlobalSections R X r • y))
          = cechExplicitHomologyAddEquiv R M U i (homologyExplicitAddEquiv
              (TopCat.Presheaf.cechComplex U M.presheaf) i
              (HomologicalComplex.homologyMap (K := TopCat.Presheaf.cechComplex U M.presheaf)
                (L := TopCat.Presheaf.cechComplex U M.presheaf)
                (TopCat.Presheaf.cechComplexMap U
                  (M.smulHom (Scheme.Modules.baseRingToGlobalSections R X r)).hom) (i + 1) y)) := rfl
        _ = cechExplicitHomologyAddEquiv R M U i (explicitHomologyMap
              (TopCat.Presheaf.cechComplexMap U
                (M.smulHom (Scheme.Modules.baseRingToGlobalSections R X r)).hom) i
              (homologyExplicitAddEquiv (TopCat.Presheaf.cechComplex U M.presheaf) i y)) := by
            rw [hnat]
            rfl
        _ = r • cechExplicitHomologyAddEquiv R M U i
              (homologyExplicitAddEquiv (TopCat.Presheaf.cechComplex U M.presheaf) i y) := hsm
        _ = r • h := by rw [hy, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    change (sgaCohomologyLinearEquiv M (i + 1)) ((CohomologyAux.H'CongrOpens M (i + 1) hcov)
        ((M.cechHomologyLinearEquiv U (i + 1) (Scheme.Modules.isAffineOpen_cechOpen hU))
          ((homologyExplicitAddEquiv _ i).symm ((cechExplicitHomologyAddEquiv R M U i).symm
            (r • h))))) =
      r • (sgaCohomologyLinearEquiv M (i + 1)) ((CohomologyAux.H'CongrOpens M (i + 1) hcov)
        ((M.cechHomologyLinearEquiv U (i + 1) (Scheme.Modules.isAffineOpen_cechOpen hU))
          y))
    rw [key, LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Scheme.Modules.base_smul_cohomology]

include R in
/-- **Finite generation of Čech cohomology** from that of sheaf cohomology. -/
theorem finite_cechHomologyAt
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (i : ℕ)
    [Module.Finite R (Scheme.Modules.Cohomology M (i + 1))] :
    Module.Finite R (homologyAt (TopCat.Presheaf.cechDₗ M.presheaf
      (presheaf_map_homOfLE_ring_smul R M) U)
        (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul R M) U) i) :=
  Module.Finite.equiv (cechHomologyAtCohomologyLinearEquiv R M U hU hcov i).symm

/-- **Exactness of the `R`-linear Čech complex is vanishing of sheaf cohomology.** -/
theorem exact_cechDₗ_iff_subsingleton_cohomology
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (q : ℕ) :
    Function.Exact (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U q)
        (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U (q + 1)) ↔
      Subsingleton (Scheme.Modules.Cohomology M (q + 1)) :=
  (exact_iff_subsingleton_homologyAt _
    (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul R M) U) q).trans
    (cechHomologyAtCohomologyLinearEquiv R M U hU hcov q).toEquiv.subsingleton_congr

/-- The restrictions of a global section to the opens of a cover, as a Čech cocycle. -/
noncomputable def cechAugmentationLinear :
    Γ(M, ⊤) →ₗ[R] LinearMap.ker
      (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U 0) where
  toFun s := ⟨TopCat.Presheaf.cechAugmentation U M.presheaf
      (M.presheaf.map (homOfLE (le_top : ⨆ i, U i ≤ ⊤)).op s), by
    rw [LinearMap.mem_ker, TopCat.Presheaf.cechDₗ_apply, TopCat.Presheaf.cechD_cechAugmentation]⟩
  map_add' s t := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  map_smul' r s := by
    apply Subtype.ext
    funext x
    rw [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply]
    dsimp only
    rw [TopCat.Presheaf.cechAugmentation_apply, TopCat.Presheaf.cechAugmentation_apply,
      presheaf_map_homOfLE_ring_smul, presheaf_map_homOfLE_ring_smul]

/-- **Global sections are Čech `H⁰`** for a cover of the scheme. -/
theorem cechAugmentationLinear_bijective (hcov : ⨆ i, U i = ⊤) :
    Function.Bijective (cechAugmentationLinear R M U) := by
  constructor
  · intro s t hst
    have hst' : TopCat.Presheaf.cechAugmentation U M.presheaf
          (M.presheaf.map (homOfLE (le_top : ⨆ i, U i ≤ ⊤)).op s) =
        TopCat.Presheaf.cechAugmentation U M.presheaf
          (M.presheaf.map (homOfLE (le_top : ⨆ i, U i ≤ ⊤)).op t) :=
      congrArg Subtype.val hst
    have h2 := TopCat.Presheaf.cechAugmentation_injective U M.toAbSheaf hst'
    have h3 := congrArg (M.presheaf.map (homOfLE hcov.ge).op) h2
    rwa [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply,
      CohomologyAux.modules_map_self, CohomologyAux.modules_map_self] at h3
  · intro c
    obtain ⟨s', hs'⟩ := TopCat.Presheaf.exists_cechAugmentation_eq U M.toAbSheaf c.1
      (LinearMap.mem_ker.mp c.2)
    refine ⟨M.presheaf.map (homOfLE hcov.ge).op s', Subtype.ext ?_⟩
    change TopCat.Presheaf.cechAugmentation U M.presheaf
      (M.presheaf.map _ (M.presheaf.map (homOfLE hcov.ge).op s')) = c.1
    rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
    exact hs'

end Cech

end MixedFujita
