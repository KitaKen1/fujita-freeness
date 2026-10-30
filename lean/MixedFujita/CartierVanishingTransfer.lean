/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierCechBaseChange
public import MixedFujita.CechHomologyComparison
public import MixedFujita.FlatComplexBaseChange
public import MixedFujita.FibreGlobalSectionsRank
public import MixedFujita.ProperCartierCohomology

/-!
Transfer of the vanishing of the cohomology of `𝒪(D)` from the closed fibre (step 10, R4-7).

Let `X` be integral, proper and flat over a noetherian ring `A`, with a finite affine cover `U_i`
and a Cartier divisor `D` with local equations `g_i` on `U_i` and transition functions `u_{ij}`.
The Čech cochains of `𝒪(D)` are flat over `A` (`flat_cartierCechCochain`: first-vertex
trivializations, check 499, and check 516). Let `𝔪` be a maximal ideal, `X_κ` the fibre over
`κ = A_𝔪/𝔪` with a Cartier divisor `D_κ` whose transition functions are the images of the `u_{ij}`,
and `X_K` the fibre over a field `K` flat over `A_𝔪` (for instance a field containing `A`), with
a Cartier divisor `D_K` with the same property. If `H^j(X_κ, 𝒪(D_κ)) = 0` for all `j ≥ 1` then
`H^j(X_K, 𝒪(D_K)) = 0` for all `j ≥ 1` (`subsingleton_cohomology_of_residueField`): the Čech
complexes are exact in high degrees for all coefficients (check 495), the Čech cohomology of
`𝒪(D)` is finite over `A` (properness, SGA), check 493 transfers exactness from `κ ⊗ Č` to
`K ⊗ Č`, check 499 identifies these with the Čech complexes on the fibres and check 500 with sheaf
cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of A))]

/-- **The Čech cochains of `𝒪(D)` on an affine cover of a flat scheme are flat.** -/
theorem flat_cartierCechCochain [Flat (X ↘ Spec (CommRingCat.of A))] (D : CartierDivisor X)
    {n : ℕ} (U : Fin n → X.Opens)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (hne : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), Nonempty (TopCat.Presheaf.cechOpen U x))
    (gX : Fin n → X.functionFieldˣ) (hgX : ∀ i, ∀ y ∈ U i, D.IsLocalEquationAt y (gX i))
    (q : ℕ) : Module.Flat A (TopCat.Presheaf.CechCochain U D.sheaf.presheaf q) := by
  have : ∀ x : Fin (q + 1) → Fin n, Module.Flat A
      ((CohomologyAux.unitModule X).presheaf.obj (op (TopCat.Presheaf.cechOpen U x))) :=
    fun x => flat_sections_of_flat (hU x)
  have : Module.Flat A
      (TopCat.Presheaf.CechCochain U (CohomologyAux.unitModule X).presheaf q) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A)
      (M := fun x : Fin (q + 1) → Fin n =>
        (CohomologyAux.unitModule X).presheaf.obj (op (TopCat.Presheaf.cechOpen U x)))).symm
  exact Module.Flat.of_linearEquiv (cartierCechTrivialization (A := A) D U hne gX hgX q)

/-- **Transfer of the vanishing of the cohomology of `𝒪(D)` from the closed fibre** to a fibre
over a field flat over the local ring. -/
theorem subsingleton_cohomology_of_residueField [IsNoetherianRing A]
    [IsProper (X ↘ Spec (CommRingCat.of A))] [Flat (X ↘ Spec (CommRingCat.of A))]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hneX : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), Nonempty (TopCat.Presheaf.cechOpen U x))
    (DX : CartierDivisor X) (gX : Fin n → X.functionFieldˣ)
    (hgX : ∀ i, ∀ y ∈ U i, DX.IsLocalEquationAt y (gX i)) (uX : ∀ i j, Γ(X, U i ⊓ U j))
    (huX : ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (uX i j) * gX j = gX i)
    (𝔪 : Ideal A) [𝔪.IsMaximal]
    {Yk : Scheme.{u}} [IsIntegral Yk] [Yk.Over (Spec (CommRingCat.of 𝔪.ResidueField))]
    {gk : Yk ⟶ X}
    (Hk : IsPullback gk (Yk ↘ Spec (CommRingCat.of 𝔪.ResidueField)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
    [IsAffineHom gk] [IsAffineHom (pullback.diagonal (terminal.from Yk))]
    (hneYk : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gk ⁻¹ᵁ U i) x))
    (Dk : CartierDivisor Yk) (gYk : Fin n → Yk.functionFieldˣ)
    (hgYk : ∀ i, ∀ y ∈ gk ⁻¹ᵁ U i, Dk.IsLocalEquationAt y (gYk i))
    (huk : ∀ i j, ∀ (_ : Nonempty (gk ⁻¹ᵁ U i ⊓ gk ⁻¹ᵁ U j : Yk.Opens)),
      Yk.germToFunctionField (gk ⁻¹ᵁ U i ⊓ gk ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gYk j =
        gYk i)
    (hvan : ∀ j, 1 ≤ j → Subsingleton (Scheme.Modules.Cohomology Dk.sheaf j))
    (K : Type u) [Field K] [Algebra A K] [Algebra (Localization.AtPrime 𝔪) K]
    [IsScalarTower A (Localization.AtPrime 𝔪) K] [Module.Flat (Localization.AtPrime 𝔪) K]
    {YK : Scheme.{u}} [IsIntegral YK] [YK.Over (Spec (CommRingCat.of K))] {gK : YK ⟶ X}
    (HK : IsPullback gK (YK ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    [IsAffineHom gK] [IsAffineHom (pullback.diagonal (terminal.from YK))]
    (hneYK : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gK ⁻¹ᵁ U i) x))
    (DK : CartierDivisor YK) (gYK : Fin n → YK.functionFieldˣ)
    (hgYK : ∀ i, ∀ y ∈ gK ⁻¹ᵁ U i, DK.IsLocalEquationAt y (gYK i))
    (huK : ∀ i j, ∀ (_ : Nonempty (gK ⁻¹ᵁ U i ⊓ gK ⁻¹ᵁ U j : YK.Opens)),
      YK.germToFunctionField (gK ⁻¹ᵁ U i ⊓ gK ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gYK j =
        gYK i)
    {j : ℕ} (hj : 1 ≤ j) : Subsingleton (Scheme.Modules.Cohomology DK.sheaf j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hUc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x) :=
    Scheme.Modules.isAffineOpen_cechOpen hU
  let := DX.isInvertible_sheaf
  let := Dk.isInvertible_sheaf
  let := DK.isInvertible_sheaf
  have : DX.sheaf.IsCoherent := invertible_module_isCoherent _
  have : DX.sheaf.IsQuasicoherent := invertibleModule_isQuasicoherent _
  have : Dk.sheaf.IsQuasicoherent := invertibleModule_isQuasicoherent _
  have : DK.sheaf.IsQuasicoherent := invertibleModule_isQuasicoherent _
  have : ∀ q, Module.Flat A (TopCat.Presheaf.CechCochain U DX.sheaf.presheaf q) :=
    flat_cartierCechCochain DX U hUc hneX gX hgX
  have hfg : ∀ q, 0 ≤ q → Module.Finite A (homologyAt
      (TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U)
      (cechDₗ_comp_eq_zero DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U) q) := by
    intro q _
    have := proper_coherent_cohomology_finite A DX.sheaf (q + 1)
    exact finite_cechHomologyAt A DX.sheaf U hU hcov q
  have hcovk : ⨆ i, gk ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  have hcovK : ⨆ i, gK ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  have hk : ∀ q, 0 ≤ q → Function.Exact
      ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
        q).lTensor 𝔪.ResidueField)
      ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
        (q + 1)).lTensor 𝔪.ResidueField) := fun q _ =>
    (exact_lTensor_cartierCech_iff Hk U hUc DX Dk hneX hneYk gX hgX gYk hgYk uX huX huk q).mpr
      ((exact_cechDₗ_iff_subsingleton_cohomology 𝔪.ResidueField Dk.sheaf (fun i => gk ⁻¹ᵁ U i)
        (fun i => (hU i).preimage gk) hcovk q).mpr (hvan (q + 1) (by omega)))
  have hK := exact_lTensor_of_exact_residueField
    (TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U)
    (cechDₗ_comp_eq_zero DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U) 𝔪 n 0
    (fun N _ _ q hq => exact_lTensor_cechDₗ_modules_of_card_le A DX.sheaf U N q (by omega)) hfg hk
    K i (Nat.zero_le i)
  exact (exact_cechDₗ_iff_subsingleton_cohomology K DK.sheaf (fun i => gK ⁻¹ᵁ U i)
    (fun i => (hU i).preimage gK) hcovK i).mp
    ((exact_lTensor_cartierCech_iff HK U hUc DX DK hneX hneYK gX hgX gYK hgYK uX huX huK i).mp hK)

/-- **A field containing a domain is flat over its localizations**: the algebra structure over
`A_𝔪` (`localizationAtPrimeFieldAlgebra`) and the flatness (through the fraction field of
`A_𝔪`). -/
@[instance_reducible]
noncomputable def localizationAtPrimeFieldAlgebra [IsDomain A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (K : Type u) [Field K] [Algebra A K] (hK : Function.Injective (algebraMap A K)) :
    Algebra (Localization.AtPrime 𝔪) K :=
  (IsLocalization.lift (M := 𝔪.primeCompl) (S := Localization.AtPrime 𝔪) (g := algebraMap A K)
    fun s => by
      have hs : (s : A) ≠ 0 := fun h0 => s.2 (by rw [h0]; exact 𝔪.zero_mem)
      exact ((map_ne_zero_iff (algebraMap A K) hK).mpr hs).isUnit).toAlgebra

theorem localizationAtPrimeFieldAlgebra_isScalarTower [IsDomain A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (K : Type u) [Field K] [Algebra A K] (hK : Function.Injective (algebraMap A K)) :
    letI := localizationAtPrimeFieldAlgebra 𝔪 K hK
    IsScalarTower A (Localization.AtPrime 𝔪) K :=
  letI := localizationAtPrimeFieldAlgebra 𝔪 K hK
  IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm

theorem localizationAtPrimeFieldAlgebra_flat [IsDomain A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (K : Type u) [Field K] [Algebra A K] (hK : Function.Injective (algebraMap A K)) :
    letI := localizationAtPrimeFieldAlgebra 𝔪 K hK
    Module.Flat (Localization.AtPrime 𝔪) K := by
  let _ := localizationAtPrimeFieldAlgebra 𝔪 K hK
  have hinj : Function.Injective (algebraMap (Localization.AtPrime 𝔪) K) := by
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [(IsLocalization.injective (Localization.AtPrime 𝔪)
      𝔪.primeCompl_le_nonZeroDivisors).eq_iff, hK.eq_iff]
  let F := FractionRing (Localization.AtPrime 𝔪)
  let _ : Algebra F K := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔪) F K :=
    IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have : Module.Flat (Localization.AtPrime 𝔪) F :=
    IsLocalization.flat F (nonZeroDivisors (Localization.AtPrime 𝔪))
  exact Module.Flat.trans (Localization.AtPrime 𝔪) F K

/-- **Transfer of the vanishing of the cohomology of `𝒪(D)` from the closed fibre to the fibre over
a field containing `A`.** -/
theorem subsingleton_cohomology_of_residueField_of_injective [IsDomain A] [IsNoetherianRing A]
    [IsProper (X ↘ Spec (CommRingCat.of A))] [Flat (X ↘ Spec (CommRingCat.of A))]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hneX : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), Nonempty (TopCat.Presheaf.cechOpen U x))
    (DX : CartierDivisor X) (gX : Fin n → X.functionFieldˣ)
    (hgX : ∀ i, ∀ y ∈ U i, DX.IsLocalEquationAt y (gX i)) (uX : ∀ i j, Γ(X, U i ⊓ U j))
    (huX : ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (uX i j) * gX j = gX i)
    (𝔪 : Ideal A) [𝔪.IsMaximal]
    {Yk : Scheme.{u}} [IsIntegral Yk] [Yk.Over (Spec (CommRingCat.of 𝔪.ResidueField))]
    {gk : Yk ⟶ X}
    (Hk : IsPullback gk (Yk ↘ Spec (CommRingCat.of 𝔪.ResidueField)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
    [IsAffineHom gk] [IsAffineHom (pullback.diagonal (terminal.from Yk))]
    (hneYk : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gk ⁻¹ᵁ U i) x))
    (Dk : CartierDivisor Yk) (gYk : Fin n → Yk.functionFieldˣ)
    (hgYk : ∀ i, ∀ y ∈ gk ⁻¹ᵁ U i, Dk.IsLocalEquationAt y (gYk i))
    (huk : ∀ i j, ∀ (_ : Nonempty (gk ⁻¹ᵁ U i ⊓ gk ⁻¹ᵁ U j : Yk.Opens)),
      Yk.germToFunctionField (gk ⁻¹ᵁ U i ⊓ gk ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gYk j =
        gYk i)
    (hvan : ∀ j, 1 ≤ j → Subsingleton (Scheme.Modules.Cohomology Dk.sheaf j))
    (K : Type u) [Field K] [Algebra A K] (hK : Function.Injective (algebraMap A K))
    {YK : Scheme.{u}} [IsIntegral YK] [YK.Over (Spec (CommRingCat.of K))] {gK : YK ⟶ X}
    (HK : IsPullback gK (YK ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    [IsAffineHom gK] [IsAffineHom (pullback.diagonal (terminal.from YK))]
    (hneYK : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gK ⁻¹ᵁ U i) x))
    (DK : CartierDivisor YK) (gYK : Fin n → YK.functionFieldˣ)
    (hgYK : ∀ i, ∀ y ∈ gK ⁻¹ᵁ U i, DK.IsLocalEquationAt y (gYK i))
    (huK : ∀ i j, ∀ (_ : Nonempty (gK ⁻¹ᵁ U i ⊓ gK ⁻¹ᵁ U j : YK.Opens)),
      YK.germToFunctionField (gK ⁻¹ᵁ U i ⊓ gK ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gYK j =
        gYK i)
    {j : ℕ} (hj : 1 ≤ j) : Subsingleton (Scheme.Modules.Cohomology DK.sheaf j) := by
  let _ := localizationAtPrimeFieldAlgebra 𝔪 K hK
  have := localizationAtPrimeFieldAlgebra_isScalarTower 𝔪 K hK
  have := localizationAtPrimeFieldAlgebra_flat 𝔪 K hK
  exact subsingleton_cohomology_of_residueField U hU hcov hneX DX gX hgX uX huX 𝔪 Hk hneYk Dk gYk
    hgYk huk hvan K HK hneYK DK gYK hgYK huK hj

end MixedFujita
