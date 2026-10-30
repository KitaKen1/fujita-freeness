/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpAtlasHyperplanes
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.DominantCartierPullback
public import Hironaka.Scheme.BlowUp.Descent
public import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
Relative ampleness of a blow-up of a projective variety (step 10, R1).

Let `(U_i, u_{i,k})` be a projective coordinate atlas of `X`, `H₀` the hyperplane divisor of
`x_{k₀}` (check 471) and `g_{i,l}` generators of the centre `I` with `g_{i,l} = u_{i,k}^d g_{k,l}`.
On `U_i` the divisor `B := (d+1) H₀ + div g_{k₀,l₀}` has the local equation `u_{i,k₀} g_{i,l₀}`
(`baseAtlasDivisor_isLocalEquationAt`). On the chart `V_{(i,j)}` of the blow-up the hyperplane
divisor `A` of the coordinate `(k₀, l₀)` has the local equation `π*(u_{i,k₀}) g_{i,l₀}/g_{i,j}`,
so `G := π*B − A` has the local equation `π*g_{i,j}` (`blowUpExceptionalDivisor_isLocalEquationAt`):
`G` is effective and supported over the centre, and `π*((d+1) H₀) − G = A − π*(div g_{k₀,l₀})` is
very ample (`blowUp_pullback_sub_exceptional_isAmpleProj`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Base

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n m : ℕ} (U : Fin n → X.affineOpens) (u : ∀ i, Fin n → Γ(X, U i))
  (hU : ⨆ i, (U i).1 = ⊤) (hu1 : ∀ i, u i i = 1)
  (huc : ∀ i k k',
    X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
        X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))

omit [IsIntegral X] in
include hu1 huc in
/-- On the overlap with the chart of `x_{k₀}` the ratio `u_{i,k₀}` is a unit. -/
theorem baseAtlasRatio_restrict_isUnit (i k₀ : Fin n) :
    IsUnit (X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k₀).1 ≤ (U i).1)).op (u i k₀)) := by
  have h := huc i k₀ i
  rw [hu1, map_one] at h
  exact IsUnit.of_mul_eq_one _ h.symm

include hu1 huc in
theorem baseAtlasRatio_ne_zero (i k₀ : Fin n) [Nonempty (U i).1] [Nonempty (U k₀).1] :
    u i k₀ ≠ 0 := by
  have := integral_opens_inter_nonempty X (U i).1 (U k₀).1
  have hdom : IsDomain Γ(X, (U i).1 ⊓ (U k₀).1) := IsIntegral.component_integral _
  intro h
  have hu := baseAtlasRatio_restrict_isUnit U u hu1 huc i k₀
  rw [h, map_zero] at hu
  exact not_isUnit_zero hu

variable (I : X.IdealSheafData) (g : ∀ i, Fin m → I.ideal (U i)) (d : ℕ)
  (hgc : ∀ i k l,
    X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (g i l : Γ(X, U i)) =
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) ^ d *
        X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op
          (g k l : Γ(X, U k)))

include hgc in
/-- `g_{i,l₀} = u_{i,k₀}^d g_{k₀,l₀}` in the function field. -/
theorem baseAtlasGenerator_germ (i k₀ : Fin n) (l₀ : Fin m) [Nonempty (U i).1]
    [Nonempty (U k₀).1] :
    X.germToFunctionField (U i).1 (u i k₀) ^ d *
        X.germToFunctionField (U k₀).1 (g k₀ l₀ : Γ(X, U k₀)) =
      X.germToFunctionField (U i).1 (g i l₀ : Γ(X, U i)) := by
  have := integral_opens_inter_nonempty X (U i).1 (U k₀).1
  have h := congrArg (X.germToFunctionField ((U i).1 ⊓ (U k₀).1)) (hgc i k₀ l₀)
  rw [map_mul, map_pow, germToFunctionField_restrict X, germToFunctionField_restrict X,
    germToFunctionField_restrict X] at h
  exact h.symm

include hu1 huc hgc in
theorem baseAtlasGenerator_ne_zero (i k₀ : Fin n) (l₀ : Fin m) [Nonempty (U i).1]
    [Nonempty (U k₀).1] (hgl : (g k₀ l₀ : Γ(X, U k₀)) ≠ 0) : (g i l₀ : Γ(X, U i)) ≠ 0 := by
  intro h
  have hgerm := baseAtlasGenerator_germ U u I g d hgc i k₀ l₀
  rw [h, map_zero] at hgerm
  have hu : X.germToFunctionField (U i).1 (u i k₀) ≠ 0 := fun h' =>
    baseAtlasRatio_ne_zero U u hu1 huc i k₀
      (X.germToFunctionField_injective _ (h'.trans (map_zero _).symm))
  have hg0 := (mul_eq_zero.mp hgerm).resolve_left (pow_ne_zero d hu)
  exact hgl (X.germToFunctionField_injective _ (hg0.trans (map_zero _).symm))

variable (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1)

include hub in
/-- **The divisor `B = (d+1) H₀ + div g_{k₀,l₀}` has a local equation with value
`u_{i,k₀} g_{i,l₀}` on `U_i`.** -/
theorem baseAtlasDivisor_isLocalEquationAt (k₀ : Fin n) (l₀ : Fin m) [Nonempty (U k₀).1]
    (hgl : (g k₀ l₀ : Γ(X, U k₀)) ≠ 0)
    (hggen : MvPolynomial.X k₀ ∉
      ((baseAtlasMap K U u hU hu1 huc) (genericPoint X)).asHomogeneousIdeal)
    (i : Fin n) [Nonempty (U i).1] (x : X) (hx : x ∈ (U i).1) :
    ((d + 1) • projectiveHyperplaneCartier (baseAtlasMap K U u hU hu1 huc) (MvPolynomial.X k₀)
          (MvPolynomial.isHomogeneous_X K k₀) hggen +
        principalCartierDivisor X (regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl)).IsLocalEquationAt
      x (regularEquationRationalUnit X (U i).1 (u i k₀) (baseAtlasRatio_ne_zero U u hu1 huc i k₀) ^
          (d + 1) * regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl) :=
  (cartierLocalEquation_pow _ x _ (baseAtlasHyperplane_isLocalEquationAt U u hU hu1 huc hub k₀ hggen
    i (baseAtlasRatio_ne_zero U u hu1 huc i k₀) x hx) (d + 1)).mul
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor x _)

include hgc in
theorem baseAtlasDivisor_equation_val (k₀ : Fin n) (l₀ : Fin m) [Nonempty (U k₀).1]
    (hgl : (g k₀ l₀ : Γ(X, U k₀)) ≠ 0) (i : Fin n) [Nonempty (U i).1] (hu : u i k₀ ≠ 0) :
    ((regularEquationRationalUnit X (U i).1 (u i k₀) hu ^ (d + 1) *
        regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl : X.functionFieldˣ) : X.functionField) =
      X.germToFunctionField (U i).1 (u i k₀) * X.germToFunctionField (U i).1 (g i l₀ : Γ(X, U i)) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, regularEquationRationalUnit_val,
    regularEquationRationalUnit_val, ← baseAtlasGenerator_germ U u I g d hgc i k₀ l₀]
  ring

variable (K) in
/-- The divisor `B = (d+1) H₀ + div g_{k₀,l₀}` on the base. -/
noncomputable def baseAtlasDivisor (k₀ : Fin n) (l₀ : Fin m) [Nonempty (U k₀).1]
    (hgl : (g k₀ l₀ : Γ(X, U k₀)) ≠ 0)
    (hggen : MvPolynomial.X k₀ ∉
      ((baseAtlasMap K U u hU hu1 huc) (genericPoint X)).asHomogeneousIdeal) : CartierDivisor X :=
  (d + 1) • projectiveHyperplaneCartier (baseAtlasMap K U u hU hu1 huc) (MvPolynomial.X k₀)
      (MvPolynomial.isHomogeneous_X K k₀) hggen +
    principalCartierDivisor X (regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl)

end Base

section BlowUp

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  (I : X.IdealSheafData) [IsIntegral (blowUp I)] [(blowUp I).Over (Spec (CommRingCat.of K))]
  [IsDominant (blowUpπ I)]
  {n m : ℕ} (U : Fin n → X.affineOpens) (u : ∀ i, Fin n → Γ(X, U i))
  (g : ∀ i, Fin m → I.ideal (U i))
  (hU : ⨆ i, (U i).1 = ⊤) (hu1 : ∀ i, u i i = 1)
  (huc : ∀ i k k',
    X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
        X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))
  (d : ℕ)
  (hg : ∀ i, Ideal.span (Set.range fun l => (g i l : Γ(X, U i))) = I.ideal (U i))
  (hgc : ∀ i k l,
    X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (g i l : Γ(X, U i)) =
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) ^ d *
        X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op
          (g k l : Γ(X, U k)))
  (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1)
  (k₀ : Fin n) (l₀ : Fin m) [Nonempty (U k₀).1] (hgl : (g k₀ l₀ : Γ(X, U k₀)) ≠ 0)
  (hggen : MvPolynomial.X k₀ ∉
    ((baseAtlasMap K U u hU hu1 huc) (genericPoint X)).asHomogeneousIdeal)
  (hggenB : MvPolynomial.X (finProdFinEquiv (k₀, l₀)) ∉
    ((blowUpAtlasMap K I U u g hU hu1 huc d hg hgc) (genericPoint (blowUp I))).asHomogeneousIdeal)

variable (K) in
/-- **The exceptional divisor of the atlas**: `G = π*B − A`. -/
noncomputable def blowUpAtlasExceptional : CartierDivisor (blowUp I) :=
  cartierPullback (blowUpπ I) (baseAtlasDivisor K U u hU hu1 huc I g d k₀ l₀ hgl hggen) -
    projectiveHyperplaneCartier (blowUpAtlasMap K I U u g hU hu1 huc d hg hgc)
      (MvPolynomial.X (finProdFinEquiv (k₀, l₀)))
      (MvPolynomial.isHomogeneous_X K (finProdFinEquiv (k₀, l₀))) hggenB

omit [IsIntegral X] [IsDominant (blowUpπ I)] in
/-- The pulled back generator of a nonempty chart is nonzero. -/
theorem blowUpChartGenerator_ne_zero (i : Fin n) (j : Fin m)
    [Nonempty (blowUpChartOpen I (U i) (g i j))] :
    (blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
      (blowUpChartOpen_le_preimage I (U i) (g i j)) (g i j : Γ(X, U i)) ≠ 0 := by
  have : IsDomain Γ(blowUp I, blowUpChartOpen I (U i) (g i j)) := IsIntegral.component_integral _
  exact blowUpπ_appLE_chart_ne_zero I (U i) (g i j)

include hub in
/-- **The exceptional divisor of the atlas has the local equation `π*g_{i,j}` on the chart
`V_{(i,j)}`.** -/
theorem blowUpAtlasExceptional_isLocalEquationAt (i : Fin n) (j : Fin m)
    [Nonempty (blowUpChartOpen I (U i) (g i j))] (y : blowUp I)
    (hy : y ∈ blowUpChartOpen I (U i) (g i j)) :
    (blowUpAtlasExceptional K I U u g hU hu1 huc d hg hgc k₀ l₀ hgl hggen hggenB).IsLocalEquationAt y
      (regularEquationRationalUnit (blowUp I) (blowUpChartOpen I (U i) (g i j))
        ((blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
          (blowUpChartOpen_le_preimage I (U i) (g i j)) (g i j : Γ(X, U i)))
        (blowUpChartGenerator_ne_zero I U g i j)) := by
  set V := blowUpChartOpen I (U i) (g i j) with hV
  have hle : V ≤ blowUpπ I ⁻¹ᵁ (U i).1 := blowUpChartOpen_le_preimage I (U i) (g i j)
  have hπy : blowUpπ I y ∈ (U i).1 := hle hy
  have : Nonempty (U i).1 := ⟨⟨_, hπy⟩⟩
  have hu := baseAtlasRatio_ne_zero U u hu1 huc i k₀
  have hgi := baseAtlasGenerator_ne_zero U u hu1 huc I g d hgc i k₀ l₀ hgl
  -- germs on the chart of pulled back functions
  have hφ : ∀ s : Γ(X, U i), (dominantFunctionFieldMap (blowUpπ I)).hom (X.germToFunctionField (U i).1 s) =
      (blowUp I).germToFunctionField V ((blowUpπ I).appLE (U i).1 V hle s) :=
    fun s => dominantFunctionFieldMap_germ (blowUpπ I) (U i).1 V hle s
  let frac := blowUpChartSection I (U i) (g i j)
    (affineBlowUpAlgebra.frac (a := ((g i j : I.ideal (U i)) : Γ(X, U i))) (g i l₀).2)
  have hrel : (blowUp I).germToFunctionField V frac *
      (blowUp I).germToFunctionField V ((blowUpπ I).appLE (U i).1 V hle (g i j : Γ(X, U i))) =
      (blowUp I).germToFunctionField V ((blowUpπ I).appLE (U i).1 V hle (g i l₀ : Γ(X, U i))) := by
    rw [← map_mul]
    exact congrArg _ (blowUpChartSection_frac_mul I (U i) (g i j) (g i l₀))
  have hgerm_ne : ∀ s : Γ(X, U i), s ≠ 0 →
      (blowUp I).germToFunctionField V ((blowUpπ I).appLE (U i).1 V hle s) ≠ 0 := by
    intro s hs
    rw [← hφ]
    exact (map_ne_zero _).mpr fun h => hs (X.germToFunctionField_injective _ (h.trans (map_zero _).symm))
  have hfrac_ne : (blowUp I).germToFunctionField V frac ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hgerm_ne _ hgi hrel.symm
  have hcval : (blowUp I).germToFunctionField V (blowUpAtlasCoordinate I U u g i j k₀ l₀) =
      (blowUp I).germToFunctionField V ((blowUpπ I).appLE (U i).1 V hle (u i k₀)) *
        (blowUp I).germToFunctionField V frac := by
    rw [blowUpAtlasCoordinate, map_mul]
  have hc : blowUpAtlasCoordinate I U u g i j k₀ l₀ ≠ 0 := by
    intro h
    have h' := congrArg ((blowUp I).germToFunctionField V) h
    rw [hcval, map_zero] at h'
    exact mul_ne_zero (hgerm_ne _ hu) hfrac_ne h'
  have hB := baseAtlasDivisor_isLocalEquationAt U u hU hu1 huc I g d hub k₀ l₀ hgl hggen i
    (blowUpπ I y) hπy
  have hPB := cartierPullback_isLocalEquationAt (blowUpπ I) _ y hB
  have hA := blowUpAtlasHyperplane_isLocalEquationAt I U u g hU hu1 huc d hg hgc hub k₀ l₀ hggenB
    i j hc y hy
  have hG := hPB.mul hA.inv
  unfold blowUpAtlasExceptional
  rw [sub_eq_add_neg]
  convert hG using 1
  · rfl
  apply Units.ext
  rw [Units.val_mul, Units.coe_map, Units.val_inv_eq_inv_val, regularEquationRationalUnit_val,
    regularEquationRationalUnit_val]
  change _ = (dominantFunctionFieldMap (blowUpπ I)).hom
    ((regularEquationRationalUnit X (U i).1 (u i k₀) hu ^ (d + 1) *
      regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl : X.functionFieldˣ) : X.functionField) * _
  rw [baseAtlasDivisor_equation_val U u I g d hgc k₀ l₀ hgl i hu, map_mul, hφ, hφ, hcval, ← hrel]
  have hu' := hgerm_ne _ hu
  field_simp
  rfl

include hub in
/-- **The exceptional divisor of the atlas is effective.** -/
theorem blowUpAtlasExceptional_isEffective :
    (blowUpAtlasExceptional K I U u g hU hu1 huc d hg hgc k₀ l₀ hgl hggen hggenB).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro y
  have hy : y ∈ ⨆ β : ULift.{u} (Fin n × Fin m),
      blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2) := by
    rw [iSup_blowUpChartOpen_eq_top I U g hU hg]
    trivial
  obtain ⟨β, hβ⟩ := Opens.mem_iSup.mp hy
  have : Nonempty (blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2)) := ⟨⟨y, hβ⟩⟩
  exact ⟨_, blowUpAtlasExceptional_isLocalEquationAt I U u g hU hu1 huc d hg hgc hub k₀ l₀ hgl hggen
    hggenB β.down.1 β.down.2 y hβ, regularEquationRationalUnit_mem_stalk_range (blowUp I) _ _ _ y hβ⟩

include hub in
/-- **The exceptional divisor of the atlas is supported over the centre**: its coefficient
vanishes at the points not lying over the support of `I`. -/
theorem blowUpAtlasExceptional_coefficient_eq_zero [IsLocallyNoetherian (blowUp I)] (t : blowUp I)
    (ht : blowUpπ I t ∉ I.support) :
    cartierCoefficient (blowUpAtlasExceptional K I U u g hU hu1 huc d hg hgc k₀ l₀ hgl hggen hggenB)
      t = 0 := by
  have hy : t ∈ ⨆ β : ULift.{u} (Fin n × Fin m),
      blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2) := by
    rw [iSup_blowUpChartOpen_eq_top I U g hU hg]
    trivial
  obtain ⟨β, hβ⟩ := Opens.mem_iSup.mp hy
  have : Nonempty (blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2)) := ⟨⟨t, hβ⟩⟩
  have hle := blowUpChartOpen_le_preimage I (U β.down.1) (g β.down.1 β.down.2)
  have hπt : blowUpπ I t ∈ (U β.down.1).1 := hle hβ
  rw [cartierCoefficient_eq_ord (blowUpAtlasExceptional_isLocalEquationAt I U u g hU hu1 huc d hg
    hgc hub k₀ l₀ hgl hggen hggenB β.down.1 β.down.2 t hβ), regularEquationRationalUnit_val]
  apply ord_germToFunctionField_eq_zero_of_mem_basicOpen
  have hchart := (blowUp.mem_range_chart_iff I (U β.down.1) (g β.down.1 β.down.2) t hπt).mp hβ
  have htop : I.exceptionalDivisor.stalkIdeal t = ⊤ := by
    rw [Scheme.IdealSheafData.exceptionalDivisor, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support I ht, Ideal.map_top]
  rw [htop, eq_comm, Ideal.span_singleton_eq_top] at hchart
  apply ((blowUp I).mem_basicOpen _ t hβ).mpr
  have hg : (blowUp I).presheaf.germ _ t hβ ((blowUpπ I).appLE (U β.down.1).1
      (blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2)) hle
        (g β.down.1 β.down.2 : Γ(X, U β.down.1))) =
      (blowUpπ I).stalkMap t (X.presheaf.germ (U β.down.1).1 (blowUpπ I t) hπt
        (g β.down.1 β.down.2 : Γ(X, U β.down.1))) := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  rw [hg]
  exact hchart

include hub in
/-- **Relative ampleness of the blow-up**: `π*((d+1) H₀) − G` is very ample. -/
theorem blowUp_pullback_sub_exceptional_isVeryAmpleProj [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsLocallyNoetherian X] [(blowUpπ I).IsOver (Spec (CommRingCat.of K))]
    (hugen : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top : (U i).1 ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (u i))) :
    CartierIsVeryAmpleProj K (cartierPullback (blowUpπ I)
        ((d + 1) • projectiveHyperplaneCartier (baseAtlasMap K U u hU hu1 huc) (MvPolynomial.X k₀)
          (MvPolynomial.isHomogeneous_X K k₀) hggen) -
      blowUpAtlasExceptional K I U u g hU hu1 huc d hg hgc k₀ l₀ hgl hggen hggenB) := by
  have heq : cartierPullback (blowUpπ I)
        ((d + 1) • projectiveHyperplaneCartier (baseAtlasMap K U u hU hu1 huc) (MvPolynomial.X k₀)
          (MvPolynomial.isHomogeneous_X K k₀) hggen) -
      blowUpAtlasExceptional K I U u g hU hu1 huc d hg hgc k₀ l₀ hgl hggen hggenB =
      projectiveHyperplaneCartier (blowUpAtlasMap K I U u g hU hu1 huc d hg hgc)
          (MvPolynomial.X (finProdFinEquiv (k₀, l₀)))
          (MvPolynomial.isHomogeneous_X K (finProdFinEquiv (k₀, l₀))) hggenB +
        principalCartierDivisor (blowUp I) (Units.map (dominantFunctionFieldMap (blowUpπ I)).hom.toMonoidHom
          (regularEquationRationalUnit X (U k₀).1 (g k₀ l₀) hgl))⁻¹ := by
    unfold blowUpAtlasExceptional baseAtlasDivisor
    rw [cartierPullback_add, cartierPullback_principal, principalCartierDivisor_inv]
    abel
  rw [heq]
  have hπ : IsProper (blowUpπ I) := blowUp.isProper_π I
  have hprop : IsProper ((blowUp I) ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := blowUpπ I) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hscal : schemeBaseScalars K (blowUp I) =
      (blowUpπ I).appTop.hom.comp (schemeBaseScalars K X) := by
    unfold schemeBaseScalars
    rw [← HomIsOver.comp_over (f := blowUpπ I) (S := Spec (CommRingCat.of K)),
      Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]
  have hci : IsClosedImmersion (blowUpAtlasMap K I U u g hU hu1 huc d hg hgc) :=
    ratioAtlasMap_isClosedImmersion (K := K)
      (fun β : ULift.{u} (Fin n × Fin m) => finProdFinEquiv β.down)
      (fun β => blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2))
      (iSup_blowUpChartOpen_eq_top I U g hU hg)
      (fun β q => blowUpAtlasCoordinate I U u g β.down.1 β.down.2
        (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
      (fun β => by
        simp only [Equiv.symm_apply_apply]
        exact blowUpAtlasCoordinate_self I U u g hu1 β.down.1 β.down.2)
      (fun β γ q => by
        simp only [Equiv.symm_apply_apply]
        exact blowUpAtlasCoordinate_cocycle I U u g d huc hgc β.down.1 β.down.2
          γ.down.1 γ.down.2 _ _)
      (fun β γ => by
        simp only [Equiv.symm_apply_apply]
        exact blowUpAtlasCoordinate_basicOpen_le I U u g d hub hgc β.down.1 β.down.2
          γ.down.1 γ.down.2)
      (fun β => isAffineOpen_blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2))
      (fun β => by
        rw [hscal]
        exact blowUpAtlasCoordinate_generate I U u g hu1 hg hugen β.down.1 β.down.2)
  exact ⟨n * m, blowUpAtlasMap K I U u g hU hu1 huc d hg hgc, hci,
    ratioAtlasMap_over _ _ _ _ _ _, MvPolynomial.X (finProdFinEquiv (k₀, l₀)),
    MvPolynomial.isHomogeneous_X K _, hggenB, _, rfl⟩

end BlowUp

end MixedFujita
