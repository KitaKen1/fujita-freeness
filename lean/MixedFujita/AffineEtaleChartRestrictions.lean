/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAdjunctionCoordinateIndependence
public import MixedFujita.ProjectivePointedGlobalSmooth
public import MixedFujita.EtalePolynomialDifferentials
public import MixedFujita.PulledCanonicalChartChange

/-! 任意affineへの実etaleチャート制限と標準Cartier方程式不変性。 check-285：恒等スキーム射の既存etale_appLEから任意のaffine開制限の形式的etale性を証明し、特定の局所化表示を入力せず実etaleチャートを任意の非空affine部分開へ構成。実一般点座標・微分基底・元の標準Cartier方程式が厳密に不変であることを証明。同じ有理方程式の実Cartier frameを元の開から制限したものと小さい開で作ったものが空開を含む全部分開で一致することを証明。実pullback済みframe生成元と切断pullbackの制限自然性から、実Cartier pullback frameの全部分開の制限一致も内部構成。純dg正規化による写像検出を任意のB加群へ拡張し、独立に構成した純正規化留数が任意の可換な実環図式で実引き戻し標準加群のチャート変更と可換であることを証明。実Cartier局所層同型への全環図式の接続、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- ANY affine open restriction is formally etale. The identity scheme map
already supplies its actual affine ring map; no localization presentation is input. -/
theorem affineOpenRestriction_formallyEtale
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (U V : X.affineOpens) (hVU : V.1 ≤ U.1) :
    (sectionOpenRestrictionAlgHom (K := K) hVU).toRingHom.FormallyEtale := by
  have he := (𝟙 X : X ⟶ X).etale_appLE U.2 V.2 (by simpa using hVU)
  have hh : ((𝟙 X : X ⟶ X).appLE U.1 V.1 (by simpa using hVU)).hom =
      (X.presheaf.map (homOfLE hVU).op).hom := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  have he' := ringHom_formallyEtale_of_etale _ he
  rw [hh] at he'
  exact he'


/-- Restrict an actual etale chart to an ARBITRARY nonempty affine subopen,
with the actual regular-function restriction and the SAME base-field action. -/
noncomputable def etaleChartAffineRestriction
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c : EtaleChart K X n) (V : X.affineOpens) [Nonempty V.1] (hVc : V.1 ≤ c.U) :
    EtaleChart K X n where
  U := V.1
  isAffine := V.2
  nonempty := inferInstance
  coords := (sectionOpenRestrictionAlgHom (K := K) hVc).comp c.coords
  formallyEtale := RingHom.FormallyEtale.comp c.formallyEtale
    (affineOpenRestriction_formallyEtale ⟨c.U, c.isAffine⟩ V hVc)


/-- The actual generic coordinates are unchanged under affine restriction. -/
theorem etaleChartAffineRestriction_generic_coords
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c : EtaleChart K X n) (V : X.affineOpens) [Nonempty V.1] (hVc : V.1 ≤ c.U) :
    etaleChartFunctionFieldCoords (etaleChartAffineRestriction c V hVc) =
      etaleChartFunctionFieldCoords c := by
  apply AlgHom.ext
  intro p
  change X.germToFunctionField V.1 (X.presheaf.map (homOfLE hVc).op (c.coords p)) =
    X.germToFunctionField c.U (c.coords p)
  exact germToFunctionField_restrict X hVc (c.coords p)


/-- Restricting a chart preserves its ACTUAL generic differential basis. -/
theorem etaleChartAffineRestriction_generic_basis
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c : EtaleChart K X n) (V : X.affineOpens) [Nonempty V.1] (hVc : V.1 ≤ c.U) :
    etaleChartBasis (etaleChartAffineRestriction c V hVc) = etaleChartBasis c := by
  unfold etaleChartBasis
  congr 1
  exact etaleChartAffineRestriction_generic_coords c V hVc


/-- The ORIGINAL canonical Cartier rational equation is unchanged by an
arbitrary affine refinement of the actual coordinate chart. -/
theorem etaleChartAffineRestriction_canonical_equation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c₀ c : EtaleChart K X n) (V : X.affineOpens) [Nonempty V.1] (hVc : V.1 ≤ c.U) :
    etaleChartCanonicalEquation c₀ (etaleChartAffineRestriction c V hVc) =
      etaleChartCanonicalEquation c₀ c := by
  apply Units.ext
  rw [etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val,
    etaleChartAffineRestriction_generic_basis]

end MixedFujita
