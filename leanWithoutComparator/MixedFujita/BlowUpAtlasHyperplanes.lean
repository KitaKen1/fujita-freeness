/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RatioAtlasHyperplane
public import MixedFujita.BlowUpRatioAtlas

/-!
The hyperplane divisors of the ratio atlases of a base and of its blow-up (step 10, R1).

* A projective coordinate atlas `(U_i, u_{i,k})` of a base `X` is an atlas of ratios
  (`baseAtlasMap`); the hyperplane divisor `H₀` of the coordinate `x_{k₀}` has the local equation
  `u_{i,k₀}` on `U_i` (`baseAtlasHyperplane_isLocalEquationAt`).
* With generators `g_{i,l}` of the centre (`g_{i,l} = u_{i,k}^d g_{k,l}`), the ratios
  `π*(u_{i,k}) g_{i,l}/g_{i,j}` on the charts `V_{(i,j)}` of the blow-up form an atlas of ratios
  (`blowUpAtlasMap`, the embedding of `exists_closedImmersion_blowUp_of_atlas`); the hyperplane
  divisor `A` of the coordinate
  `(k₀, l₀)` has the local equation `π*(u_{i,k₀}) g_{i,l₀}/g_{i,j}` on `V_{(i,j)}`
  (`blowUpAtlasHyperplane_isLocalEquationAt`).
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

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
  (U : Fin n → X.affineOpens) (u : ∀ i, Fin n → Γ(X, U i))

theorem baseAtlas_iSup (hU : ⨆ i, (U i).1 = ⊤) :
    (⨆ β : ULift.{u} (Fin n), (U β.down).1) = ⊤ := by
  rw [← hU]
  apply le_antisymm
  · exact iSup_le fun β => le_iSup (fun i => (U i).1) β.down
  · exact iSup_le fun i => le_iSup (fun β : ULift.{u} (Fin n) => (U β.down).1) ⟨i⟩

theorem baseAtlas_cocycle
    (huc : ∀ i k k',
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))
    (β γ : ULift.{u} (Fin n)) (q : Fin n) :
    X.presheaf.map (homOfLE (inf_le_right : (U β.down).1 ⊓ (U γ.down).1 ≤ (U γ.down).1)).op
        (u γ.down q) =
      X.presheaf.map (homOfLE (inf_le_right : (U β.down).1 ⊓ (U γ.down).1 ≤ (U γ.down).1)).op
          (u γ.down β.down) *
        X.presheaf.map (homOfLE (inf_le_left : (U β.down).1 ⊓ (U γ.down).1 ≤ (U β.down).1)).op
          (u β.down q) := by
  have hsw : (U β.down).1 ⊓ (U γ.down).1 ≤ (U γ.down).1 ⊓ (U β.down).1 :=
    fun x hx => ⟨hx.2, hx.1⟩
  have h := congrArg (X.presheaf.map (homOfLE hsw).op) (huc γ.down β.down q)
  rw [map_mul] at h
  have e : ∀ {W : X.Opens} (a : (U β.down).1 ⊓ (U γ.down).1 ≤ W)
      (b : (U γ.down).1 ⊓ (U β.down).1 ≤ W) (s : Γ(X, W)),
      X.presheaf.map (homOfLE a).op s = X.presheaf.map (homOfLE hsw).op
        (X.presheaf.map (homOfLE b).op s) := by
    intro W a b s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← e, ← e, ← e] at h
  exact h

variable (hU : ⨆ i, (U i).1 = ⊤) (hu1 : ∀ i, u i i = 1)
  (huc : ∀ i k k',
    X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
        X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))

variable (K) in
/-- **The morphism of a projective coordinate atlas**, as an atlas of ratios. -/
noncomputable def baseAtlasMap : X ⟶ polynomialProjectiveScheme n K :=
  ratioAtlasMap K (fun β : ULift.{u} (Fin n) => β.down) (fun β => (U β.down).1)
    (baseAtlas_iSup U hU) (fun β => u β.down) (fun β => hu1 β.down) (baseAtlas_cocycle U u huc)

variable [IsIntegral X]

/-- **The hyperplane divisor of `x_{k₀}` of the base atlas has the local equation `u_{i,k₀}` on
`U_i`.** -/
theorem baseAtlasHyperplane_isLocalEquationAt
    (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1) (k₀ : Fin n)
    (hggen : MvPolynomial.X k₀ ∉
      ((baseAtlasMap K U u hU hu1 huc) (genericPoint X)).asHomogeneousIdeal)
    (i : Fin n) [Nonempty (U i).1] (hu : u i k₀ ≠ 0) (x : X) (hx : x ∈ (U i).1) :
    (projectiveHyperplaneCartier (baseAtlasMap K U u hU hu1 huc) (MvPolynomial.X k₀)
        (MvPolynomial.isHomogeneous_X K k₀) hggen).IsLocalEquationAt x
      (regularEquationRationalUnit X (U i).1 (u i k₀) hu) := by
  have : Nonempty ((fun β : ULift.{u} (Fin n) => (U β.down).1) ⟨i⟩) :=
    inferInstanceAs (Nonempty (U i).1)
  exact ratioAtlasMap_hyperplane_isLocalEquationAt (K := K) (fun β : ULift.{u} (Fin n) => β.down)
    (fun β => (U β.down).1) (baseAtlas_iSup U hU) (fun β => u β.down) (fun β => hu1 β.down)
    (baseAtlas_cocycle U u huc) (fun β γ => hub γ.down β.down) k₀ hggen ⟨i⟩ hu x hx

end Base

section BlowUp

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  (I : X.IdealSheafData) [IsIntegral (blowUp I)] [(blowUp I).Over (Spec (CommRingCat.of K))]
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

variable (K) in
/-- **The morphism of the ratio atlas of the blow-up** (the embedding of
`exists_closedImmersion_blowUp_of_atlas`). -/
noncomputable def blowUpAtlasMap : blowUp I ⟶ polynomialProjectiveScheme (n * m) K :=
  ratioAtlasMap K (fun β : ULift.{u} (Fin n × Fin m) => finProdFinEquiv β.down)
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

omit [X.Over (Spec (CommRingCat.of K))] in
/-- **The hyperplane divisor of the coordinate `(k₀, l₀)` of the blow-up atlas has the local
equation `π*(u_{i,k₀}) g_{i,l₀}/g_{i,j}` on the chart `V_{(i,j)}`.** -/
theorem blowUpAtlasHyperplane_isLocalEquationAt
    (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1) (k₀ : Fin n) (l₀ : Fin m)
    (hggen : MvPolynomial.X (finProdFinEquiv (k₀, l₀)) ∉
      ((blowUpAtlasMap K I U u g hU hu1 huc d hg hgc) (genericPoint (blowUp I))).asHomogeneousIdeal)
    (i : Fin n) (j : Fin m) [Nonempty (blowUpChartOpen I (U i) (g i j))]
    (hc : blowUpAtlasCoordinate I U u g i j k₀ l₀ ≠ 0) (y : blowUp I)
    (hy : y ∈ blowUpChartOpen I (U i) (g i j)) :
    (projectiveHyperplaneCartier (blowUpAtlasMap K I U u g hU hu1 huc d hg hgc)
        (MvPolynomial.X (finProdFinEquiv (k₀, l₀)))
        (MvPolynomial.isHomogeneous_X K (finProdFinEquiv (k₀, l₀))) hggen).IsLocalEquationAt y
      (regularEquationRationalUnit (blowUp I) (blowUpChartOpen I (U i) (g i j))
        (blowUpAtlasCoordinate I U u g i j k₀ l₀) hc) := by
  have : Nonempty ((fun β : ULift.{u} (Fin n × Fin m) =>
      blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2)) ⟨(i, j)⟩) :=
    inferInstanceAs (Nonempty (blowUpChartOpen I (U i) (g i j)))
  have hc' : (fun β q => blowUpAtlasCoordinate I U u g β.down.1 β.down.2
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
      (⟨(i, j)⟩ : ULift.{u} (Fin n × Fin m)) (finProdFinEquiv (k₀, l₀)) ≠ 0 := by
    simpa only [Equiv.symm_apply_apply] using hc
  have h := ratioAtlasMap_hyperplane_isLocalEquationAt (K := K)
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
    (finProdFinEquiv (k₀, l₀)) hggen ⟨(i, j)⟩ hc' y hy
  have heq : regularEquationRationalUnit (blowUp I) (blowUpChartOpen I (U i) (g i j))
      (blowUpAtlasCoordinate I U u g i j k₀ l₀) hc =
      regularEquationRationalUnit (blowUp I) ((fun β : ULift.{u} (Fin n × Fin m) =>
        blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2)) ⟨(i, j)⟩)
        ((fun β q => blowUpAtlasCoordinate I U u g β.down.1 β.down.2
          (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
          (⟨(i, j)⟩ : ULift.{u} (Fin n × Fin m)) (finProdFinEquiv (k₀, l₀))) hc' := by
    apply Units.ext
    simp only [regularEquationRationalUnit_val, Equiv.symm_apply_apply]
  rw [heq]
  exact h

end BlowUp

end MixedFujita
