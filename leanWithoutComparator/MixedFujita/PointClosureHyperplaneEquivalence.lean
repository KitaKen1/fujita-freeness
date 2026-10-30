/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureTaylor
public import MixedFujita.ProjectiveHyperplaneSections
public import MixedFujita.DominantCartierPullback

/-!
Linear equivalences of hyperplane classes restrict to the closure of a point (step 4). Let W be
the closure of a point η of an integral scheme X, with its closed immersion ι, and let e, e' be
morphisms of X to polynomial projective spaces with degree-one forms g, g' that do not vanish at
the generic point of W. If k' J ∼ k J' on X for the hyperplane divisors J, J' of (e, g) and
(e', g'), then k' J_W ∼ k J'_W on W for the hyperplane divisors of (ι ≫ e, g) and (ι ≫ e', g').

The divisor k' J - k J' is principal on X, but its rational function need not be regular along W.
At a point ι(y) the two local equations (g/X_j)^k' and (g'/X_j')^k · f of k' J differ by a unit
u_y of the local ring of X; a germ at ι(y) restricts to a rational function on W through the
stalk map of ι, and this restriction is compatible with specialization inside W. Comparing the
units at y and at the generic point ξ of W inside the local ring of X at ι(ξ), where all four
chart equations are regular, gives one rational function f_W on W with
(g/X_j)^k' = u_y|_W · (g'/X_j')^k · f_W at every y. A unit of the local ring times a local
equation is a local equation, so the two divisors on W have a common local equation at every
point. No pullback of general Cartier divisors along ι is constructed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section StalkUnit

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- A unit of the local ring times a local equation is a local equation. -/
theorem isLocalEquationAt_stalkUnit_mul {D : CartierDivisor Y} {t : Y} {g h : Y.functionFieldˣ}
    (hg : D.IsLocalEquationAt t g) (u : (Y.presheaf.stalk t)ˣ)
    (hh : (h : Y.functionField) = algebraMap (Y.presheaf.stalk t) Y.functionField u * g) :
    D.IsLocalEquationAt t h := by
  obtain ⟨U, htU, a, ha⟩ := Y.presheaf.exists_germ_eq (u : Y.presheaf.stalk t)
  obtain ⟨V, i, htV, hV⟩ := RingedSpace.isUnit_res_of_isUnit_germ Y.toRingedSpace U a t htU
    (by rw [ha]; exact u.isUnit)
  have : Nonempty V := ⟨⟨t, htV⟩⟩
  have hres := isLocalEquationAt_regularUnit_mul hg V htV hV.unit
  have heq : h = regularUnitToFunctionField Y V hV.unit * g := by
    apply Units.ext
    rw [hh, Units.val_mul, regularUnitToFunctionField_apply, Units.coe_map, IsUnit.unit_spec]
    congr 1
    rw [← ha, ← Y.presheaf.germ_res_apply i t htV a]
    exact Y.algebraMap_germ_eq_germToFunctionField htV _
  rw [heq]
  exact hres

end StalkUnit

section Restriction

variable {X : Scheme.{u}} [IsIntegral X] {η : X}

/-- Germs at ι(y) restricted to rational functions on the closure of η. -/
noncomputable def pointClosureStalkToFunctionField (y : pointClosureScheme η) :
    X.presheaf.stalk (pointClosureι η y) →+* (pointClosureScheme η).functionField :=
  (algebraMap ((pointClosureScheme η).presheaf.stalk y) (pointClosureScheme η).functionField).comp
    ((pointClosureι η).stalkMap y).hom

omit [IsIntegral X] in
theorem pointClosureStalkToFunctionField_apply (y : pointClosureScheme η)
    (c : X.presheaf.stalk (pointClosureι η y)) :
    pointClosureStalkToFunctionField y c =
      algebraMap ((pointClosureScheme η).presheaf.stalk y) (pointClosureScheme η).functionField
        ((pointClosureι η).stalkMap y c) := rfl

omit [IsIntegral X] in
/-- The restriction is compatible with specialization inside the closure. -/
theorem pointClosureStalkToFunctionField_specializes {y y' : pointClosureScheme η} (h : y' ⤳ y)
    (c : X.presheaf.stalk (pointClosureι η y)) :
    pointClosureStalkToFunctionField y'
        (X.presheaf.stalkSpecializes ((pointClosureι η).base.hom.map_specializes h) c) =
      pointClosureStalkToFunctionField y c := by
  rw [pointClosureStalkToFunctionField_apply, pointClosureStalkToFunctionField_apply,
    Scheme.Hom.stalkSpecializes_stalkMap_apply (pointClosureι η) y' y h,
    stalkSpecializes_algebraMap_functionField h]

variable {R : Type u} [CommRing R] {n : ℕ} (e : X ⟶ polynomialProjectiveScheme n R)

omit [IsIntegral X] in
theorem pointClosureι_mem_projectiveCoordinateOpen {y : pointClosureScheme η} {k : Fin n}
    (h : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k) :
    pointClosureι η y ∈ projectivePullbackCoordinateOpen e k := by
  rw [projectivePullbackCoordinateOpen, Scheme.Hom.comp_preimage] at h
  rw [projectivePullbackCoordinateOpen]
  exact (Scheme.Hom.mem_preimage _).mp h

variable (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)

/-- The chart equation of g on X at ι(y) is the image of its germ. -/
theorem projectiveHyperplaneUnit_eq_algebraMap_germ
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (x : X)
    (hx : x ∈ projectivePullbackCoordinateOpen e j.val) :
    (projectiveHyperplaneUnit e g hg hggen j : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ (projectivePullbackCoordinateOpen e j.val) x hx
          (projectivePullbackHomogeneousEquation e j.val 1 g hg)) :=
  (X.algebraMap_germ_eq_germToFunctionField hx _).symm

omit [IsIntegral X] in
/-- The chart equation of g on the closure of η is the restriction of its germ on X. -/
theorem pointClosureStalkToFunctionField_hyperplaneEquation (y : pointClosureScheme η)
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)})
    (hy : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j.val) :
    pointClosureStalkToFunctionField y
        (X.presheaf.germ (projectivePullbackCoordinateOpen e j.val) (pointClosureι η y)
          (pointClosureι_mem_projectiveCoordinateOpen e hy)
          (projectivePullbackHomogeneousEquation e j.val 1 g hg)) =
      (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW j :
        (pointClosureScheme η).functionField) := by
  rw [pointClosureStalkToFunctionField_apply, Scheme.Hom.germ_stalkMap_apply]
  exact (pointClosureScheme η).algebraMap_germ_eq_germToFunctionField hy
    (projectivePullbackHomogeneousEquation (pointClosureι η ≫ e) j.val 1 g hg)

end Restriction

section Transfer

variable {X : Scheme.{u}} [IsIntegral X] {η : X} {R : Type u} [CommRing R] {n n' : ℕ}
  (e : X ⟶ polynomialProjectiveScheme n R) (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
  (e' : X ⟶ polynomialProjectiveScheme n' R) (g' : MvPolynomial (Fin n') R)
  (hg' : g'.IsHomogeneous 1) (hggen' : g' ∉ (e' (genericPoint X)).asHomogeneousIdeal)
  (hgW' : g' ∉
    ((pointClosureι η ≫ e') (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)

/-- The chart of e at ι(y) given by a chart of ι ≫ e at y. -/
def pointClosureAmbientChart {y : pointClosureScheme η} {k : Fin n}
    (h : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k) :
    {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
  ⟨k, ⟨⟨pointClosureι η y, pointClosureι_mem_projectiveCoordinateOpen e h⟩⟩⟩

/-- Comparison of the unit factors at a point y and at a generization y₀ of it. -/
theorem pointClosure_hyperplane_unit_cross {k k' : ℕ} (f : X.functionFieldˣ)
    {y y₀ : pointClosureScheme η} (hsp : y₀ ⤳ y)
    (j j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)})
    (j' j₀' :
      {k : Fin n' // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e') k)})
    (hy : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j.val)
    (hy' : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e') j'.val)
    (hy₀ : y₀ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j₀.val)
    (hy₀' : y₀ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e') j₀'.val)
    (u : (X.presheaf.stalk (pointClosureι η y))ˣ)
    (u₀ : (X.presheaf.stalk (pointClosureι η y₀))ˣ)
    (hu : algebraMap (X.presheaf.stalk (pointClosureι η y)) X.functionField u *
        ((projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' hy') :
          X.functionField) ^ k * f) =
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hy) :
        X.functionField) ^ k')
    (hu₀ : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField u₀ *
        ((projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' hy₀') :
          X.functionField) ^ k * f) =
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hy₀) :
        X.functionField) ^ k') :
    (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW j :
          (pointClosureScheme η).functionField) ^ k' *
        pointClosureStalkToFunctionField y₀ u₀ *
        (projectiveHyperplaneUnit (pointClosureι η ≫ e') g' hg' hgW' j₀' :
          (pointClosureScheme η).functionField) ^ k =
      (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW j₀ :
          (pointClosureScheme η).functionField) ^ k' *
        pointClosureStalkToFunctionField y u *
        (projectiveHyperplaneUnit (pointClosureι η ≫ e') g' hg' hgW' j' :
          (pointClosureScheme η).functionField) ^ k := by
  have hyg : y₀ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j.val :=
    hsp.mem_open (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j.val).isOpen hy
  have hyg' : y₀ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e') j'.val :=
    hsp.mem_open (projectivePullbackCoordinateOpen (pointClosureι η ≫ e') j'.val).isOpen hy'
  have hspX : pointClosureι η y₀ ⤳ pointClosureι η y :=
    (pointClosureι η).base.hom.map_specializes hsp
  -- the four chart equations as germs at ι(y₀)
  set α := X.presheaf.germ (projectivePullbackCoordinateOpen e j.val) (pointClosureι η y₀)
    (pointClosureι_mem_projectiveCoordinateOpen e hyg)
    (projectivePullbackHomogeneousEquation e j.val 1 g hg) with hα
  set α₀ := X.presheaf.germ (projectivePullbackCoordinateOpen e j₀.val) (pointClosureι η y₀)
    (pointClosureι_mem_projectiveCoordinateOpen e hy₀)
    (projectivePullbackHomogeneousEquation e j₀.val 1 g hg) with hα₀
  set β := X.presheaf.germ (projectivePullbackCoordinateOpen e' j'.val) (pointClosureι η y₀)
    (pointClosureι_mem_projectiveCoordinateOpen e' hyg')
    (projectivePullbackHomogeneousEquation e' j'.val 1 g' hg') with hβ
  set β₀ := X.presheaf.germ (projectivePullbackCoordinateOpen e' j₀'.val) (pointClosureι η y₀)
    (pointClosureι_mem_projectiveCoordinateOpen e' hy₀')
    (projectivePullbackHomogeneousEquation e' j₀'.val 1 g' hg') with hβ₀
  have hAα : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField α =
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hy) : X.functionField) :=
    (projectiveHyperplaneUnit_eq_algebraMap_germ e g hg hggen (pointClosureAmbientChart e hy)
      (pointClosureι η y₀) (pointClosureι_mem_projectiveCoordinateOpen e hyg)).symm
  have hAα₀ : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField α₀ =
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hy₀) :
        X.functionField) :=
    (projectiveHyperplaneUnit_eq_algebraMap_germ e g hg hggen (pointClosureAmbientChart e hy₀)
      (pointClosureι η y₀) (pointClosureι_mem_projectiveCoordinateOpen e hy₀)).symm
  have hAβ : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField β =
      (projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' hy') :
        X.functionField) :=
    (projectiveHyperplaneUnit_eq_algebraMap_germ e' g' hg' hggen'
      (pointClosureAmbientChart e' hy') (pointClosureι η y₀)
      (pointClosureι_mem_projectiveCoordinateOpen e' hyg')).symm
  have hAβ₀ : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField β₀ =
      (projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' hy₀') :
        X.functionField) :=
    (projectiveHyperplaneUnit_eq_algebraMap_germ e' g' hg' hggen'
      (pointClosureAmbientChart e' hy₀') (pointClosureι η y₀)
      (pointClosureι_mem_projectiveCoordinateOpen e' hy₀')).symm
  have hAs : algebraMap (X.presheaf.stalk (pointClosureι η y₀)) X.functionField
      (X.presheaf.stalkSpecializes hspX (u : X.presheaf.stalk (pointClosureι η y))) =
        algebraMap (X.presheaf.stalk (pointClosureι η y)) X.functionField u :=
    stalkSpecializes_algebraMap_functionField hspX _
  -- the identity in the local ring at ι(y₀)
  have hlocal : α ^ k' * (u₀ : X.presheaf.stalk (pointClosureι η y₀)) * β₀ ^ k =
      α₀ ^ k' * X.presheaf.stalkSpecializes hspX (u : X.presheaf.stalk (pointClosureι η y)) *
        β ^ k := by
    apply IsFractionRing.injective (X.presheaf.stalk (pointClosureι η y₀)) X.functionField
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hAα, hAα₀, hAβ,
      hAβ₀, hAs, ← hu, ← hu₀]
    ring
  have hmap := congrArg (pointClosureStalkToFunctionField y₀) hlocal
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    pointClosureStalkToFunctionField_specializes hsp] at hmap
  rw [hα, hα₀, hβ, hβ₀,
    pointClosureStalkToFunctionField_hyperplaneEquation e g hg hgW y₀ j hyg,
    pointClosureStalkToFunctionField_hyperplaneEquation e g hg hgW y₀ j₀ hy₀,
    pointClosureStalkToFunctionField_hyperplaneEquation e' g' hg' hgW' y₀ j' hyg',
    pointClosureStalkToFunctionField_hyperplaneEquation e' g' hg' hgW' y₀ j₀' hy₀'] at hmap
  exact hmap

/-- A linear equivalence k' J ∼ k J' of hyperplane divisors on X restricts to the closure of a
point at whose generic point the forms g, g' do not vanish. -/
theorem pointClosure_hyperplane_nsmul_eq_add_principal {k k' : ℕ} (f : X.functionFieldˣ)
    (hrel : k' • projectiveHyperplaneCartier e g hg hggen =
      k • projectiveHyperplaneCartier e' g' hg' hggen' + principalCartierDivisor X f) :
    ∃ fW : (pointClosureScheme η).functionFieldˣ,
      k' • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW =
        k • projectiveHyperplaneCartier (pointClosureι η ≫ e') g' hg' hgW' +
          principalCartierDivisor (pointClosureScheme η) fW := by
  -- charts at every point of the closure
  have hchart : ∀ y : pointClosureScheme η, ∃ j : Fin n,
      y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) j := fun y =>
    polynomialProjective_exists_coordinate_chart n R ((pointClosureι η ≫ e) y)
  have hchart' : ∀ y : pointClosureScheme η, ∃ j : Fin n',
      y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e') j := fun y =>
    polynomialProjective_exists_coordinate_chart n' R ((pointClosureι η ≫ e') y)
  choose c hc using hchart
  choose c' hc' using hchart'
  let J : ∀ y : pointClosureScheme η,
      {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)} :=
    fun y => ⟨c y, ⟨⟨y, hc y⟩⟩⟩
  let J' : ∀ y : pointClosureScheme η,
      {k : Fin n' // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e') k)} :=
    fun y => ⟨c' y, ⟨⟨y, hc' y⟩⟩⟩
  -- the unit factor at every point, from the equivalence on X
  have hunit : ∀ y : pointClosureScheme η, ∃ u : (X.presheaf.stalk (pointClosureι η y))ˣ,
      algebraMap (X.presheaf.stalk (pointClosureι η y)) X.functionField u *
        ((projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' (hc' y)) :
          X.functionField) ^ k * f) =
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e (hc y)) :
        X.functionField) ^ k' := by
    intro y
    have h1 : (k' • projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt
        (pointClosureι η y)
        (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e (hc y)) ^ k') :=
      cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt e g hg hggen
        (pointClosureAmbientChart e (hc y)) (pointClosureι η y)
        (pointClosureι_mem_projectiveCoordinateOpen e (hc y))) k'
    have h2 : (k' • projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt
        (pointClosureι η y)
        (projectiveHyperplaneUnit e' g' hg' hggen' (pointClosureAmbientChart e' (hc' y)) ^ k *
          f) := by
      rw [hrel]
      exact (cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt e' g' hg'
        hggen' (pointClosureAmbientChart e' (hc' y)) (pointClosureι η y)
        (pointClosureι_mem_projectiveCoordinateOpen e' (hc' y))) k).mul
          (CartierDivisor.isLocalEquationAt_principalCartierDivisor _ f)
    obtain ⟨u, hu⟩ := h1.exists_unit_mul_eq h2
    refine ⟨u, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    exact hu
  choose u hu using hunit
  set ξ := genericPoint (pointClosureScheme η) with hξ
  -- the rational function on the closure
  let t₀ : (pointClosureScheme η).functionFieldˣ :=
    Units.map (pointClosureStalkToFunctionField ξ).toMonoidHom (u ξ)
  let fW : (pointClosureScheme η).functionFieldˣ :=
    projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW (J ξ) ^ k' *
      (t₀ * projectiveHyperplaneUnit (pointClosureι η ≫ e') g' hg' hgW' (J' ξ) ^ k)⁻¹
  refine ⟨fW, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro y
  have hcross := pointClosure_hyperplane_unit_cross e g hg hggen hgW e' g' hg' hggen' hgW' f
    (genericPoint_specializes y) (J y) (J ξ) (J' y) (J' ξ) (hc y) (hc' y) (hc ξ) (hc' ξ)
    (u y) (u ξ) (hu y) (hu ξ)
  have hL : (k' • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).IsLocalEquationAt y
      (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW (J y) ^ k') :=
    cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt
      (pointClosureι η ≫ e) g hg hgW (J y) y (hc y)) k'
  have hRraw : (k • projectiveHyperplaneCartier (pointClosureι η ≫ e') g' hg' hgW' +
      principalCartierDivisor (pointClosureScheme η) fW).IsLocalEquationAt y
      (projectiveHyperplaneUnit (pointClosureι η ≫ e') g' hg' hgW' (J' y) ^ k * fW) :=
    (cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt
      (pointClosureι η ≫ e') g' hg' hgW' (J' y) y (hc' y)) k).mul
        (CartierDivisor.isLocalEquationAt_principalCartierDivisor _ fW)
  refine ⟨projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW (J y) ^ k', hL, ?_⟩
  refine isLocalEquationAt_stalkUnit_mul hRraw
    (Units.map ((pointClosureι η).stalkMap y).hom.toMonoidHom (u y)) ?_
  -- v^k' = (u_y restricted) * (v'^k * fW)
  have ht₀ : (t₀ : (pointClosureScheme η).functionField) =
      pointClosureStalkToFunctionField ξ (u ξ) := rfl
  have hty : algebraMap ((pointClosureScheme η).presheaf.stalk y)
      (pointClosureScheme η).functionField
        ((Units.map ((pointClosureι η).stalkMap y).hom.toMonoidHom (u y) :
          ((pointClosureScheme η).presheaf.stalk y)ˣ) :
            (pointClosureScheme η).presheaf.stalk y) =
      pointClosureStalkToFunctionField y (u y) := rfl
  rw [hty]
  have hne₀ : (t₀ : (pointClosureScheme η).functionField) ≠ 0 := t₀.ne_zero
  have hneB : ((projectiveHyperplaneUnit (pointClosureι η ≫ e') g' hg' hgW' (J' ξ) :
      (pointClosureScheme η).functionFieldˣ) : (pointClosureScheme η).functionField) ^ k ≠ 0 :=
    pow_ne_zero k (Units.ne_zero _)
  simp only [fW, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, mul_inv]
  rw [← ht₀] at hcross
  field_simp
  linear_combination hcross

end Transfer

end MixedFujita
