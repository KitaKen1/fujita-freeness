/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureHyperplaneEquivalence
public import MixedFujita.ProperBirationalSections
public import MixedFujita.ProjectiveRestrictedDimGrowth
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.TangentCoordinateChain

/-!
The sections of q J restricted to the closure of a point are sections on the closure, and the
degree condition of section 5 from the growth of the restricted sections (step 11).

Let X be an integral scheme over K with a morphism e to projective space, J the hyperplane divisor
cut by a degree-one form g, and W the closure of a point η of X such that g does not vanish at the
generic point of W. Take a chart k containing η. The local coefficient at η of a section s of q J
is restricted to W through the stalk map at the generic point of W and divided by the q-th power
of the chart equation of g on W. This gives a rational function on W. At every point y of W, this
function times the q-th power of the chart equation of g at y is the restriction of the local
coefficient of s at ι(y): the coefficients are compatible with specialization, and the chart
equations of g differ by the same factor on X and on W. So the rational function is a section of
q J_W, and the restriction is a K-linear map from Γ(X, q J) to the sections of q J_W. A section
whose restriction is zero vanishes at η, because a unit coefficient restricts to a unit. Hence
the sections of q J restricted to W have dimension at most h^0(W, q J_W).

With the Hilbert asymptotics of W this gives the degree condition. Let d = dim W ≥ 1. Suppose
that for every ε > 0 and all large j some sections of j J restrict to W with dimension at least
(c - ε) j^d/d!. Then the degree r of W (h^0(W, D J_W) ~ r D^d/d!) is at least c. If the closure
of every generization w ≠ x of a point x satisfies this with c = s^dim, the degree condition of
section 5 holds at x; a generization w ≠ x has a closure of dimension at least one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra

section Specialization

variable {X : Scheme.{u}} [IsIntegral X]

/-- A local equation at a point is a local equation at its generizations. -/
theorem isLocalEquationAt_of_specializes {D : CartierDivisor X} {x x' : X} (h : x' ⤳ x)
    {f : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) : D.IsLocalEquationAt x' f := by
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (h.mem_open V.isOpen hxV)

/-- Local coefficients are compatible with the specialization maps of stalks. -/
theorem cartierLocalCoefficient_stalkSpecializes (D : CartierDivisor X) {x x' : X} (h : x' ⤳ x)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (hf' : D.IsLocalEquationAt x' f)
    (s : Γ(D.sheaf, ⊤)) :
    X.presheaf.stalkSpecializes h (cartierLocalCoefficient D x f hf s) =
      cartierLocalCoefficient D x' f hf' s := by
  apply IsFractionRing.injective (X.presheaf.stalk x') X.functionField
  rw [stalkSpecializes_algebraMap_functionField, cartierLocalCoefficient_image,
    cartierLocalCoefficient_image]

end Specialization

section Restriction

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- Germs at ι(y), restricted to rational functions on the closure of η, as a K-algebra map. -/
noncomputable def pointClosureFunctionFieldAlgHom (η : X) (y : pointClosureScheme η) :
    X.presheaf.stalk (pointClosureι η y) →ₐ[K] (pointClosureScheme η).functionField where
  toRingHom := pointClosureStalkToFunctionField y
  commutes' k := by
    change pointClosureStalkToFunctionField y
        (algebraMap K (X.presheaf.stalk (pointClosureι η y)) k) =
      algebraMap K (pointClosureScheme η).functionField k
    rw [pointClosureStalkToFunctionField_apply]
    rw [show (pointClosureι η).stalkMap y (algebraMap K (X.presheaf.stalk (pointClosureι η y)) k) =
        algebraMap K ((pointClosureScheme η).presheaf.stalk y) k from
      (pointClosureStalkAlgHom (K := K) η y).commutes k]
    change algebraMap ((pointClosureScheme η).presheaf.stalk y) (pointClosureScheme η).functionField
        ((pointClosureScheme η).presheaf.germ ⊤ y trivial
          (Scheme.Modules.baseRingToGlobalSections K (pointClosureScheme η) k)) =
      (pointClosureScheme η).germToFunctionField ⊤
        (Scheme.Modules.baseRingToGlobalSections K (pointClosureScheme η) k)
    exact (pointClosureScheme η).algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := y) trivial _

variable {N : ℕ} (e : X ⟶ polynomialProjectiveScheme N K) (g : MvPolynomial (Fin N) K)
  (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)

omit [X.Over (Spec (CommRingCat.of K))] in
/-- The local equation of q J at the image of the generic point of the closure of η, in a chart
containing it. -/
theorem pointClosure_hyperplane_isLocalEquationAt_generic (η : X) (q : ℕ) {k : Fin N}
    (hk : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k) :
    (q • projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt
      (pointClosureι η (genericPoint (pointClosureScheme η)))
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hk) ^ q) :=
  cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt e g hg hggen
    (pointClosureAmbientChart e hk) _ (pointClosureι_mem_projectiveCoordinateOpen e hk)) q

/-- The restriction of the sections of q J to rational functions on the closure W of η: the local
coefficient at η in the chart k, restricted to W and divided by the q-th power of the chart
equation of g on W. -/
noncomputable def pointClosureHyperplaneRestriction (η : X)
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    (q : ℕ) {k : Fin N} (hk : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k) :
    Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) →ₗ[K]
      (pointClosureScheme η).functionField :=
  LinearMap.mulRight K ((((projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW
      ⟨k, ⟨⟨_, hk⟩⟩⟩)⁻¹ ^ q : (pointClosureScheme η).functionFieldˣ) :
        (pointClosureScheme η).functionField)) ∘ₗ
    ((pointClosureFunctionFieldAlgHom (K := K) η
        (genericPoint (pointClosureScheme η))).toLinearMap ∘ₗ
      ((cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _
        (pointClosure_hyperplane_isLocalEquationAt_generic e g hg hggen η q hk)).restrictScalars
          K))

theorem pointClosureHyperplaneRestriction_apply (η : X)
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    (q : ℕ) {k : Fin N} (hk : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)
    (s : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    pointClosureHyperplaneRestriction e g hg hggen η hgW q hk s =
      pointClosureStalkToFunctionField (genericPoint (pointClosureScheme η))
          (cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _
            (pointClosure_hyperplane_isLocalEquationAt_generic e g hg hggen η q hk) s) *
        (((projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW ⟨k, ⟨⟨_, hk⟩⟩⟩)⁻¹ ^ q :
          (pointClosureScheme η).functionFieldˣ) : (pointClosureScheme η).functionField) :=
  rfl

/-- The restriction of a section of q J is a section of q J_W. -/
theorem pointClosureHyperplaneRestriction_mem (η : X)
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    (q : ℕ) {k : Fin N} (hk : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)
    (s : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :
    pointClosureHyperplaneRestriction e g hg hggen η hgW q hk s ∈
      cartierSectionSpace K (q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW) := by
  rw [mem_cartierSectionSpace_iff]
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro y _
  have hξy : genericPoint (pointClosureScheme η) ⤳ y :=
    (genericPoint_spec (pointClosureScheme η)).specializes trivial
  -- a chart containing y, which also contains the generic point
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart N K ((pointClosureι η ≫ e) y)
  have hyk' : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k' := hk'
  have hξk' : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k' :=
    hξy.mem_open (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k').isOpen hyk'
  set jW : {l : Fin N // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) l)} :=
    ⟨k, ⟨⟨_, hk⟩⟩⟩ with hjW
  set jW' : {l : Fin N // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) l)} :=
    ⟨k', ⟨⟨y, hyk'⟩⟩⟩ with hjW'
  refine ⟨projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW jW' ^ q,
    cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt (pointClosureι η ≫ e)
      g hg hgW jW' y hyk') q, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  -- the local equations on X at ι(y) and at the image of the generic point
  have hfy : (q • projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt (pointClosureι η y)
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hyk') ^ q) :=
    cartierLocalEquation_pow _ _ _ (projectiveHyperplane_isLocalEquationAt e g hg hggen
      (pointClosureAmbientChart e hyk') _ (pointClosureι_mem_projectiveCoordinateOpen e hyk')) q
  have hξyX : pointClosureι η (genericPoint (pointClosureScheme η)) ⤳ pointClosureι η y :=
    hξy.map (pointClosureι η).continuous
  have hfξ' := isLocalEquationAt_of_specializes hξyX hfy
  refine ⟨(pointClosureι η).stalkMap y
    (cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _ hfy s), ?_⟩
  change pointClosureStalkToFunctionField y
      (cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _ hfy s) = _
  rw [← pointClosureStalkToFunctionField_specializes hξy,
    cartierLocalCoefficient_stalkSpecializes _ hξyX _ hfy hfξ',
    pointClosureHyperplaneRestriction_apply]
  -- the chart equations of g at the image of the generic point, on X and on W
  obtain ⟨G, hGX, hGW⟩ : ∃ G : X.presheaf.stalk (pointClosureι η (genericPoint
      (pointClosureScheme η))),
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hk) : X.functionField) =
        algebraMap _ X.functionField G ∧
      pointClosureStalkToFunctionField (genericPoint (pointClosureScheme η)) G =
        (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW jW :
          (pointClosureScheme η).functionField) :=
    ⟨_, projectiveHyperplaneUnit_eq_algebraMap_germ e g hg hggen (pointClosureAmbientChart e hk)
      _ (pointClosureι_mem_projectiveCoordinateOpen e hk),
      pointClosureStalkToFunctionField_hyperplaneEquation e g hg hgW _ jW hk⟩
  obtain ⟨G', hGX', hGW'⟩ : ∃ G' : X.presheaf.stalk (pointClosureι η (genericPoint
      (pointClosureScheme η))),
      (projectiveHyperplaneUnit e g hg hggen (pointClosureAmbientChart e hyk') :
          X.functionField) = algebraMap _ X.functionField G' ∧
      pointClosureStalkToFunctionField (genericPoint (pointClosureScheme η)) G' =
        (projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW jW' :
          (pointClosureScheme η).functionField) :=
    ⟨_, projectiveHyperplaneUnit_eq_algebraMap_germ e g hg hggen (pointClosureAmbientChart e hyk')
      _ (pointClosureι_mem_projectiveCoordinateOpen e hξk'),
      pointClosureStalkToFunctionField_hyperplaneEquation e g hg hgW _ jW' hξk'⟩
  -- the two coefficients differ by the ratio of the chart equations
  have hX : cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _ hfξ' s *
      G ^ q = cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _
        (pointClosure_hyperplane_isLocalEquationAt_generic e g hg hggen η q hk) s * G' ^ q := by
    apply IsFractionRing.injective
      (X.presheaf.stalk (pointClosureι η (genericPoint (pointClosureScheme η)))) X.functionField
    rw [map_mul, map_mul, map_pow, map_pow, cartierLocalCoefficient_image,
      cartierLocalCoefficient_image, ← hGX, ← hGX', Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    ring
  have hW := congrArg (pointClosureStalkToFunctionField (genericPoint (pointClosureScheme η))) hX
  rw [map_mul, map_mul, map_pow, map_pow, hGW, hGW'] at hW
  have hU : ((projectiveHyperplaneUnit (pointClosureι η ≫ e) g hg hgW jW :
      (pointClosureScheme η).functionFieldˣ) : (pointClosureScheme η).functionField) ≠ 0 :=
    Units.ne_zero _
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  field_simp
  linear_combination hW

/-- A section whose restriction to the closure of η is zero vanishes at η. -/
theorem mem_cartierSectionsVanishingAt_of_pointClosureHyperplaneRestriction_eq_zero (η : X)
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    (q : ℕ) {k : Fin N} (hk : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k)
    (s : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    (h : pointClosureHyperplaneRestriction e g hg hggen η hgW q hk s = 0) :
    s ∈ cartierSectionsVanishingAt K (q • projectiveHyperplaneCartier e g hg hggen) η := by
  rw [pointClosureHyperplaneRestriction_apply] at h
  have h1 := (mul_eq_zero.mp h).resolve_right (Units.ne_zero _)
  have hs : s ∈ cartierSectionsVanishingAt K (q • projectiveHyperplaneCartier e g hg hggen)
      (pointClosureι η (genericPoint (pointClosureScheme η))) := by
    rw [mem_cartierSectionsVanishingAt_iff _ _ _
      (pointClosure_hyperplane_isLocalEquationAt_generic e g hg hggen η q hk)]
    by_contra hc
    have hu : IsUnit (cartierLocalCoefficient (q • projectiveHyperplaneCartier e g hg hggen) _ _
        (pointClosure_hyperplane_isLocalEquationAt_generic e g hg hggen η q hk) s) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
    exact (hu.map (pointClosureStalkToFunctionField (genericPoint (pointClosureScheme η)))).ne_zero
      h1
  rwa [pointClosureι_genericPoint] at hs

/-- The sections of q J restricted to the closure of η have at most the dimension of the sections
of q J_W. -/
theorem projectiveHyperplane_cartierRestrictedDim_le_pointClosure (η : X)
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    (q : ℕ) [FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    [FiniteDimensional K
      Γ((q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤)] :
    cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) η ≤
      Module.finrank K
        Γ((q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart N K
    ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η)))
  have hk' : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k := hk
  have hker : LinearMap.ker (pointClosureHyperplaneRestriction e g hg hggen η hgW q hk') ≤
      cartierSectionsVanishingAt K (q • projectiveHyperplaneCartier e g hg hggen) η :=
    fun s hs => mem_cartierSectionsVanishingAt_of_pointClosureHyperplaneRestriction_eq_zero e g hg
      hggen η hgW q hk' s hs
  have hrange : LinearMap.range (pointClosureHyperplaneRestriction e g hg hggen η hgW q hk') ≤
      cartierSectionSpace K (q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW) := by
    rintro _ ⟨s, rfl⟩
    exact pointClosureHyperplaneRestriction_mem e g hg hggen η hgW q hk' s
  have : FiniteDimensional K (cartierSectionSpace K
      (q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW)) :=
    LinearMap.finiteDimensional_range _
  have h1 := Submodule.finrank_quotient_add_finrank
    (cartierSectionsVanishingAt K (q • projectiveHyperplaneCartier e g hg hggen) η)
  have h2 := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (pointClosureHyperplaneRestriction e g hg hggen η hgW q hk'))
  have h3 := Submodule.finrank_mono hker
  have h4 := (pointClosureHyperplaneRestriction e g hg hggen η hgW q hk').quotKerEquivRange.finrank_eq
  have h5 : Module.finrank K
      (LinearMap.range (pointClosureHyperplaneRestriction e g hg hggen η hgW q hk')) ≤
      Module.finrank K (cartierSectionSpace K
        (q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW)) :=
    LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hrange)
      (Submodule.inclusion_injective hrange)
  have h6 := finrank_cartierSectionSpace K
    (q • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW)
  unfold cartierRestrictedDim
  omega

end Restriction

section Degree

variable {K : Type u} [Field K] [Infinite K] {N : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  (e : X ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)

/-- The degree of the closure of η is at least c when, for every ε > 0, some sections of j J
restrict to it with dimension at least (c - ε) j^d/d! for all large j. -/
theorem projectiveHyperplane_degree_ge_of_restrictedGrowth
    (he : e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K)) (η : X) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : topologicalKrullDim (closure ({η} : Set X)) = ((d : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    [∀ q : ℕ, FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    {c : ℝ} (hgrow : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
        (c - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V)
    (r : ℕ) (hr : Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
          (D : ℝ) ^ d) atTop (nhds ((r : ℝ) / d.factorial))) :
    c ≤ r := by
  have hW : topologicalKrullDim (pointClosureScheme η) = ((d : ℕ) : WithBot ℕ∞) := by
    rw [pointClosureScheme_topologicalKrullDim, hd]
  have heW : (pointClosureι η ≫ e) ≫ polynomialProjectiveToBase N K =
      pointClosureScheme η ↘ Spec (CommRingCat.of K) :=
    pointClosureι_comp_toBase (fun _ : ℕ => e) (fun _ => he) 0
  have hfinW : ∀ D : ℕ, FiniteDimensional K
      Γ((D • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) :=
    fun D => projectiveHyperplaneSections_finiteDimensional_integral (pointClosureι η ≫ e) g hg
      hgW heW hW hd1 D
  have hdfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- eventually (c - ε)/d! ≤ h^0(W, j J_W)/j^d
  have hev : ∀ᶠ j : ℕ in atTop, (c - ε) / d.factorial ≤ (Module.finrank K
      Γ((j • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
        (j : ℝ) ^ d := by
    filter_upwards [hgrow ε hε, eventually_ge_atTop 1] with j hj hj1
    obtain ⟨V, -, hV⟩ := hj
    have := hfinW j
    have h1 := cartierRestrictedSubspaceDim_le K (j • projectiveHyperplaneCartier e g hg hggen) η V
    have h2 := projectiveHyperplane_cartierRestrictedDim_le_pointClosure e g hg hggen η hgW j
    have hjpos : (0 : ℝ) < (j : ℝ) ^ d := by
      have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      positivity
    rw [le_div_iff₀ hjpos]
    have h3 : (cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V :
        ℝ) ≤ (Module.finrank K
          Γ((j • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) : ℝ) := by
      exact_mod_cast h1.trans h2
    calc (c - ε) / d.factorial * (j : ℝ) ^ d = (c - ε) * (j : ℝ) ^ d / d.factorial := by ring
      _ ≤ _ := hV
      _ ≤ _ := h3
  have hlim := ge_of_tendsto hr hev
  have h4 : c - ε ≤ r := by
    have := mul_le_mul_of_nonneg_right hlim hdfac.le
    rwa [div_mul_cancel₀ _ hdfac.ne', div_mul_cancel₀ _ hdfac.ne'] at this
  linarith

/-- The degree condition of section 5 at x from the growth of the restricted sections with constant
s^dim at the closures of the generizations of x: every generization w ≠ x of x whose closure has
dimension D' has degree at least s^D'. -/
theorem projectiveHyperplane_degreeCondition_of_restrictedGrowth
    (he : e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K)) (x : X) (s : ℕ)
    [∀ q : ℕ, FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    (hgrow : ∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          (((s : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V) :
    ∀ (w : X) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set X)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r := by
  intro w hgW D' hwx hne hD' r hr
  -- the closure of a proper generization has dimension at least one
  have h1 := le_topologicalKrullDim_closure_of_generization_chain 1 ![x, w]
    (fun i => by fin_cases i; simpa using hwx) (fun i => by fin_cases i; simpa using hne)
  have h1' : ((1 : ℕ) : WithBot ℕ∞) ≤ ((D' : ℕ) : WithBot ℕ∞) := by
    have h2 : (![x, w] (Fin.last 1) : X) = w := rfl
    rw [h2, hD'] at h1
    exact h1
  have hD'1 : 1 ≤ D' := by exact_mod_cast h1'
  have := projectiveHyperplane_degree_ge_of_restrictedGrowth e g hg hggen he w hD'1 hD' hgW
    (hgrow w D' hD' hD'1) r hr
  exact_mod_cast this

end Degree

section Dimension

variable {T : Type*} [TopologicalSpace T]

/-- In a space of dimension m, the closure of a point has the dimension of a natural number at most
m. -/
theorem exists_nat_topologicalKrullDim_closure_eq {m : ℕ}
    (hT : topologicalKrullDim T = ((m : ℕ) : WithBot ℕ∞)) (w : T) :
    ∃ D' : ℕ, D' ≤ m ∧
      topologicalKrullDim (closure ({w} : Set T)) = ((D' : ℕ) : WithBot ℕ∞) := by
  have hle : topologicalKrullDim (closure ({w} : Set T)) ≤ ((m : ℕ) : WithBot ℕ∞) :=
    hT ▸ topologicalKrullDim_subspace_le T _
  have hne : topologicalKrullDim (closure ({w} : Set T)) ≠ ⊥ := by
    intro hbot
    have hempty := Order.krullDim_eq_bot_iff.mp hbot
    exact hempty.false ⟨closure {⟨w, subset_closure rfl⟩}, isIrreducible_singleton.closure,
      isClosed_closure⟩
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← ha] at hle
  have hle' : a ≤ (m : ℕ∞) := by exact_mod_cast hle
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hle'
  refine ⟨a.toNat, ?_, ?_⟩
  · have := ENat.toNat_le_toNat hle' (ENat.natCast_ne_top m)
    simpa using this
  · rw [← ha]
    exact_mod_cast (ENat.natCast_toNat hatop).symm

end Dimension

end MixedFujita
