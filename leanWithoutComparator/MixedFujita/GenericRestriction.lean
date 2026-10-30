/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedIdealLemmaThree
public import MixedFujita.LemmaThreeFromRestriction
public import MixedFujita.GenericFibreCharts
public import MixedFujita.PointEtaleCoordinates
public import MixedFujita.FibreTestPrimeLift
public import MixedFujita.FibreSNCOrders
public import MixedFujita.AffineEtaleChartRestrictions

/-!
Generic restriction for products (step 9): `GenericRestrictionStatement` holds
(`genericRestrictionStatement_holds`), so F1 follows from sum KV and restriction to fibres alone
(`mixedFujitaFreeness_of_kvSum_of_fibreRestriction`).

Let X = Spec(Γ(V) ⊗ B) and T a projective simple normal crossing model principalizing the nonzero
members of the family. Choose h ≠ 0 in B such that over D(h) every point of T has a fibre chart
(generic smoothness of the strata), the generic point of every fibre lies in the domain of a
section of T → X near the generic point, and the members stay nonzero on the fibres. For a K-point
w with w(h) ≠ 0 and a bad test prime e of a fibre at y, restrict the test model over V and map it
into the fibre of X over w; it lifts near e to T. At the image t₀ of e take the fibre chart, a
chart of X at (y, w) whose coordinates are a_i ⊗ 1 and 1 ⊗ u_l for coordinates a of V at y and u of
B at w, and a chart of Y at y with coordinates a. The orders o_s of the members along e satisfy
Σ_s (1 - b_s) o_s ≤ A(e) and compute the orders of the members of the family and of the
principalized divisor, so a member of the family with o_s > 0 is bad, and its centre contains
(y, w).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra specAlgebraOver

section Germs

/-- The pullback of a global section along a Spec map. -/
theorem specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) r
  simp only [CommRingCat.comp_apply] at h
  exact h.symm

/-- Germs of global sections pulled back along a composite. -/
theorem stalkMap_stalkMap_germ_top {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (s : Γ(Z, ⊤)) :
    f.stalkMap x (g.stalkMap (f x) (Z.presheaf.germ ⊤ (g (f x)) trivial s)) =
      X.presheaf.germ ⊤ x trivial ((f ≫ g).appTop s) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- Germs of global sections pulled back along a morphism. -/
theorem stalkMap_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (s : Γ(Y, ⊤)) :
    f.stalkMap x (Y.presheaf.germ ⊤ (f x) trivial s) = X.presheaf.germ ⊤ x trivial (f.appTop s) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- Germs of sections of an affine open pulled back to its spectrum. -/
theorem fromSpec_stalkMap_germ {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    (y : Spec Γ(Y, V)) (hy : hV.fromSpec y ∈ V) (a : Γ(Y, V)) :
    hV.fromSpec.stalkMap y (Y.presheaf.germ V (hV.fromSpec y) hy a) =
      (Spec Γ(Y, V)).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso Γ(Y, V)).inv a) := by
  rw [Scheme.Hom.germ_stalkMap_apply, IsAffineOpen.fromSpec_app_self_apply]
  exact TopCat.Presheaf.germ_res_apply' _ _ _ _ _

/-- The germ of a constant global function. -/
theorem germ_top_algebraMap {K : Type u} [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] (x : X) (k : K) :
    X.presheaf.germ ⊤ x trivial (algebraMap K Γ(X, ⊤) k) = algebraMap K (X.presheaf.stalk x) k := by
  change X.presheaf.germ ⊤ x trivial (((X.baseRingToStructurePresheaf K).app (op ⊤)).hom k) = _
  rw [Scheme.baseRingToStructurePresheaf_app]
  change X.presheaf.germ ⊤ x trivial (X.presheaf.map (homOfLE le_top).op
    (Scheme.Modules.baseRingToGlobalSections K X k)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- Germs of functions on an affine open V pulled back along Spec(Γ(V) ⊗ B) → Spec Γ(V) → Y. -/
theorem stalkMap_specMap_includeLeft_fromSpec_germ {K : Type u} [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] {V : Y.Opens} (hV : IsAffineOpen V) (B : Type u)
    [CommRing B] [Algebra K B] (x : Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))
    (hx : (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom) ≫
        hV.fromSpec) x ∈ V) (a : Γ(Y, V)) :
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom) ≫
        hV.fromSpec).stalkMap x (Y.presheaf.germ V _ hx a) =
      (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ x trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (a ⊗ₜ[K] (1 : B))) := by
  have h1 := fromSpec_stalkMap_germ hV ((Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom)) x) hx a
  rw [Scheme.Hom.stalkMap_comp]
  refine (congrArg (fun z => ConcreteCategory.hom ((Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom)).stalkMap x) z)
      h1).trans ?_
  refine (stalkMap_germ_top (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom)) x _).trans ?_
  exact congrArg _ (specMap_appTop_ΓSpecIso_inv (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B).toRingHom) a)

end Germs

section Orders

variable {K : Type u} [Field K] {N : ℕ} {T W : Scheme.{u}}
  [T.Over (Spec (CommRingCat.of K))] [IsIntegral W] [IsLocallyNoetherian W] (α : W ⟶ T)

/-- The member orders are nonnegative. -/
theorem fibreSNCOrder_nonneg (e : W) (F : EtaleChart K T N) (hF : α e ∈ F.U) {r : ℕ}
    (σF : Fin r → Option (Fin N)) (s : Fin r) : 0 ≤ fibreSNCOrder α e F hF σF s := by
  unfold fibreSNCOrder
  cases σF s with
  | none => exact le_rfl
  | some a =>
    exact scheme_ord_nonneg_of_mem_stalk e _ ⟨_, rfl⟩

/-- A member whose closure misses the image of e has order zero. -/
theorem fibreSNCOrder_eq_zero_of_notMem_closure (e : W) (F : EtaleChart K T N) (hF : α e ∈ F.U)
    {r : ℕ} (ξ : Fin r → T) (σF : Fin r → Option (Fin N)) (hFsnc : IsSNCChart F ξ σF)
    (s : Fin r) (hs : α e ∉ closure ({ξ s} : Set T)) : fibreSNCOrder α e F hF σF s = 0 := by
  unfold fibreSNCOrder
  cases hσ : σF s with
  | none => rfl
  | some a =>
    have hset := hFsnc.2 s
    rw [hσ, Option.elim_some] at hset
    have hb : α e ∈ T.basicOpen (F.coords (MvPolynomial.X a)) := by
      by_contra hb
      apply hs
      have hmem : α e ∈ T.zeroLocus ({F.coords (MvPolynomial.X a)} : Set Γ(T, F.U)) ∩ F.U :=
        ⟨by rw [Scheme.zeroLocus_singleton]; exact hb, hF⟩
      rw [← hset] at hmem
      exact hmem.1
    have hunit : IsUnit (T.presheaf.germ F.U (α e) hF (F.coords (MvPolynomial.X a))) :=
      (T.mem_basicOpen _ (α e) hF).mp hb
    simp only [Option.elim_some, fibreOrd]
    exact scheme_ord_stalk_unit e (hunit.map (α.stalkMap e).hom).unit

end Orders

section LocalProductVariant

attribute [local instance] cartierGlobalStalkFunctionFieldTower cartierBaseGlobalAlgebra
  cartierBaseLocalScalarTower functionFieldBaseAlgebra

variable {K : Type u} [Field K] {N : ℕ} {T W : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [IsIntegral W] [IsLocallyNoetherian W]
  (α : W ⟶ T) [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]

/-- The order along a prime of W of the pullback of a local equation of a divisor supported on the
simple normal crossing family is the weighted sum of the orders of the member coordinates, provided
the pullback of the equation is nonzero (then so are the pullbacks of the member coordinates with
positive coefficient). -/
theorem fibreOrd_snc_local_equation_of_ne_zero (e : CodimensionOnePoint W)
    [IsDiscreteValuationRing (W.presheaf.stalk (e : W))]
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (F : EtaleChart K T N) (hF : α (e : W) ∈ F.U) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σF : Fin r → Option (Fin N)) (hFsnc : IsSNCChart F ξ σF) (D : CartierDivisor T)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient D (z : T) = 0)
    (hnonneg : ∀ i, 0 ≤ cartierCoefficient D (ξ i)) (q : T.presheaf.stalk (α (e : W)))
    (hq : algebraMap (T.presheaf.stalk (α (e : W))) T.functionField q ≠ 0)
    (hloc : D.IsLocalEquationAt (α (e : W)) (Units.mk0 _ hq))
    (hq0 : α.stalkMap (e : W) q ≠ 0) :
    fibreOrd α (e : W) q =
      ∑ s, cartierCoefficient D (ξ s) * fibreSNCOrder α (e : W) F hF σF s := by
  classical
  obtain ⟨f, hf, u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm D F ξ hinj hξ σF hFsnc
    hsupp (α (e : W)) hF
  obtain ⟨u', hu'⟩ := hloc.exists_unit_mul_eq hf
  -- the member coordinates and their exponents in the stalk
  let z : Fin r → T.presheaf.stalk (α (e : W)) := fun s =>
    (σF s).elim 1 fun a => etaleChartStalkCoords F (α (e : W)) hF (MvPolynomial.X a)
  have hzval : ∀ s, (sncChartComponentEquation F σF s : T.functionField) =
      algebraMap (T.presheaf.stalk (α (e : W))) T.functionField (z s) := by
    intro s
    cases hs : σF s with
    | none => simp [sncChartComponentEquation, z, hs]
    | some a =>
      simp only [sncChartComponentEquation, z, hs, Option.elim_some,
        etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
      rw [← T.algebraMap_germ_eq_germToFunctionField hF]
      rfl
  have hpow : ∀ s, ((sncChartComponentEquation F σF s ^ cartierCoefficient D (ξ s) :
      T.functionFieldˣ) : T.functionField) =
      algebraMap (T.presheaf.stalk (α (e : W))) T.functionField
        (z s ^ (cartierCoefficient D (ξ s)).toNat) := by
    intro s
    have h0 := hnonneg s
    rw [← Int.toNat_of_nonneg h0, zpow_natCast, Units.val_pow_eq_pow_val, hzval, map_pow,
      Int.toNat_natCast]
  have hq' : q = ((u' * u : (T.presheaf.stalk (α (e : W)))ˣ) : T.presheaf.stalk (α (e : W))) *
      ∏ s, z s ^ (cartierCoefficient D (ξ s)).toNat := by
    apply IsFractionRing.injective (T.presheaf.stalk (α (e : W))) T.functionField
    have h1 : algebraMap (T.presheaf.stalk (α (e : W))) T.functionField q =
        algebraMap _ _ (u' : T.presheaf.stalk (α (e : W))) * (f : T.functionField) := by
      rw [hu']
      rfl
    rw [h1, hu, Units.coe_prod, Finset.prod_congr rfl fun s _ => hpow s]
    simp only [Units.val_mul, map_mul, map_prod]
    ring
  -- the coordinates with positive exponent pull back to nonzero elements
  have hzs : ∀ s, cartierCoefficient D (ξ s) ≠ 0 → α.stalkMap (e : W) (z s) ≠ 0 := by
    intro s hs h0
    apply hq0
    rw [hq', map_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ s) ?_)
    have hpos : 0 < (cartierCoefficient D (ξ s)).toNat := by
      have := hnonneg s
      omega
    rw [map_pow, h0, zero_pow hpos.ne']
  let z' : Fin r → T.presheaf.stalk (α (e : W)) := fun s =>
    if cartierCoefficient D (ξ s) = 0 then 1 else z s
  have hz'pow : ∀ s, z s ^ (cartierCoefficient D (ξ s)).toNat =
      z' s ^ (cartierCoefficient D (ξ s)).toNat := by
    intro s
    by_cases hs : cartierCoefficient D (ξ s) = 0
    · simp [hs]
    · simp [z', hs]
  have hz's : ∀ s, α.stalkMap (e : W) (z' s) ≠ 0 := by
    intro s
    by_cases hs : cartierCoefficient D (ξ s) = 0
    · simp [z', hs]
    · simpa [z', hs] using hzs s hs
  let v : Fin r → W.functionFieldˣ := fun s => Units.mk0
    (algebraMap (W.presheaf.stalk (e : W)) W.functionField (α.stalkMap (e : W) (z' s)))
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz's s))
  have hunit : IsUnit (α.stalkMap (e : W) ((u' * u : (T.presheaf.stalk (α (e : W)))ˣ) :
      T.presheaf.stalk (α (e : W)))) := (Units.isUnit _).map _
  have hval : algebraMap (W.presheaf.stalk (e : W)) W.functionField (α.stalkMap (e : W) q) =
      algebraMap (W.presheaf.stalk (e : W)) W.functionField hunit.unit *
        ((∏ s, v s ^ cartierCoefficient D (ξ s) : W.functionFieldˣ) : W.functionField) := by
    rw [hq', Finset.prod_congr rfl fun s _ => hz'pow s, map_mul, map_prod, map_mul,
      IsUnit.unit_spec, Units.coe_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← Int.toNat_of_nonneg (hnonneg s), zpow_natCast, Units.val_pow_eq_pow_val, map_pow,
      map_pow, Int.toNat_natCast]
    rfl
  have hne : algebraMap (W.presheaf.stalk (e : W)) W.functionField hunit.unit ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hunit.unit.ne_zero
  unfold fibreOrd
  rw [hval, Scheme.ord_mul hne (Units.ne_zero _), scheme_ord_stalk_unit, zero_add,
    scheme_ord_prod_zpow]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : cartierCoefficient D (ξ s) = 0
  · rw [hs, zero_mul, zero_mul]
  congr 1
  unfold fibreSNCOrder
  cases hσ : σF s with
  | none => simp [v, z', z, hs, hσ]
  | some a => simp [v, z', z, hs, hσ, fibreOrd]

end LocalProductVariant

section AwayCoordinates

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsAffine X]
  {N : ℕ} [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))]

omit [IsAffine X] [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))] in
/-- The base field acts compatibly on the global functions and the functions on a basic open. -/
theorem isScalarTower_top_basicOpen (b : Γ(X, ⊤)) :
    IsScalarTower K Γ(X, ⊤) Γ(X, X.basicOpen b) := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  change ((X.baseRingToStructurePresheaf K).app (op (X.basicOpen b))).hom k =
    (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom
      (((X.baseRingToStructurePresheaf K).app (op ⊤)).hom k)
  rw [Scheme.baseRingToStructurePresheaf_app, Scheme.baseRingToStructurePresheaf_app]
  change _ = X.presheaf.map (homOfLE (X.basicOpen_le b)).op (X.presheaf.map (homOfLE le_top).op
    (Scheme.Modules.baseRingToGlobalSections K X k))
  rw [presheaf_map_map_eq]
  rfl

/-- Étale coordinates of a smooth affine scheme at a K-point, given by global functions, on a
basic open neighbourhood. -/
theorem exists_away_coordinates (x : X) (χ : Γ(X, ⊤) →ₐ[K] K)
    (hχ : ∀ a, χ a = 0 ↔ a ∈ ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal) :
    ∃ (u : Fin N → Γ(X, ⊤)) (b : Γ(X, ⊤)), χ b ≠ 0 ∧ DifferentialsIndependentAt K χ u ∧
      (MvPolynomial.aeval (R := K)
        (fun l => algebraMap Γ(X, ⊤) (Localization.Away b) (u l))).toRingHom.FormallyEtale := by
  obtain ⟨u, hu⟩ := exists_differentialsIndependentAt (N := N) (isAffineOpen_top X) x trivial χ hχ
  obtain ⟨c, hxc, hle, hc⟩ :=
    exists_etaleChart_of_differentialsIndependentAt (isAffineOpen_top X) x trivial χ hχ u hu
  obtain ⟨b, hbc, hxb⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := c.U) ⟨x, hxc⟩ trivial
  refine ⟨u, b, fun h0 => ?_, hu, ?_⟩
  · exact (mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top X) x trivial b).mp hxb
      ((hχ b).mp h0)
  · haveI := isScalarTower_top_basicOpen (K := K) b
    let φ₁ : MvPolynomial (Fin N) K →ₐ[K] Γ(X, X.basicOpen b) :=
      (sectionOpenRestrictionAlgHom (K := K) hbc).comp c.coords
    have hφ₁ : φ₁.toRingHom.FormallyEtale := formallyEtale_comp _
      (affineOpenRestriction_formallyEtale ⟨c.U, c.isAffine⟩
        ⟨X.basicOpen b, (isAffineOpen_top X).basicOpen b⟩ hbc) _ c.formallyEtale
    let e : Localization.Away b ≃ₐ[Γ(X, ⊤)] Γ(X, X.basicOpen b) :=
      IsLocalization.algEquiv (Submonoid.powers b) _ _
    let eK : Localization.Away b ≃ₐ[K] Γ(X, X.basicOpen b) := e.restrictScalars K
    have heq : MvPolynomial.aeval (R := K)
        (fun l => algebraMap Γ(X, ⊤) (Localization.Away b) (u l)) =
        eK.symm.toAlgHom.comp φ₁ := by
      apply MvPolynomial.algHom_ext
      intro l
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply]
      have h1 : φ₁ (MvPolynomial.X l) = algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b) (u l) := by
        change X.presheaf.map (homOfLE hbc).op (c.coords (MvPolynomial.X l)) = _
        rw [hc l, presheaf_map_map_eq]
        rfl
      rw [h1]
      change _ = e.symm (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b) (u l))
      rw [AlgEquiv.commutes]
    rw [heq]
    exact formallyEtale_comp _ (ringHom_formallyEtale_of_etale _
      (RingHom.Etale.of_bijective eK.symm.bijective)) _ hφ₁

end AwayCoordinates

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (Y : Scheme.{u}) [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] {n : ℕ}
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] (cY : EtaleChart K Y n)
  (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (B : Type u) [CommRing B] [IsDomain B]
  [Algebra K B] {d : ℕ}
  [SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))]
  [IsDomain (Γ(Y, V) ⊗[K] B)]
  [SmoothOfRelativeDimension (n + d)
    (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)) ↘ Spec (CommRingCat.of K))]

set_option maxHeartbeats 3200000 in
include hV in
/-- Generic restriction for a product V × Spec B. -/
theorem generic_restriction_of_product (cX : EtaleChart K (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (n + d)) {J : Type} [Finite J]
    (g : J → (Γ(Y, V) ⊗[K] B)) (M : ℕ) (hn : 1 ≤ n) (hM : 1 ≤ M) :
    ∃ h : B, h ≠ 0 ∧ ∀ w : B →ₐ[K] K, w h ≠ 0 →
      ∀ (y : Y) (hy : y ∈ V) (ψ : Γ(Y, V) →ₐ[K] K),
      (∀ a, ψ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) →
      ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
        (fun j => Y.germToFunctionField V (fibreAt w (g j))) M →
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ)))
        (specAlgHomPoint (pairAlgHom ψ w))
        (fun j => (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j))) M := by
  classical
  have hsmX : Smooth ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + d) _
  -- the zero family
  by_cases hzero : ∀ j, g j = 0
  · refine ⟨1, one_ne_zero, fun w _ y hy ψ hψ _ => ?_⟩
    exact modelThresholdBadAt_of_forall_eq_zero (by omega) cX _ (specAlgHomPoint_isClosed _) _
      (fun j => by rw [hzero j, map_zero, map_zero]) M
  push Not at hzero
  obtain ⟨j₀, hj₀⟩ := hzero
  -- the divisors of the nonzero members
  let J' := {j : J // g j ≠ 0}
  haveI : Nonempty J' := ⟨⟨j₀, hj₀⟩⟩
  have hgerm0 : ∀ j : J', (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j.1)) ≠ 0 := by
    intro j h0
    haveI : Nonempty (⊤ : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    apply j.2
    have h1 := (Scheme.germToFunctionField_injective (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) ⊤) (h0.trans (map_zero _).symm)
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).hom h1
    simpa using h2
  let uX : J' → (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ := fun j => Units.mk0 _ (hgerm0 j)
  let Adiv : J' → CartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) := fun j => principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (uX j)
  have hA : ∀ j, (Adiv j).IsEffective := fun j => by
    change (principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (uX j)).IsEffective
    rw [CartierDivisor.isEffective_principalCartierDivisor_iff]
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j.1), rfl⟩
  -- a principalizing simple normal crossing model
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, -, hAsupp, -, -, -, Gc, hGc, hGcI, hGc0, hmin, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n + d) cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ)))
      (Empty.elim : Empty → CartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))) Adiv hA
      (Empty.elim : Empty → (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).IdealSheafData) (fun j => j.elim)
  -- the relative canonical divisor of the model is supported on the family
  have hbrcd_supp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT
        etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    have h := hsupp z hz
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg,
      logDiscrepancyDivisor_boundary_zero, cartierCoefficient_nsmul] at h
    simpa using h
  -- generic fibre charts
  let incR : B →ₐ[K] (Γ(Y, V) ⊗[K] B) := Algebra.TensorProduct.includeRight
  let prB : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) ⟶ (Spec (CommRingCat.of B)) := Spec.map (CommRingCat.ofHom incR.toRingHom)
  let φ' : Γ((Spec (CommRingCat.of B)), ⊤) →+* Γ(T, ⊤) := ρ.appTop.hom.comp prB.appTop.hom
  have hbaseX : ∀ k : K, Scheme.Modules.baseRingToGlobalSections K (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) k =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (algebraMap K (Γ(Y, V) ⊗[K] B) k) := by
    intro k
    rw [Scheme.Modules.baseRingToGlobalSections_apply]
    change (Spec.map (CommRingCat.ofHom (algebraMap K (Γ(Y, V) ⊗[K] B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k) = _
    rw [specMap_appTop_ΓSpecIso_inv]
    rfl
  have hφ' : ∀ k : K, φ' (algebraMap K Γ((Spec (CommRingCat.of B)), ⊤) k) =
      Scheme.Modules.baseRingToGlobalSections K T k := by
    intro k
    rw [← scheme_appTop_baseRingToGlobalSections K ρ k, hbaseX]
    change ρ.appTop (prB.appTop (algebraMap K Γ((Spec (CommRingCat.of B)), ⊤) k)) = _
    congr 1
    rw [specAlgebraOver_algebraMap, specMap_appTop_ΓSpecIso_inv]
    congr 1
    exact incR.commutes k
  haveI : SmoothOfRelativeDimension d ((Spec (CommRingCat.of B)) ↘ Spec (CommRingCat.of K)) :=
    ‹SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))›
  haveI : Algebra.FiniteType K Γ((Spec (CommRingCat.of B)), ⊤) :=
    smooth_affineOpen_finiteType (K := K) (n := d) (isAffineOpen_top _)
  haveI : Nonempty (⊤ : (Spec (CommRingCat.of B)).Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  obtain ⟨hfib, hfib0, hfibprop⟩ :=
    exists_generic_fibreCharts (n := n) (d := d) ξ hsnc Γ((Spec (CommRingCat.of B)), ⊤) φ' hφ'
  -- a section of the model near the generic point
  obtain ⟨X₀, hηX₀, s₀, hs₀⟩ := exists_section_of_birational ρ hρ
  have hηX₀' : (⊥ : PrimeSpectrum (Γ(Y, V) ⊗[K] B)) ∈ (X₀ : Set (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))) := by
    have h := hηX₀
    rwa [genericPoint_eq_bot_of_affine] at h
  obtain ⟨_, ⟨F₀, rfl⟩, hF₀η, hF₀X₀⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηX₀' X₀.isOpen
  have hF₀ : F₀ ≠ 0 := fun h0 => by
    have h' : (⊥ : PrimeSpectrum (Γ(Y, V) ⊗[K] B)) ∈ PrimeSpectrum.basicOpen F₀ := hF₀η
    rw [PrimeSpectrum.mem_basicOpen, h0] at h'
    exact h' (Ideal.zero_mem _)
  obtain ⟨hiso, hiso0, hisoprop⟩ := exists_ne_zero_fibreAt hF₀
  -- the members stay nonzero on the fibres
  haveI : Fintype J' := Fintype.ofFinite J'
  choose hnz hnz0 hnzprop using fun j : J' => exists_ne_zero_fibreAt j.2
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom hfib * hiso * ∏ j, hnz j, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (fun h0 => hfib0 ?_) hiso0)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hnz0 j)
    have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).inv h0
    simpa using h1
  intro w hw y hy ψ hψ hbad
  rw [map_mul, map_mul, map_prod] at hw
  have hwfib : w ((Scheme.ΓSpecIso (CommRingCat.of B)).hom hfib) ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hw)
  have hwiso : w hiso ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hw)
  have hwnz : ∀ j, w (hnz j) ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hw) j (Finset.mem_univ j)
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hApos, hineq⟩ := hbad
  -- the part of the test model over V
  have heV : σ (e : U) ∈ V := (specializes_iff_mem_closure.mpr hye).mem_open V.isOpen hy
  let U' : U.Opens := σ ⁻¹ᵁ V
  have : Nonempty U' := ⟨⟨(e : U), heV⟩⟩
  let : U'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U'.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  have : U'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant U'.ι := ⟨U'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (U'.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := U'.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (U'.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : Smooth (U'.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : IsDominant (σ ∣_ V) := isDominant_morphismRestrict_integral σ V
  have hsq : (σ ∣_ V) ≫ V.ι = U'.ι ≫ σ := morphismRestrict_ι σ V
  have hbij : Function.Bijective (U'.ι.stalkMap ⟨(e : U), heV⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let e' : CodimensionOnePoint U'.toScheme :=
    ⟨⟨(e : U), heV⟩, (coheight_eq_of_stalkMap_bijective U'.ι ⟨(e : U), heV⟩ hbij).trans
      e.property⟩
  -- the test model mapped into the fibre of X over w
  let ιw : Spec Γ(Y, V) ⟶ (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) := Spec.map (CommRingCat.ofHom (fibreAt w).toRingHom)
  let τ : U'.toScheme ⟶ (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) := (σ ∣_ V) ≫ hV.isoSpec.hom ≫ ιw
  have hτη : τ (genericPoint U'.toScheme) ∈ X₀ := by
    apply hF₀X₀
    have h1 : (σ ∣_ V) (genericPoint U'.toScheme) = genericPoint V.toScheme :=
      dominant_map_genericPoint (σ ∣_ V)
    have h2 : hV.isoSpec.hom (genericPoint V.toScheme) = genericPoint (Spec Γ(Y, V)) :=
      dominant_map_genericPoint hV.isoSpec.hom
    have h3 : τ (genericPoint U'.toScheme) = ιw (genericPoint (Spec Γ(Y, V))) := by
      change ιw (hV.isoSpec.hom ((σ ∣_ V) (genericPoint U'.toScheme))) = _
      rw [h1, h2]
    rw [h3, genericPoint_eq_bot_of_affine]
    change F₀ ∉ ((PrimeSpectrum.comap (fibreAt w).toRingHom) ⊥).asIdeal
    intro hmem
    exact hisoprop w hwiso hmem
  -- the lift to the model near e
  have : IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (e' : U'.toScheme)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) e'
  obtain ⟨W, heW, α, hα⟩ := exists_local_lift_of_section ρ X₀ s₀ hs₀ τ hτη (e' : U'.toScheme)
  have : Nonempty W := ⟨⟨(e' : U'.toScheme), heW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : W.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨W.ι ≫ (U'.toScheme ↘ Spec (CommRingCat.of K))⟩
  have : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U'.toScheme ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have hbijW : Function.Bijective (W.ι.stalkMap ⟨(e' : U'.toScheme), heW⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let eW : CodimensionOnePoint W.toScheme :=
    ⟨⟨(e' : U'.toScheme), heW⟩, (coheight_eq_of_stalkMap_bijective W.ι ⟨(e' : U'.toScheme), heW⟩
      hbijW).trans e'.property⟩
  -- the projection to Y and the morphism identity
  let incL : Γ(Y, V) →ₐ[K] (Γ(Y, V) ⊗[K] B) := Algebra.TensorProduct.includeLeft
  let π : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) ⟶ Y := Spec.map (CommRingCat.ofHom incL.toRingHom) ≫ hV.fromSpec
  have hιπ : ιw ≫ Spec.map (CommRingCat.ofHom incL.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    change fibreAt w (a ⊗ₜ[K] (1 : B)) = a
    rw [fibreAt_tmul, map_one, map_one, mul_one]
  have hτπ : τ ≫ π = U'.ι ≫ σ := by
    simp only [τ, π, Category.assoc]
    rw [← Category.assoc ιw, hιπ, Category.id_comp, IsAffineOpen.isoSpec_hom_fromSpec, hsq]
  have heq : α ≫ ρ ≫ π = W.ι ≫ U'.ι ≫ σ := by
    rw [← Category.assoc, hα, Category.assoc, hτπ]
  -- the maps are over K
  have : π.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change Spec.map (CommRingCat.ofHom incL.toRingHom) ≫ hV.fromSpec ≫
      (Y ↘ Spec (CommRingCat.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K (Γ(Y, V) ⊗[K] B)))
    rw [affineOpen_fromSpec_over_eq_specMap hV, ← Spec.map_comp]
    congr 1
  have : α.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    have h1 := congrArg (· ≫ (Y ↘ Spec (CommRingCat.of K))) heq
    simp only [Category.assoc, HomIsOver.comp_over] at h1
    exact h1
  -- the test map α ≫ ρ ≫ π is the restriction of σ
  have hU'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) U'.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion U'.ι
  have hWι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  have hσU' := dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι
  have hσW := dominantFunctionFieldAlgHom_comp_bijective (U'.ι ≫ σ) W.ι hσU' hWι
  have : IsDominant (α ≫ ρ ≫ π) := by rw [heq]; infer_instance
  have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)) := by
    rw [dominantFunctionFieldAlgHom_congr_hom heq]
    exact hσW
  -- the points
  set t₀ : T := α (eW : W.toScheme) with ht₀
  have hρt₀ : ρ t₀ = τ (e' : U'.toScheme) := by
    change (α ≫ ρ) (eW : W.toScheme) = _
    rw [hα]
    rfl
  have hpair : ∀ r, ψ (fibreAt w r) = pairAlgHom ψ w r := by
    intro r
    induction r with
    | tmul a b => rw [fibreAt_tmul, pairAlgHom_tmul, map_mul, AlgHom.commutes]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  set p₀ : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) := specAlgHomPoint (pairAlgHom ψ w) with hp₀
  have hτp : τ (e' : U'.toScheme) ⤳ p₀ := by
    have h1 : (σ ∣_ V) (e' : U'.toScheme) ⤳ (⟨y, hy⟩ : V.toScheme) := by
      have h0 : (⟨y, hy⟩ : V.toScheme) ∈ closure ({(σ ∣_ V) (e' : U'.toScheme)} : Set V.toScheme) := by
        apply (mem_closure_singleton_open_immersion_iff V.ι ((σ ∣_ V) (e' : U'.toScheme))
          ⟨y, hy⟩).mp
        have h2 : V.ι ((σ ∣_ V) (e' : U'.toScheme)) = σ (e : U) := by
          rw [← Scheme.Hom.comp_apply, hsq]
          rfl
        rw [h2]
        exact hye
      exact specializes_iff_mem_closure.mpr h0
    have h2 := h1.map (hV.isoSpec.hom ≫ ιw).continuous
    have h3 : (hV.isoSpec.hom ≫ ιw) (⟨y, hy⟩ : V.toScheme) = p₀ := by
      apply PrimeSpectrum.ext
      ext r
      change fibreAt w r ∈ (hV.isoSpec.hom ⟨y, hy⟩).asIdeal ↔ r ∈ RingHom.ker (pairAlgHom ψ w).toRingHom
      have h4 : (hV.isoSpec.hom ⟨y, hy⟩).asIdeal = (hV.primeIdealOf ⟨y, hy⟩).asIdeal := rfl
      rw [h4, ← hψ, RingHom.mem_ker]
      exact Iff.of_eq (congrArg (· = (0 : K)) (hpair r))
    rw [← h3]
    exact h2
  -- a chart of Y at y with coordinates functions on V
  obtain ⟨a, ha⟩ := exists_differentialsIndependentAt (N := n) hV y hy ψ hψ
  obtain ⟨cY', hycY', hcY'V, hcY'⟩ :=
    exists_etaleChart_of_differentialsIndependentAt hV y hy ψ hψ a ha
  -- coordinates of B at w on a basic open
  let ΓB : Γ((Spec (CommRingCat.of B)), ⊤) →ₐ[K] B :=
    { (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom with
      commutes' := fun k => by
        change (Scheme.ΓSpecIso (CommRingCat.of B)).hom (algebraMap K Γ((Spec (CommRingCat.of B)), ⊤) k) = _
        rw [specAlgebraOver_algebraMap]
        exact Iso.inv_hom_id_apply _ _ }
  let ΓBinv : B →ₐ[K] Γ((Spec (CommRingCat.of B)), ⊤) :=
    { (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom with
      commutes' := fun k => (specAlgebraOver_algebraMap B k).symm }
  have hΓB : ∀ c, ΓBinv (ΓB c) = c := fun c => by
    change (Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).hom c) = c
    exact Iso.hom_inv_id_apply _ _
  have hΓB' : ∀ c, ΓB (ΓBinv c) = c := fun c => by
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv c) = c
    exact Iso.inv_hom_id_apply _ _
  have hχB : ∀ c : Γ((Spec (CommRingCat.of B)), ⊤), (w.comp ΓB) c = 0 ↔
      c ∈ ((isAffineOpen_top (Spec (CommRingCat.of B))).primeIdealOf ⟨specAlgHomPoint w, trivial⟩).asIdeal := by
    intro c
    have h := mem_primeIdealOf_specAlgHomPoint_iff w (ΓB c)
    change ΓBinv (ΓB c) ∈ _ ↔ _ at h
    rw [hΓB] at h
    exact h.symm
  obtain ⟨u', b', hb'0, hu'ind, hu'et⟩ :=
    exists_away_coordinates (N := d) (specAlgHomPoint w) (w.comp ΓB) hχB
  have hu : DifferentialsIndependentAt K w (ΓB ∘ u') := by
    have h := differentialsIndependentAt_of_comp ΓBinv (w.comp ΓB) (ΓB ∘ u')
      (by simpa [Function.comp_def, hΓB] using hu'ind)
    have hχ : (w.comp ΓB).comp ΓBinv = w := by
      ext c
      simp [hΓB']
    rwa [hχ] at h
  -- a chart of X at (y, w) with coordinates a_i ⊗ 1 and 1 ⊗ u_l
  let ΓX : Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤) →ₐ[K] (Γ(Y, V) ⊗[K] B) :=
    { (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).hom.hom with
      commutes' := fun k => by
        change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).hom (algebraMap K Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤) k) = _
        rw [specAlgebraOver_algebraMap]
        exact Iso.inv_hom_id_apply _ _ }
  let ΓXinv : (Γ(Y, V) ⊗[K] B) →ₐ[K] Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤) :=
    { (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv.hom with
      commutes' := fun k => (specAlgebraOver_algebraMap (Γ(Y, V) ⊗[K] B) k).symm }
  have hΓX : ∀ c, ΓX (ΓXinv c) = c := fun c => by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv c) = c
    exact Iso.inv_hom_id_apply _ _
  have hΓX' : ∀ c, ΓXinv (ΓX c) = c := fun c => by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).hom c) = c
    exact Iso.hom_inv_id_apply _ _
  let G : Fin (n + d) → (Γ(Y, V) ⊗[K] B) :=
    Fin.append (fun i => a i ⊗ₜ[K] (1 : B)) (fun l => (1 : Γ(Y, V)) ⊗ₜ[K] ΓB (u' l))
  have hG : DifferentialsIndependentAt K (pairAlgHom ψ w) G :=
    differentialsIndependentAt_tensor ψ w a (ΓB ∘ u') ha hu
  have hGX : DifferentialsIndependentAt K ((pairAlgHom ψ w).comp ΓX) (ΓXinv ∘ G) :=
    differentialsIndependentAt_of_comp ΓX (pairAlgHom ψ w) (ΓXinv ∘ G)
      (by simpa [Function.comp_def, hΓX] using hG)
  have hχX : ∀ c : Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤), ((pairAlgHom ψ w).comp ΓX) c = 0 ↔
      c ∈ ((isAffineOpen_top (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))).primeIdealOf ⟨p₀, trivial⟩).asIdeal := by
    intro c
    have h := mem_primeIdealOf_specAlgHomPoint_iff (pairAlgHom ψ w) (ΓX c)
    change ΓXinv (ΓX c) ∈ _ ↔ _ at h
    rw [hΓX'] at h
    exact h.symm
  obtain ⟨P, hp₀P, hPle, hP⟩ := exists_etaleChart_of_differentialsIndependentAt
    (isAffineOpen_top (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))) p₀ trivial ((pairAlgHom ψ w).comp ΓX) hχX (ΓXinv ∘ G) hGX
  have hPt₀ : ρ t₀ ∈ P.U := by
    rw [hρt₀]
    exact hτp.mem_open P.U.isOpen hp₀P
  -- the fibre chart at t₀
  have hprB : ∀ c, prB.appTop c = ΓXinv ((1 : Γ(Y, V)) ⊗ₜ[K] ΓB c) := by
    intro c
    conv_lhs => rw [← hΓB c]
    exact specMap_appTop_ΓSpecIso_inv _ _
  have hunit_of : ∀ c : Γ((Spec (CommRingCat.of B)), ⊤), w (ΓB c) ≠ 0 →
      IsUnit (T.presheaf.germ ⊤ t₀ trivial (φ' c)) := by
    intro c hc
    have hmem : p₀ ∈ (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).basicOpen (prB.appTop c) := by
      rw [mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))) p₀ trivial, ← hχX]
      change pairAlgHom ψ w (ΓX (prB.appTop c)) ≠ 0
      rw [hprB, hΓX, pairAlgHom_tmul, map_one, one_mul]
      exact hc
    have hmem' : ρ t₀ ∈ (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).basicOpen (prB.appTop c) := by
      rw [hρt₀]
      exact hτp.mem_open ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).basicOpen (prB.appTop c)).isOpen hmem
    have hu1 : IsUnit ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ (ρ t₀) trivial (prB.appTop c)) :=
      ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).mem_basicOpen (prB.appTop c) (ρ t₀) trivial).mp hmem'
    have h2 := hu1.map (ρ.stalkMap t₀).hom
    rwa [stalkMap_germ_top] at h2
  obtain ⟨F, hF, σF, hFsnc, hσF, hFcoord⟩ :=
    hfibprop t₀ (hunit_of hfib hwfib) u' b' (hunit_of b' hb'0) hu'et
  -- the stalk coordinates of the charts
  have hY' : (α ≫ ρ ≫ π) (eW : W.toScheme) ∈ cY'.U := by
    rw [heq]
    exact (specializes_iff_mem_closure.mpr hye).mem_open cY'.U.isOpen hycY'
  have hYV : (α ≫ ρ ≫ π) (eW : W.toScheme) ∈ V := hcY'V hY'
  have hstalkY : ∀ i, etaleChartStalkCoords cY' _ hY' (MvPolynomial.X i) =
      Y.presheaf.germ V _ hYV (a i) := by
    intro i
    change Y.presheaf.germ cY'.U _ hY' (cY'.coords (MvPolynomial.X i)) = _
    rw [hcY' i, TopCat.Presheaf.germ_res_apply]
  have hstalkP : ∀ k, etaleChartStalkCoords P _ hPt₀ (MvPolynomial.X k) =
      (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ _ trivial (ΓXinv (G k)) := by
    intro k
    change (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ P.U _ hPt₀ (P.coords (MvPolynomial.X k)) = _
    rw [hP k, TopCat.Presheaf.germ_res_apply]
    rfl
  have hcomp : ∀ z, ((α ≫ ρ ≫ π).stalkMap (eW : W.toScheme)) z =
      α.stalkMap (eW : W.toScheme) (ρ.stalkMap (α (eW : W.toScheme))
        (π.stalkMap (ρ (α (eW : W.toScheme))) z)) := by
    intro z
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    rfl
  have P1 : ∀ i : Fin n, schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (eW : W.toScheme)
      (etaleChartStalkCoords cY' _ hY' (MvPolynomial.X i)) =
      schemeStalkMapAlgHom (K := K) α (eW : W.toScheme) (schemeStalkMapAlgHom (K := K) ρ
        (α (eW : W.toScheme)) (etaleChartStalkCoords P _ hPt₀
          (MvPolynomial.X (Fin.castAdd d i)))) := by
    intro i
    rw [hstalkY i, hstalkP]
    change ((α ≫ ρ ≫ π).stalkMap (eW : W.toScheme)) (Y.presheaf.germ V _ hYV (a i)) =
      α.stalkMap (eW : W.toScheme) (ρ.stalkMap (α (eW : W.toScheme))
        ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ _ trivial (ΓXinv (G (Fin.castAdd d i)))))
    rw [hcomp]
    have h1 := stalkMap_specMap_includeLeft_fromSpec_germ hV B (ρ (α (eW : W.toScheme))) hYV
      (a i)
    refine congrArg (fun z => ConcreteCategory.hom (α.stalkMap (eW : W.toScheme))
      (ConcreteCategory.hom (ρ.stalkMap (α (eW : W.toScheme))) z)) (h1.trans ?_)
    simp [G, ΓXinv, Fin.append_left]
  have P2 : ∀ l : Fin d, schemeStalkMapAlgHom (K := K) ρ (α (eW : W.toScheme))
      (etaleChartStalkCoords P _ hPt₀ (MvPolynomial.X (Fin.natAdd n l))) =
      etaleChartStalkCoords F _ hF (MvPolynomial.X (Fin.natAdd n l)) := by
    intro l
    rw [hstalkP, hFcoord l]
    change ρ.stalkMap (α (eW : W.toScheme)) ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ _ trivial
      (ΓXinv (G (Fin.natAdd n l)))) = T.presheaf.germ ⊤ _ trivial (φ' (u' l))
    rw [stalkMap_germ_top]
    congr 1
    change ρ.appTop (ΓXinv (G (Fin.natAdd n l))) = ρ.appTop (prB.appTop (u' l))
    rw [hprB]
    simp [G, Fin.append_right]
  have happ : ∀ t, (α ≫ ρ).appTop t =
      W.ι.appTop ((σ ∣_ V).appTop (hV.isoSpec.hom.appTop (ιw.appTop t))) := by
    intro t
    rw [hα]
    rfl
  have P3 : ∀ l : Fin d, ∃ κ : K, schemeStalkMapAlgHom (K := K) α (eW : W.toScheme)
      (etaleChartStalkCoords F _ hF (MvPolynomial.X (Fin.natAdd n l))) = algebraMap K _ κ := by
    intro l
    refine ⟨w (ΓB (u' l)), ?_⟩
    rw [hFcoord l]
    change α.stalkMap (eW : W.toScheme) (T.presheaf.germ ⊤ _ trivial
      (ρ.appTop (prB.appTop (u' l)))) = _
    rw [stalkMap_germ_top]
    have hιw : ιw.appTop (prB.appTop (u' l)) =
        ιw.appTop (algebraMap K Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤) (w (ΓB (u' l)))) := by
      rw [hprB, specAlgebraOver_algebraMap]
      change ιw.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv _) =
        ιw.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv _)
      rw [specMap_appTop_ΓSpecIso_inv, specMap_appTop_ΓSpecIso_inv]
      congr 1
      change fibreAt w ((1 : Γ(Y, V)) ⊗ₜ[K] ΓB (u' l)) =
        fibreAt w (algebraMap K (Γ(Y, V) ⊗[K] B) (w (ΓB (u' l))))
      rw [fibreAt_tmul, one_mul, AlgHom.commutes]
    have hs : α.appTop (ρ.appTop (prB.appTop (u' l))) =
        (α ≫ ρ).appTop (algebraMap K Γ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))), ⊤) (w (ΓB (u' l)))) := by
      change (α ≫ ρ).appTop (prB.appTop (u' l)) = _
      rw [happ, happ, hιw]
    rw [hs, ← stalkMap_germ_top, germ_top_algebraMap]
    exact (schemeStalkMapAlgHom (K := K) (α ≫ ρ) (eW : W.toScheme)).commutes _
  -- the log discrepancy inequality along e
  obtain ⟨cW₀, -⟩ : ∃ c : EtaleChart K W.toScheme n, (eW : W.toScheme) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
      Opens.mem_top _)
  have hcore := fibre_snc_discrepancy_le α ρ hρ π hσ' cX cT cY cW₀ ξ hinj hcoh hsnc hbrcd_supp
    eW F hF σF hFsnc hσF P hPt₀ cY' hY' P1 P2 P3
  -- the log discrepancy of the test model along e
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + d) _
  have : Smooth (W.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨cU'₀, -⟩ : ∃ c : EtaleChart K U'.toScheme n, (e' : U'.toScheme) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := U'.toScheme) (n := n)).symm ▸
      Opens.mem_top _)
  have hlogW : cartierCoefficient (birationalRelativeCanonicalDivisor n (α ≫ ρ ≫ π) hσ' cY
      etaleCharts_cover cW₀ etaleCharts_cover) (eW : W.toScheme) = cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU etaleCharts_cover) (e : U) := by
    have h1 : cartierCoefficient (birationalRelativeCanonicalDivisor n (α ≫ ρ ≫ π) hσ' cY
        etaleCharts_cover cW₀ etaleCharts_cover) (eW : W.toScheme) =
        cartierCoefficient (logDiscrepancyDivisor n (α ≫ ρ ≫ π) hσ' cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          cW₀ etaleCharts_cover) (eW : W.toScheme) := by
      rw [logDiscrepancyDivisor_boundary_zero, cartierCoefficient_nsmul]
      simp
    rw [h1, logDiscrepancyDivisor_congr_hom heq hσ' hσW,
      logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective (U'.ι ≫ σ) W.ι hσU' hWι cY
        1 1 _ cU'₀ cW₀ eW e'.property hbijW]
    exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ U'.ι hσ hU'ι cY 1 1 _
      cU cU'₀ e' e.property hbij
  rw [hlogW] at hcore
  -- the members of the family along e
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have : IsDiscreteValuationRing (W.toScheme.presheaf.stalk (eW : W.toScheme)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eW
  have : IsDiscreteValuationRing (U.presheaf.stalk (U'.ι (e' : U'.toScheme))) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨U'.ι (e' : U'.toScheme), e.property⟩ : CodimensionOnePoint U)
  have : IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (W.ι (eW : W.toScheme))) :=
    ‹IsDiscreteValuationRing (U'.toScheme.presheaf.stalk (e' : U'.toScheme))›
  haveI : Nonempty (⊤ : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have hιwj : ∀ j, ιw.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv
      (fibreAt w (g j) ⊗ₜ[K] (1 : B))) =
      ιw.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)) := by
    intro j
    rw [specMap_appTop_ΓSpecIso_inv, specMap_appTop_ΓSpecIso_inv]
    congr 1
    change fibreAt w (fibreAt w (g j) ⊗ₜ[K] (1 : B)) = fibreAt w (g j)
    rw [fibreAt_tmul, map_one, map_one, mul_one]
  have hqval : ∀ j, algebraMap (W.toScheme.presheaf.stalk (eW : W.toScheme))
      W.toScheme.functionField (α.stalkMap (eW : W.toScheme) (T.presheaf.germ ⊤ (α (eW : W.toScheme)) trivial (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j))))) =
      dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)
        (Y.germToFunctionField V (fibreAt w (g j))) := by
    intro j
    rw [← Y.algebraMap_germ_eq_germToFunctionField hYV]
    change _ = (dominantFunctionFieldMap (α ≫ ρ ≫ π)).hom _
    rw [dominantFunctionFieldMap_algebraMap (α ≫ ρ ≫ π) (eW : W.toScheme)]
    congr 1
    rw [hcomp]
    have h2 : α.stalkMap (eW : W.toScheme) (ρ.stalkMap (α (eW : W.toScheme))
        (π.stalkMap (ρ (α (eW : W.toScheme))) (Y.presheaf.germ V _ hYV (fibreAt w (g j))))) =
        α.stalkMap (eW : W.toScheme) (ρ.stalkMap (α (eW : W.toScheme))
          ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).presheaf.germ ⊤ (ρ (α (eW : W.toScheme))) trivial
            ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (fibreAt w (g j) ⊗ₜ[K] (1 : B))))) :=
      congrArg (fun z => ConcreteCategory.hom (α.stalkMap (eW : W.toScheme))
        (ConcreteCategory.hom (ρ.stalkMap (α (eW : W.toScheme))) z))
        (stalkMap_specMap_includeLeft_fromSpec_germ hV B (ρ (α (eW : W.toScheme))) hYV
          (fibreAt w (g j)))
    refine Eq.trans ?_ h2.symm
    rw [stalkMap_germ_top, stalkMap_germ_top, stalkMap_germ_top]
    congr 1
    change (α ≫ ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)) =
      (α ≫ ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (fibreAt w (g j) ⊗ₜ[K] (1 : B)))
    rw [happ, happ, hιwj]
  have hordj : ∀ j, U.ord ((dominantFunctionFieldMap σ).hom
      (Y.germToFunctionField V (fibreAt w (g j)))) (e : U) =
      fibreOrd α (eW : W.toScheme) (T.presheaf.germ ⊤ (α (eW : W.toScheme)) trivial (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)))) := by
    intro j
    unfold fibreOrd
    rw [hqval j, dominantFunctionFieldAlgHom_congr_hom heq, dominantFunctionFieldAlgHom_comp,
      AlgHom.comp_apply, dominantFunctionFieldAlgHom_comp, AlgHom.comp_apply]
    exact ((scheme_ord_pullback_of_stalkMap_bijective W.ι eW e'.property hbijW _).trans
      (scheme_ord_pullback_of_stalkMap_bijective U'.ι e' e.property hbij
        (dominantFunctionFieldAlgHom (K := K) σ (Y.germToFunctionField V (fibreAt w (g j)))))).symm
  have hqne : ∀ j : J', α.stalkMap (eW : W.toScheme) (T.presheaf.germ ⊤ (α (eW : W.toScheme)) trivial (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j.1)))) ≠ 0 := by
    intro j h0
    have h1 := hqval j.1
    rw [h0, map_zero] at h1
    have h2 : Y.germToFunctionField V (fibreAt w (g j.1)) = 0 :=
      (map_eq_zero_iff _ (dominantFunctionFieldAlgHom (K := K)
        (α ≫ ρ ≫ π)).toRingHom.injective).mp h1.symm
    exact hnzprop j w (hwnz j)
      ((Scheme.germToFunctionField_injective Y V) (h2.trans (map_zero _).symm))
  have hqT : ∀ j : J', algebraMap (T.presheaf.stalk (α (eW : W.toScheme))) T.functionField
      (T.presheaf.germ ⊤ (α (eW : W.toScheme)) trivial (ρ.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j.1)))) ≠ 0 := by
    intro j h0
    apply hqne j
    rw [(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h0, map_zero]
  have hAq : ∀ j : J', (cartierPullback ρ (Adiv j)).IsLocalEquationAt (α (eW : W.toScheme))
      (Units.mk0 _ (hqT j)) := by
    intro j
    have h1 := cartierPullback_isLocalEquationAt ρ (Adiv j) (α (eW : W.toScheme))
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor (ρ (α (eW : W.toScheme))) (uX j))
    have h2 : Units.mk0 _ (hqT j) =
        Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (uX j) := by
      apply Units.ext
      rw [Units.val_mk0, Units.coe_map]
      change _ = (dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j.1)))
      rw [← (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).algebraMap_germ_eq_germToFunctionField
        (show ρ (α (eW : W.toScheme)) ∈ (⊤ : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).Opens) from trivial),
        dominantFunctionFieldMap_algebraMap, stalkMap_germ_top]
    rw [h2]
    exact h1
  -- a member of the family realising the principalized ideal at t₀
  obtain ⟨j₁, f₁, hGcf, hAf⟩ :=
    exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ Adiv hA Gc hGc
      hGcI (α (eW : W.toScheme))
  obtain ⟨u₁, hu₁⟩ := hAf.exists_unit_mul_eq (hAq j₁)
  have hGcq : Gc.IsLocalEquationAt (α (eW : W.toScheme)) (Units.mk0 _ (hqT j₁)) :=
    isLocalEquationAt_of_eq_unit_mul hGcf u₁ hu₁.symm
  have hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have hGsum := fibreOrd_snc_local_equation_of_ne_zero α eW hnorm F hF ξ hinj hcoh σF hFsnc Gc
    hGc0 (fun i => cartierCoefficient_nonneg_of_isEffective Gc hGc (ξ i)) _ (hqT j₁) hGcq
    (hqne j₁)
  -- the weighted inequality
  have hne₁ : Y.germToFunctionField V (fibreAt w (g j₁.1)) ≠ 0 := fun h0 =>
    hnzprop j₁ w (hwnz j₁)
      ((Scheme.germToFunctionField_injective Y V) (h0.trans (map_zero _).symm))
  have hb : (M : ℝ) * ((((1 : ℕ) : ℝ) + ((cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU etaleCharts_cover) (e : U) : ℤ) : ℝ)) / ((1 : ℕ) : ℝ)) ≤
      ((U.ord ((dominantFunctionFieldMap σ).hom
        (Y.germToFunctionField V (fibreAt w (g j₁.1)))) (e : U) : ℤ) : ℝ) :=
    hineq j₁.1 hne₁
  rw [hordj j₁.1, hGsum, Nat.cast_one, div_one] at hb
  rw [Nat.cast_one, div_one] at hApos
  have hbZ : (M : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU etaleCharts_cover) (e : U)) ≤ ∑ s, cartierCoefficient Gc (ξ s) * fibreSNCOrder α (eW : W.toScheme) F hF σF s := by
    exact_mod_cast hb
  have hAZ : 0 < 1 + cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU etaleCharts_cover) (e : U) := by exact_mod_cast hApos
  have hsum : (M : ℤ) * ∑ s, (1 + cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT etaleCharts_cover) (ξ s)) * fibreSNCOrder α (eW : W.toScheme) F hF σF s ≤ ∑ s, cartierCoefficient Gc (ξ s) * fibreSNCOrder α (eW : W.toScheme) F hF σF s :=
    (mul_le_mul_of_nonneg_left hcore (by positivity)).trans hbZ
  have hpos : 0 < ∑ s, cartierCoefficient Gc (ξ s) * fibreSNCOrder α (eW : W.toScheme) F hF σF s := by
    have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    nlinarith
  obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge
    (fun s => fibreSNCOrder_nonneg α (eW : W.toScheme) F hF σF s) hsum hpos
  have hs' : (M : ℤ) * (1 + cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT etaleCharts_cover) (ξ s)) ≤ cartierCoefficient Gc (ξ s) := hs
  have hts : α (eW : W.toScheme) ∈ closure ({ξ s} : Set T) := by
    by_contra hnot
    exact hos.ne' (fibreSNCOrder_eq_zero_of_notMem_closure α (eW : W.toScheme) F hF ξ σF hFsnc s
      hnot)
  -- the bad member is a bad test prime of X through (y, w)
  refine ⟨T, hTi, inferInstance, hTo, hTs, ρ, hdom, hover, hρ, cT, ⟨ξ s, hcoh s⟩, ?_, ?_, ?_⟩
  · have h1 : ρ (ξ s) ⤳ ρ (α (eW : W.toScheme)) :=
      (specializes_iff_mem_closure.mpr hts).map ρ.continuous
    have h2 : ρ (α (eW : W.toScheme)) ⤳ p₀ := by
      rw [show ρ (α (eW : W.toScheme)) = τ (e' : U'.toScheme) from hρt₀]
      exact hτp
    exact specializes_iff_mem_closure.mp (h1.trans h2)
  · have h0 := zeroBoundary_logDiscrepancy_coefficient_nonneg cX ρ hρ cT (ξ s)
    rw [Nat.cast_one, div_one]
    have h0' : (0 : ℝ) ≤ ((cartierCoefficient (logDiscrepancyDivisor (n + d) ρ hρ cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ))) cT etaleCharts_cover) (ξ s) : ℤ) : ℝ) := by exact_mod_cast h0
    linarith
  · intro j hj
    have hj' : g j ≠ 0 := fun h0 => hj (by
      show (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)) = 0
      rw [h0, map_zero, map_zero])
    have hordT : T.ord ((dominantFunctionFieldMap ρ).hom ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)))) (ξ s) =
        cartierCoefficient (cartierPullback ρ (Adiv ⟨j, hj'⟩)) (ξ s) := by
      change _ = cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))
        (uX ⟨j, hj'⟩))) (ξ s)
      rw [cartierPullback_principal, cartierCoefficient_principal]
      rfl
    have hmin1 := (hmin (ξ s)).1 ⟨j, hj'⟩
    have hk : cartierCoefficient (logDiscrepancyDivisor (n + d) ρ hρ cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ))) cT etaleCharts_cover) (ξ s) = cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT etaleCharts_cover) (ξ s) := by
      rw [logDiscrepancyDivisor_boundary_zero, cartierCoefficient_nsmul]
      simp
    have hfin : (M : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor (n + d) ρ hρ cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ))) cT etaleCharts_cover) (ξ s)) ≤ T.ord ((dominantFunctionFieldMap ρ).hom
        ((Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j)))) (ξ s) := by
      rw [hk, hordT]
      linarith
    rw [Nat.cast_one, div_one]
    exact_mod_cast hfin

end Assembly

section Conclusion

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- Generic restriction for products holds. -/
theorem genericRestrictionStatement_holds : GenericRestrictionStatement K := by
  intro Y _ _ _ n _ cY V hV _ B _ _ _ d _ _ _ cX J _ g M hn hM
  exact generic_restriction_of_product Y cY V hV B cX g M hn hM

/-- F1 from sum KV and restriction to fibres of products. -/
theorem mixedFujitaFreeness_of_kvSum_of_fibreRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hRI : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], FibreRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_restriction hKV hRI
    (fun _ _ _ _ => genericRestrictionStatement_holds)

/-- F1 from the usual KV, big plus nef and restriction to fibres of products. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_fibreRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hRI : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], FibreRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_restriction hKV hba hRI
    (fun _ _ _ _ => genericRestrictionStatement_holds)

end Conclusion

end MixedFujita
