/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModelPrimeOrders
public import MixedFujita.RelativeCanonicalEffectivity
public import MixedFujita.DVRJacobianOrderBound
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
public import MixedFujita.LogPairDenominatorScaling

/-!
Orders of a simple normal crossing family along a prime of a test model of a fibre (step 9,
generic restriction).

Let α : W → T map a smooth n-dimensional W into a smooth (n + d)-dimensional model T, not
necessarily dominantly, e a codimension-one point of W and F a simple normal crossing chart at
α(e). For a Cartier divisor of T supported on the family with a local equation q at α(e), the order
along e of the pullback of q is Σ_s (coefficient at ξ_s) o_s, where o_s is the order along e of the
pullback of the coordinate of ξ_s (`fibreOrd_snc_local_equation`): pull back the local product.

Let moreover ρ : T → X be birational with relative canonical divisor supported on the family and
π : X → Y with α ≫ ρ ≫ π dominant and birational onto a smooth n-dimensional Y. If the first n
coordinates of a chart P of X at ρ(α(e)) are pulled back from a chart of Y by π, its last d
coordinates pull back by ρ to the last d coordinates of F, and these pull back by α to constants
(F is a fibre chart), then the log discrepancies satisfy
Σ_s (1 + k_s) o_s ≤ 1 + (discrepancy of α ≫ ρ ≫ π at e) (`fibre_snc_discrepancy_le`).
The Jacobian of ρ in the charts P, F is block triangular with the identity in the base block, so
the Jacobian of α ≫ ρ ≫ π is the pullback of the Jacobian of ρ times the Jacobian of the pulled
back fibre coordinates (chain rule; the base coordinates are constant on W), and the latter has
order at least Σ o_s - 1 (logarithmic poles).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section LocalProduct

variable {K : Type u} [Field K] {N : ℕ} {T W : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [IsIntegral W] [IsLocallyNoetherian W]
  (α : W ⟶ T)

/-- The order along a point of W of the pullback of a germ at its image. -/
noncomputable def fibreOrd (e : W) (q : T.presheaf.stalk (α e)) : ℤ :=
  W.ord (algebraMap (W.presheaf.stalk e) W.functionField (α.stalkMap e q)) e

/-- The order along e of the pullback of the coordinate of a member of the family, zero when the
member misses the chart. -/
noncomputable def fibreSNCOrder (e : W) (F : EtaleChart K T N) (hF : α e ∈ F.U) {r : ℕ}
    (σF : Fin r → Option (Fin N)) (s : Fin r) : ℤ :=
  (σF s).elim 0 fun a => fibreOrd α e (etaleChartStalkCoords F (α e) hF (MvPolynomial.X a))

variable [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]

/-- The order along a prime of W of the pullback of a local equation of a divisor supported on the
simple normal crossing family is the weighted sum of the orders of the member coordinates. -/
theorem fibreOrd_snc_local_equation (e : CodimensionOnePoint W)
    [IsDiscreteValuationRing (W.presheaf.stalk (e : W))]
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (F : EtaleChart K T N) (hF : α (e : W) ∈ F.U) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σF : Fin r → Option (Fin N)) (hFsnc : IsSNCChart F ξ σF) (D : CartierDivisor T)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient D (z : T) = 0)
    (hnonneg : ∀ i, 0 ≤ cartierCoefficient D (ξ i)) (q : T.presheaf.stalk (α (e : W)))
    (hq : algebraMap (T.presheaf.stalk (α (e : W))) T.functionField q ≠ 0)
    (hloc : D.IsLocalEquationAt (α (e : W)) (Units.mk0 _ hq))
    (hcoord : ∀ s a, σF s = some a →
      α.stalkMap (e : W) (etaleChartStalkCoords F (α (e : W)) hF (MvPolynomial.X a)) ≠ 0) :
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
  -- pull back along α and take orders
  have hzs : ∀ s, α.stalkMap (e : W) (z s) ≠ 0 := by
    intro s
    cases hs : σF s with
    | none => simp [z, hs]
    | some a => simpa [z, hs] using hcoord s a hs
  let v : Fin r → W.functionFieldˣ := fun s => Units.mk0
    (algebraMap (W.presheaf.stalk (e : W)) W.functionField (α.stalkMap (e : W) (z s)))
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hzs s))
  have hunit : IsUnit (α.stalkMap (e : W) ((u' * u : (T.presheaf.stalk (α (e : W)))ˣ) :
      T.presheaf.stalk (α (e : W)))) := (Units.isUnit _).map _
  have hval : algebraMap (W.presheaf.stalk (e : W)) W.functionField (α.stalkMap (e : W) q) =
      algebraMap (W.presheaf.stalk (e : W)) W.functionField hunit.unit *
        ((∏ s, v s ^ cartierCoefficient D (ξ s) : W.functionFieldˣ) : W.functionField) := by
    rw [hq', map_mul, map_prod, map_mul, IsUnit.unit_spec, Units.coe_prod, map_prod]
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
  congr 1
  unfold fibreSNCOrder
  cases hs : σF s with
  | none => simp [v, z, hs]
  | some a => simp [v, z, hs, fibreOrd]

end LocalProduct

section ChainRule

variable {K : Type u} [Field K]

/-- The chain rule for étale coordinate derivations of different dimensions:
∂^z_k(ψ s) = Σ_j ψ(∂^y_j s) ∂^z_k(ψ y_j). -/
theorem etaleCoordinateDerivation_chainRule_of_dims {S T' : Type*} [CommRing S] [Algebra K S]
    [CommRing T'] [Algebra K T'] {N m : ℕ} (ψ : S →ₐ[K] T') (y : MvPolynomial (Fin N) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin m) K →ₐ[K] T')
    (hz : z.toRingHom.FormallyEtale) (k : Fin m) (s : S) :
    etaleCoordinateDerivation z hz k (ψ s) =
      ∑ j, ψ (etaleCoordinateDerivation y hy j s) *
        etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))) := by
  let _ : Algebra S T' := ψ.toRingHom.toAlgebra
  have : IsScalarTower K S T' := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  let d₁ : Derivation K S T' := (etaleCoordinateDerivation z hz k).compAlgebraMap S
  let d₂ : Derivation K S T' := ∑ j, (LinearMap.id.smulRight
    (etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))))).compDer
      (etaleCoordinateDerivation y hy j)
  have hd₂ : ∀ s, d₂ s = ∑ j, ψ (etaleCoordinateDerivation y hy j s) *
      etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))) := by
    intro s
    have h := congr_fun (map_sum (Derivation.coeFnAddMonoidHom (R := K) (A := S) (M := T'))
      (fun j => (LinearMap.id.smulRight
        (etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))))).compDer
          (etaleCoordinateDerivation y hy j)) Finset.univ) s
    rw [Finset.sum_apply] at h
    exact h
  have h : d₁ = d₂ := derivation_ext_etaleCoordinates y hy fun i => by
    rw [hd₂]
    change etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X i))) = _
    simp_rw [etaleCoordinateDerivation_coordinate]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [ite_eq_right (Ne.symm hji), map_zero, zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi), ite_eq_left rfl, map_one, one_mul]
  rw [← hd₂, ← h]
  rfl

variable {n d : ℕ} {W T X Y : Scheme.{u}}
  [IsIntegral W] [IsLocallyNoetherian W] [W.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (W ↘ Spec (CommRingCat.of K))]
  [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (n + d) (T ↘ Spec (CommRingCat.of K))]
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (n + d) (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  (α : W ⟶ T) [α.IsOver (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))] [IsDominant (α ≫ ρ ≫ π)]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)))

include hρ hσ in
/-- The log discrepancy inequality along a prime of a test model of a fibre: if the chart P of X
is a product chart (its first n coordinates pulled back from Y by π, its last d pulled back by ρ to
the last d coordinates of the fibre chart F, which are constant along α), then
Σ_s (1 + k_s) o_s ≤ 1 + (discrepancy of α ≫ ρ ≫ π at e), with k_s the coefficients of the relative
canonical divisor of ρ and o_s the orders of the member coordinates of F along e. -/
theorem fibre_snc_discrepancy_le (cX : EtaleChart K X (n + d)) (cT : EtaleChart K T (n + d))
    (cY : EtaleChart K Y n) (cW : EtaleChart K W n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K (n + d) ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT
        etaleCharts_cover) (z : T) = 0)
    (e : CodimensionOnePoint W) (F : EtaleChart K T (n + d)) (hF : α (e : W) ∈ F.U)
    (σF : Fin r → Option (Fin (n + d))) (hFsnc : IsSNCChart F ξ σF)
    (hσF : ∀ k a, σF k = some a → (a : ℕ) < n)
    (P : EtaleChart K X (n + d)) (hP : ρ (α (e : W)) ∈ P.U)
    (cY' : EtaleChart K Y n) (hY' : (α ≫ ρ ≫ π) (e : W) ∈ cY'.U)
    (P1 : ∀ i : Fin n, schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (e : W)
        (etaleChartStalkCoords cY' _ hY' (MvPolynomial.X i)) =
      schemeStalkMapAlgHom (K := K) α (e : W) (schemeStalkMapAlgHom (K := K) ρ (α (e : W))
        (etaleChartStalkCoords P _ hP (MvPolynomial.X (Fin.castAdd d i)))))
    (P2 : ∀ l : Fin d, schemeStalkMapAlgHom (K := K) ρ (α (e : W))
        (etaleChartStalkCoords P _ hP (MvPolynomial.X (Fin.natAdd n l))) =
      etaleChartStalkCoords F _ hF (MvPolynomial.X (Fin.natAdd n l)))
    (P3 : ∀ l : Fin d, ∃ κ : K, schemeStalkMapAlgHom (K := K) α (e : W)
        (etaleChartStalkCoords F _ hF (MvPolynomial.X (Fin.natAdd n l))) = algebraMap K _ κ) :
    ∑ s, (1 + cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX
        etaleCharts_cover cT etaleCharts_cover) (ξ s)) * fibreSNCOrder α (e : W) F hF σF s ≤
      1 + cartierCoefficient (birationalRelativeCanonicalDivisor n (α ≫ ρ ≫ π) hσ cY
        etaleCharts_cover cW etaleCharts_cover) (e : W) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + d) _
  have : Smooth (W ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have : IsDiscreteValuationRing (W.presheaf.stalk (e : W)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) e
  obtain ⟨cW', hcW'⟩ : ∃ c : EtaleChart K W n, (e : W) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W) (n := n)).symm ▸
      Opens.mem_top (e : W))
  -- notation
  set ψα := schemeStalkMapAlgHom (K := K) α (e : W) with hψα
  set ψρ := schemeStalkMapAlgHom (K := K) ρ (α (e : W)) with hψρ
  set f := etaleChartStalkCoords F (α (e : W)) hF with hfdef
  have hf := etaleChartStalkCoords_formallyEtale F (α (e : W)) hF
  set p := etaleChartStalkCoords P (ρ (α (e : W))) hP with hpdef
  set yY := etaleChartStalkCoords cY' ((α ≫ ρ ≫ π) (e : W)) hY' with hyYdef
  set c := etaleChartStalkCoords cW' (e : W) hcW' with hcdef
  have hc := etaleChartStalkCoords_formallyEtale cW' (e : W) hcW'
  -- the n × n block of the Jacobian of ρ
  let Nm : Matrix (Fin n) (Fin n) (T.presheaf.stalk (α (e : W))) := Matrix.of fun i i' =>
    etaleCoordinateDerivation f hf (Fin.castAdd d i') (ψρ (p (MvPolynomial.X (Fin.castAdd d i))))
  have hJρ : (etaleRelativeJacobian ψρ p f hf).det = Nm.det := by
    let B : Matrix (Fin n) (Fin d) (T.presheaf.stalk (α (e : W))) := Matrix.of fun i l =>
      etaleCoordinateDerivation f hf (Fin.natAdd n l) (ψρ (p (MvPolynomial.X (Fin.castAdd d i))))
    have hblock : (etaleRelativeJacobian ψρ p f hf).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks Nm B 0 1 := by
      ext (i | l) (i' | l')
      · simp [etaleRelativeJacobian, Nm]
      · simp [etaleRelativeJacobian, B]
      · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
          etaleRelativeJacobian, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        rw [P2 l, etaleCoordinateDerivation_coordinate, ite_eq_right_iff]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, etaleRelativeJacobian,
          Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
        rw [P2 l, etaleCoordinateDerivation_coordinate]
        simp only [Fin.natAdd_inj]
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
  -- the Jacobian of α ≫ ρ ≫ π factors
  let Q : Matrix (Fin n) (Fin n) (W.presheaf.stalk (e : W)) := Matrix.of fun i' j =>
    etaleCoordinateDerivation c hc j (ψα (f (MvPolynomial.X (Fin.castAdd d i'))))
  have hJσ : (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (e : W)) yY c
      hc).det = ψα Nm.det * Q.det := by
    have hmat : etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (e : W)) yY c
        hc = (ψα : _ →+* _).mapMatrix Nm * Q := by
      ext i j
      simp only [etaleRelativeJacobian, Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, Nm, Q]
      rw [P1 i, etaleCoordinateDerivation_chainRule_of_dims ψα f hf c hc j,
        Fin.sum_univ_add]
      have hzero : ∀ l : Fin d, ψα (etaleCoordinateDerivation f hf (Fin.natAdd n l)
          (ψρ (p (MvPolynomial.X (Fin.castAdd d i))))) * etaleCoordinateDerivation c hc j
            (ψα (f (MvPolynomial.X (Fin.natAdd n l)))) = 0 := by
        intro l
        obtain ⟨κ, hκ⟩ := P3 l
        rw [hκ, Derivation.map_algebraMap, mul_zero]
      simp only [hzero, Finset.sum_const_zero, add_zero]
      rfl
    rw [hmat, Matrix.det_mul, ← RingHom.map_det]
    rfl
  -- the Jacobian of α ≫ ρ ≫ π is a unit, so the factors are nonzero
  have hRσ := isUnit_chartRelativeJacobianDet_of_bijective (α ≫ ρ ≫ π) hσ cY' cW'
  have hJσeq := (chartRelativeJacobianDet_eq_stalk (α ≫ ρ ≫ π) (e : W) cY' hY' cW' hcW').trans
    (congrArg (stalkFunctionFieldAlgHom (K := K) (e : W)) hJσ)
  have hprod0 : ψα Nm.det * Q.det ≠ 0 := by
    intro h0
    apply hRσ.ne_zero
    rw [hJσeq, h0, map_zero]
  have hN0 : ψα Nm.det ≠ 0 := left_ne_zero_of_mul hprod0
  have hQ0 : Q.det ≠ 0 := right_ne_zero_of_mul hprod0
  have hrow : ∀ i', ψα (f (MvPolynomial.X (Fin.castAdd d i'))) ≠ 0 := by
    intro i' h0
    apply hQ0
    apply Matrix.det_eq_zero_of_row_eq_zero i'
    intro j
    simp only [Q, Matrix.of_apply, h0, map_zero]
  -- the coefficient at e is the order of the Jacobian
  have hlocσ := relativeCanonicalDivisor_isLocalEquationAt (α ≫ ρ ≫ π) cY etaleCharts_cover cW
    etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective (α ≫ ρ ≫ π) hσ cY cW)
    (e : W) cY' hY' cW' hcW'
  have hcoefσ : cartierCoefficient (birationalRelativeCanonicalDivisor n (α ≫ ρ ≫ π) hσ cY
      etaleCharts_cover cW etaleCharts_cover) (e : W) =
      W.ord (algebraMap (W.presheaf.stalk (e : W)) W.functionField (ψα Nm.det * Q.det)) (e : W) := by
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord hlocσ, IsUnit.unit_spec, hJσeq]
    rfl
  -- the order of the pulled back Jacobian of ρ
  have hRρ := isUnit_chartRelativeJacobianDet_of_bijective ρ hρ cX cT
  have hlocρ := relativeCanonicalDivisor_isLocalEquationAt ρ cX etaleCharts_cover cT
    etaleCharts_cover hRρ (α (e : W)) P hP F hF
  have hJρeq := chartRelativeJacobianDet_eq_stalk ρ (α (e : W)) P hP F hF
  have hNalg : algebraMap (T.presheaf.stalk (α (e : W))) T.functionField Nm.det ≠ 0 := by
    have h1 := (isUnit_chartRelativeJacobianDet ρ cX cT hRρ P F).ne_zero
    rwa [hJρeq, hJρ] at h1
  have hlocρ' : (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT
      etaleCharts_cover).IsLocalEquationAt (α (e : W)) (Units.mk0 _ hNalg) := by
    unfold birationalRelativeCanonicalDivisor
    convert hlocρ using 1
    apply Units.ext
    rw [Units.val_mk0, IsUnit.unit_spec, hJρeq, hJρ]
    rfl
  have hcoord : ∀ s a, σF s = some a →
      α.stalkMap (e : W) (etaleChartStalkCoords F (α (e : W)) hF (MvPolynomial.X a)) ≠ 0 := by
    intro s a hsa
    have ha := hσF s a hsa
    have := hrow ⟨a, ha⟩
    have heq : Fin.castAdd d (⟨a, ha⟩ : Fin n) = a := Fin.ext rfl
    rw [heq] at this
    exact this
  have hLP := fibreOrd_snc_local_equation α e hnorm F hF ξ hinj hξ σF hFsnc
    (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT etaleCharts_cover)
    hsupp (fun i => cartierCoefficient_nonneg_of_isEffective _
      (birationalRelativeCanonicalDivisor_isEffective ρ hρ cX etaleCharts_cover cT
        etaleCharts_cover) (ξ i)) Nm.det hNalg hlocρ' hcoord
  -- the DVR bound for the fibre coordinates
  have hbound := dvr_derivation_jacobian_order_bound
    (fun j => etaleCoordinateDerivation c hc j)
    (fun i' => ψα (f (MvPolynomial.X (Fin.castAdd d i')))) hrow
  choose m hm hprime using fun i' => scheme_regular_ringOrd_and_primeOrd_nat e
    (ψα (f (MvPolynomial.X (Fin.castAdd d i')))) (hrow i')
  obtain ⟨k, hk, hkprime⟩ := scheme_regular_ringOrd_and_primeOrd_nat e Q.det hQ0
  change ∑ i', Ring.ord (W.presheaf.stalk (e : W)) (ψα (f (MvPolynomial.X (Fin.castAdd d i')))) ≤
    1 + Ring.ord (W.presheaf.stalk (e : W)) Q.det at hbound
  simp_rw [hm] at hbound
  rw [hk, ← Nat.cast_sum, ← Nat.cast_one, ← Nat.cast_add] at hbound
  have hnat : ∑ i', m i' ≤ 1 + k := by exact_mod_cast hbound
  -- the selected member coordinates
  let σ'' : Fin r → Option (Fin n) := fun s =>
    (σF s).bind fun a => if h : (a : ℕ) < n then some ⟨a, h⟩ else none
  have hσ''inj : ∀ i j a, σ'' i = some a → σ'' j = some a → i = j := by
    intro i j a hi hj
    have key : ∀ k, σ'' k = some a → σF k = some (Fin.castAdd d a) := by
      intro k hk
      cases hs : σF k with
      | none => simp [σ'', hs] at hk
      | some b =>
        simp only [σ'', hs, Option.bind_some] at hk
        split_ifs at hk with h
        · simp only [Option.some.injEq] at hk
          congr 1
          exact Fin.ext (by rw [← hk]; rfl)
    exact hFsnc.1 i j _ (key i hi) (key j hj)
  have hosel : ∀ s, fibreSNCOrder α (e : W) F hF σF s = (σ'' s).elim 0 (fun i' => (m i' : ℤ)) := by
    intro s
    unfold fibreSNCOrder
    cases hs : σF s with
    | none => simp [σ'', hs]
    | some a =>
      have ha := hσF s a hs
      simp only [Option.elim_some, σ'', hs, Option.bind_some, ha, ↓reduceDIte]
      rw [← hprime ⟨a, ha⟩]
      rfl
  have hsel := option_selected_sum_le σ'' hσ''inj (fun i' => (m i' : ℤ)) (fun i' => by positivity)
  simp_rw [← hosel] at hsel
  -- combine
  have hordsum : W.ord (algebraMap (W.presheaf.stalk (e : W)) W.functionField
      (ψα Nm.det * Q.det)) (e : W) = fibreOrd α (e : W) Nm.det + (k : ℤ) := by
    rw [map_mul, Scheme.ord_mul ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hN0)
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQ0), hkprime]
    rfl
  rw [hcoefσ, hordsum, hLP]
  have hsum1 : ∑ s, (1 + cartierCoefficient (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX
      etaleCharts_cover cT etaleCharts_cover) (ξ s)) * fibreSNCOrder α (e : W) F hF σF s =
      ∑ s, fibreSNCOrder α (e : W) F hF σF s + ∑ s, cartierCoefficient
        (birationalRelativeCanonicalDivisor (n + d) ρ hρ cX etaleCharts_cover cT
          etaleCharts_cover) (ξ s) * fibreSNCOrder α (e : W) F hF σF s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum1]
  have hcast : ((∑ i', m i' : ℕ) : ℤ) ≤ 1 + (k : ℤ) := by exact_mod_cast hnat
  push_cast at hcast
  linarith

end ChainRule

end MixedFujita
