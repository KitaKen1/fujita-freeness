/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PrimeDivisorGeneralPoints
public import MixedFujita.JacobianCriterionCharts
public import MixedFujita.CoordinateDivisorValuation
public import MixedFujita.DivisorialLogDiscrepancy
public import MixedFujita.GeometricJacobianBound
public import MixedFujita.CartierWeilVanishingOrder
public import MixedFujita.SmoothClosedPoints
public import MixedFujita.SmoothProperCurveSections
public import MixedFujita.KltPairs
public import MixedFujita.ProperBirationalSections
public import MixedFujita.CartierAmpleDefinition

/-!
The order along a prime divisor of a smooth variety is a monomial test valuation at an adapted
closed point, and the bound of Lemma 1 for prime divisors (steps 6 and 11, sections 1 and 3.1 of
the manuscript).

* Algebra. If the localization of a ring at a finitely generated prime 𝔭 is a discrete valuation
  ring, there are h ∈ 𝔭 and s ∉ 𝔭 such that h generates the maximal ideal of the localization and
  s 𝔭 ⊆ (h): on the basic open of s the prime is cut out by h.
* Geometry. Let e be a codimension-one point of a smooth variety U over an algebraically closed
  field of characteristic zero. There are a closed point q in the closure of e, an étale chart at
  q, an index j and completion coordinates at q sending the centred chart coordinates to the
  variables, such that for every nonzero germ g at q the order of g along e is the weighted order
  of the Taylor expansion of g for the weight 1 on X_j and 0 on the other variables: the j-th
  coordinate is a local equation of the closure of e at q. Nothing is assumed about the divisor.
* Consequence (lct ≥ 1/mult along a prime divisor). For a birational morphism σ : U → Y of smooth
  varieties and a prime divisor e of U there is a closed point x of Y in the closure of σ(e) such
  that for every Cartier divisor D of Y and nonzero section s of D,

    ord_e(σ* div s) ≤ (1 + ord_e(K_{U/Y})) · mult_x(s).

  This is Lemma 1 of the manuscript for the divisorial valuation of e, obtained from the Jacobian
  bound for monomial test valuations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Algebra

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- A local equation of a prime whose localization is a discrete valuation ring: if 𝔭 is finitely
generated and the localization at 𝔭 is a discrete valuation ring, some h ∈ 𝔭 generates the maximal
ideal of the localization and some s ∉ 𝔭 multiplies 𝔭 into (h). -/
theorem exists_local_equation_of_dvr_localization (𝔭 : Ideal A) [𝔭.IsPrime]
    [IsLocalization.AtPrime S 𝔭] [IsDomain S] [IsDiscreteValuationRing S] (hfg : 𝔭.FG) :
    ∃ h ∈ 𝔭, ∃ s, s ∉ 𝔭 ∧ IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S h} ∧
      ∀ a ∈ 𝔭, ∃ b, s * a = h * b := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hmax : IsLocalRing.maximalIdeal S = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl ϖ
  have hspec : ϖ * algebraMap A S (t : A) = algebraMap A S x := by
    rw [← hxt]
    exact IsLocalization.mk'_spec S x t
  have ht : IsUnit (algebraMap A S (t : A)) := IsLocalization.map_units S t
  have hgen : IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S x} := by
    rw [hmax]
    exact Ideal.span_singleton_eq_span_singleton.mpr ⟨ht.unit, by rw [IsUnit.unit_spec, hspec]⟩
  have hx : x ∈ 𝔭 := by
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 x).mp ?_
    rw [hgen]
    exact Ideal.mem_span_singleton_self _
  -- every element of 𝔭 is multiplied into (x) by an element outside 𝔭
  have hkill : ∀ a ∈ 𝔭, ∃ s, s ∉ 𝔭 ∧ ∃ b, s * a = x * b := by
    intro a ha
    have hmem : algebraMap A S a ∈ Ideal.span {algebraMap A S x} := by
      rw [← hgen]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 a).mpr ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
    obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
    have h1 : algebraMap A S (a * (v : A)) = algebraMap A S (x * b) := by
      rw [map_mul, map_mul, hy, mul_assoc, IsLocalization.mk'_spec]
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl S).mp h1
    refine ⟨(w : A) * (v : A), ?_, (w : A) * b, by linear_combination hw⟩
    exact fun hmem' => (𝔭.primeCompl.mul_mem w.2 v.2) hmem'
  obtain ⟨G, hG⟩ := hfg
  choose! sa hsa bb hbb using hkill
  refine ⟨x, hx, ∏ a ∈ G, sa a, ?_, hgen, ?_⟩
  · intro hprod
    obtain ⟨a, haG, ha⟩ := (Ideal.IsPrime.prod_mem_iff (p := 𝔭)).mp hprod
    exact hsa a (hG ▸ Ideal.subset_span haG) ha
  · intro a ha
    rw [← hG] at ha
    refine Submodule.span_induction (p := fun a _ => ∃ b, (∏ a ∈ G, sa a) * a = x * b)
      ?_ ?_ ?_ ?_ ha
    · intro g hg
      have hgp : g ∈ 𝔭 := hG ▸ Ideal.subset_span hg
      obtain ⟨c, hc⟩ : sa g ∣ ∏ a ∈ G, sa a := Finset.dvd_prod_of_mem _ hg
      exact ⟨c * bb g, by rw [hc]; linear_combination c * hbb g hgp⟩
    · exact ⟨0, by simp⟩
    · rintro a a' _ _ ⟨b, hb⟩ ⟨b', hb'⟩
      exact ⟨b + b', by linear_combination hb + hb'⟩
    · rintro r a _ ⟨b, hb⟩
      exact ⟨r * b, by rw [smul_eq_mul]; linear_combination r * hb⟩

end Algebra

section LocalEquation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A local equation of a prime divisor near its generic point: at a point e of an affine open V
whose local ring is a discrete valuation ring there are sections h and s of V, with s invertible at
e, such that the germ of h generates the maximal ideal at e and, at every specialization q of e in
V at which s is invertible, every germ at q vanishing at e is a multiple of the germ of h. -/
theorem exists_local_equation_at_dvr_point {V : X.Opens} (hV : IsAffineOpen V) (e : X)
    (he : e ∈ V) [IsDiscreteValuationRing (X.presheaf.stalk e)] :
    ∃ h s : Γ(X, V), e ∈ X.basicOpen s ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk e) = Ideal.span {X.presheaf.germ V e he h} ∧
      ∀ (q : X) (hq : q ∈ V), q ∈ X.basicOpen s → ∀ hsp : e ⤳ q, ∀ a : X.presheaf.stalk q,
        X.presheaf.stalkSpecializes hsp a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk e) →
          a ∈ Ideal.span {X.presheaf.germ V q hq h} := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨e, he⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk e) (hV.primeIdealOf ⟨e, he⟩).asIdeal :=
    hV.isLocalization_stalk (⟨e, he⟩ : V)
  have hNoeth : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨h, -, s, hs, hmax, hmul⟩ := exists_local_equation_of_dvr_localization
    (S := X.presheaf.stalk e) (hV.primeIdealOf ⟨e, he⟩).asIdeal (IsNoetherian.noetherian _)
  refine ⟨h, s, ?_, hmax, ?_⟩
  · rw [X.mem_basicOpen s e he]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk e)
      (hV.primeIdealOf ⟨e, he⟩).asIdeal s).mpr hs
  · intro q hq hqs hsp a ha
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q, hq⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk q) (hV.primeIdealOf ⟨q, hq⟩).asIdeal :=
      hV.isLocalization_stalk (⟨q, hq⟩ : V)
    obtain ⟨⟨a₀, t⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hV.primeIdealOf ⟨q, hq⟩).asIdeal.primeCompl a
    have hspec : IsLocalization.mk' (X.presheaf.stalk q) a₀ t *
        X.presheaf.germ V q hq (t : Γ(X, V)) = X.presheaf.germ V q hq a₀ :=
      IsLocalization.mk'_spec (X.presheaf.stalk q) a₀ t
    have hsp_germ : ∀ f : Γ(X, V), X.presheaf.stalkSpecializes hsp (X.presheaf.germ V q hq f) =
        X.presheaf.germ V e he f := fun f => TopCat.Presheaf.germ_stalkSpecializes_apply ..
    have h1 : X.presheaf.germ V e he a₀ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk e) := by
      rw [← hsp_germ a₀, ← hspec, map_mul]
      exact Ideal.mul_mem_right _ _ ha
    have ha₀ : a₀ ∈ (hV.primeIdealOf ⟨e, he⟩).asIdeal :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk e)
        (hV.primeIdealOf ⟨e, he⟩).asIdeal a₀).mp h1
    obtain ⟨b, hb⟩ := hmul a₀ ha₀
    have hsu : IsUnit (X.presheaf.germ V q hq s) := (X.mem_basicOpen s q hq).mp hqs
    have htu : IsUnit (X.presheaf.germ V q hq (t : Γ(X, V))) :=
      IsLocalization.map_units (X.presheaf.stalk q) t
    have hb' : X.presheaf.germ V q hq s * X.presheaf.germ V q hq a₀ =
        X.presheaf.germ V q hq h * X.presheaf.germ V q hq b := by
      rw [← map_mul, ← map_mul, hb]
    rw [Ideal.mem_span_singleton]
    refine ⟨X.presheaf.germ V q hq b * ↑hsu.unit⁻¹ * ↑htu.unit⁻¹, ?_⟩
    have e1 : IsLocalization.mk' (X.presheaf.stalk q) a₀ t =
        X.presheaf.germ V q hq a₀ * ↑htu.unit⁻¹ := by
      rw [← hspec, mul_assoc, IsUnit.mul_val_inv, mul_one]
    have e2 : X.presheaf.germ V q hq a₀ =
        X.presheaf.germ V q hq h * X.presheaf.germ V q hq b * ↑hsu.unit⁻¹ := by
      calc X.presheaf.germ V q hq a₀ =
          ↑hsu.unit⁻¹ * (X.presheaf.germ V q hq s * X.presheaf.germ V q hq a₀) := by
            rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
        _ = X.presheaf.germ V q hq h * X.presheaf.germ V q hq b * ↑hsu.unit⁻¹ := by
            rw [hb']
            ring
    change IsLocalization.mk' (X.presheaf.stalk q) a₀ t = _
    rw [e1, e2]
    ring

end LocalEquation

section AdaptedPoint

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

omit [IsLocallyNoetherian X] in
/-- The function field image of a germ at q is the image of its specialization to a
generization e of q. -/
theorem algebraMap_stalkSpecializes_functionField {e q : X} (hsp : e ⤳ q)
    (a : X.presheaf.stalk q) :
    algebraMap (X.presheaf.stalk e) X.functionField (X.presheaf.stalkSpecializes hsp a) =
      algebraMap (X.presheaf.stalk q) X.functionField a := by
  obtain ⟨W, hW, f, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty W := ⟨⟨q, hW⟩⟩
  have hWe : e ∈ W := hsp.mem_open W.isOpen hW
  rw [show X.presheaf.stalkSpecializes hsp (X.presheaf.germ W q hW f) =
      X.presheaf.germ W e hWe f from TopCat.Presheaf.germ_stalkSpecializes_apply ..,
    X.algebraMap_germ_eq_germToFunctionField hWe, X.algebraMap_germ_eq_germToFunctionField hW]

/-- The order along a prime divisor is a monomial test valuation at an adapted closed point: for a
codimension-one point e of a smooth variety there are a closed point q in the closure of e, an
étale chart at q and an index j such that, in all completion coordinates at q sending the centred
chart coordinates to the variables, the order along e of every nonzero germ at q is the weighted
order of its Taylor expansion for the weight 1 on X_j and 0 on the other variables. -/
theorem exists_adapted_closedPoint_ord_eq_weightedOrder (e : X) (he : Order.coheight e = 1) :
    ∃ (q : X) (_ : IsClosed ({q} : Set X)) (_ : e ⤳ q) (c' : EtaleChart K X n) (hq : q ∈ c'.U)
      (β' : X.presheaf.stalk q →ₐ[K] K) (j : Fin n),
      ∀ ep : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk q))
          (X.presheaf.stalk q) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ i, stalkTaylorExpansion q ep
          (etaleChartCenteredStalkCoords c' q hq β' (MvPolynomial.X i)) = MvPowerSeries.X i) →
        ∀ g : X.presheaf.stalk q, g ≠ 0 → ∃ k : ℕ,
          (stalkTaylorExpansion q ep g).weightedOrder (Pi.single j 1) = (k : ℕ∞) ∧
          X.ord (algebraMap (X.presheaf.stalk q) X.functionField g) e = (k : ℤ) := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk e) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint X)
  obtain ⟨c, hec⟩ : ∃ c : EtaleChart K X n, e ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸ Opens.mem_top e)
  obtain ⟨h, s, hes, hmax, hgen⟩ := exists_local_equation_at_dvr_point c.isAffine e hec
  -- the germ of h at the specializations of e
  have hgerm_e : ∀ (q : X) (hq : q ∈ c.U) (hsp : e ⤳ q),
      X.presheaf.stalkSpecializes hsp (X.presheaf.germ c.U q hq h) = X.presheaf.germ c.U e hec h :=
    fun q hq hsp => TopCat.Presheaf.germ_stalkSpecializes_apply ..
  have hhe : X.presheaf.germ c.U e hec h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk e) := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self _
  have hhe0 : X.presheaf.germ c.U e hec h ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (X.presheaf.stalk e)
    rw [hmax, h0, Ideal.span_singleton_eq_bot]
  have hmem : ∀ (q : X) (hq : q ∈ c.U) (_ : e ⤳ q),
      X.presheaf.germ c.U q hq h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q) := by
    intro q hq hsp
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map (X.presheaf.stalkSpecializes hsp).hom
    rw [show (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ c.U q hq h) =
      X.presheaf.germ c.U e hec h from hgerm_e q hq hsp] at hu'
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hhe)) hu'
  have hne0 : ∀ (q : X) (hq : q ∈ c.U) (_ : e ⤳ q), X.presheaf.germ c.U q hq h ≠ 0 := by
    intro q hq hsp h0
    apply hhe0
    rw [← hgerm_e q hq hsp, h0, map_zero]
  -- a closed point of the closure of e in the chart where h cuts out the closure
  obtain ⟨p, ⟨hpe, hpc, hps⟩, hpcl⟩ := nonempty_inter_closedPoints
    (Z := closure ({e} : Set X) ∩ ((c.U : Set X) ∩ (X.basicOpen s : Set X)))
    ⟨e, subset_closure rfl, hec, hes⟩
    (isClosed_closure.isLocallyClosed.inter (c.U.isOpen.inter (X.basicOpen s).isOpen).isLocallyClosed)
  have hpcl' : IsClosed ({p} : Set X) := mem_closedPoints_iff.mp hpcl
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) p hpcl'
  have hspp : e ⤳ p := specializes_iff_mem_closure.mpr hpe
  have := smoothScheme_stalk_isNoetherianRing (K := K) p
  obtain ⟨j, q, hqcl, hqe, ⟨hqc, hqs⟩, hqj⟩ := etaleChart_exists_adapted_closedPoint c p hpc β h e
    hspp (hmem p hpc hspp) (hne0 p hpc hspp) (hgen p hpc hps hspp)
    ((c.U : Set X) ∩ (X.basicOpen s : Set X)) (c.U.isOpen.inter (X.basicOpen s).isOpen) ⟨hec, hes⟩
  have hspq : e ⤳ q := specializes_iff_mem_closure.mpr hqe
  obtain ⟨β'⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) q hqcl
  have := smoothScheme_stalk_isNoetherianRing (K := K) q
  refine ⟨q, hqcl, hspq, etaleChartReplace c j h ⟨⟨q, hqj⟩⟩, hqj, β', j, fun ep hep g hg => ?_⟩
  -- the j-th variable is the Taylor expansion of the germ of h
  have hgermq : etaleChartStalkCoords (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩) q hqj
      (MvPolynomial.X j) = X.presheaf.germ c.U q hqc h := by
    change X.presheaf.germ (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).U q hqj
      ((etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).coords (MvPolynomial.X j)) = _
    rw [etaleChartReplace_coords_self]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have hβ : β' (X.presheaf.germ c.U q hqc h) = 0 := by
    have hm := hmem q hqc hspq
    rw [← rationalLocalPoint_ker β'] at hm
    exact hm
  have hXj : ep (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk q))
      (X.presheaf.stalk q)) (X.presheaf.germ c.U q hqc h)) = MvPowerSeries.X j := by
    have hcent := etaleChartCenteredStalkCoords_variable (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩) q hqj
      β' j
    have hα : rationalAffineGermPoint (U := (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).U) q hqj β'
        ((etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).coords (MvPolynomial.X j)) = 0 := by
      change β' (X.presheaf.germ (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).U q hqj
        ((etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).coords (MvPolynomial.X j))) = 0
      rw [show X.presheaf.germ (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).U q hqj
        ((etaleChartReplace c j h ⟨⟨q, hqj⟩⟩).coords (MvPolynomial.X j)) =
        etaleChartStalkCoords (etaleChartReplace c j h ⟨⟨q, hqj⟩⟩) q hqj (MvPolynomial.X j)
        from rfl, hgermq, hβ]
    rw [hα, map_zero, sub_zero, hgermq] at hcent
    have h1 := hep j
    rw [hcent, stalkTaylorExpansion_apply] at h1
    exact h1
  -- divisibility by powers of h is read off from the weighted order
  have hdiv : ∀ m : ℕ, (m : ℕ∞) ≤ (stalkTaylorExpansion q ep g).weightedOrder (Pi.single j 1) ↔
      X.presheaf.germ c.U q hqc h ^ m ∣ g := by
    intro m
    rw [natCast_le_weightedOrder_piSingle_iff, pow_dvd_iff_completion (X.presheaf.germ c.U q hqc h)
      g m, ← hXj, ← map_pow, stalkTaylorExpansion_apply]
    exact map_dvd_iff ep
  have hF0 : stalkTaylorExpansion q ep g ≠ 0 := by
    intro h0
    apply hg
    have hall : ∀ m : ℕ, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q) ^ m := by
      intro m
      have hd : X.presheaf.germ c.U q hqc h ^ m ∣ g := (hdiv m).mp (by rw [h0]; simp)
      obtain ⟨g₁, rfl⟩ := hd
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hmem q hqc hspq) m)
    have hbot : (⨅ m : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk q) ^ m) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hg0 : g ∈ (⨅ m : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk q) ^ m) :=
      Ideal.mem_iInf.mpr hall
    rw [hbot] at hg0
    exact hg0
  have hfin : (stalkTaylorExpansion q ep g).weightedOrder (Pi.single j 1) ≠ ⊤ :=
    (MvPowerSeries.weightedOrder_eq_top_iff _).not.mpr hF0
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨g', hg'⟩ := (hdiv k).mp (by rw [hk])
  have hnd : ¬ X.presheaf.germ c.U q hqc h ∣ g' := by
    rintro ⟨g'', hg''⟩
    have hd : X.presheaf.germ c.U q hqc h ^ (k + 1) ∣ g := ⟨g'', by rw [hg', hg'']; ring⟩
    have hle := (hdiv (k + 1)).mpr hd
    rw [← hk] at hle
    exact absurd (by exact_mod_cast hle : k + 1 ≤ k) (Nat.not_succ_le_self k)
  -- the cofactor is a unit at e
  have hunit : IsUnit (X.presheaf.stalkSpecializes hspq g') := by
    by_contra hnu
    exact hnd (Ideal.mem_span_singleton.mp (hgen q hqc hqs hspq g'
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))))
  -- the order at e
  have hsplit : X.presheaf.stalkSpecializes hspq g =
      X.presheaf.germ c.U e hec h ^ k * X.presheaf.stalkSpecializes hspq g' := by
    rw [hg', map_mul, map_pow, hgerm_e q hqc hspq]
  have hne : X.presheaf.stalkSpecializes hspq g ≠ 0 := by
    rw [hsplit]
    exact mul_ne_zero (pow_ne_zero _ hhe0) hunit.ne_zero
  have hord : localAdicOrder (X.presheaf.stalk e) (X.presheaf.stalkSpecializes hspq g) = k := by
    rw [localAdicOrder_eq_nat_iff, hmax, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hsplit]
    refine ⟨Ideal.mem_span_singleton.mpr ⟨_, rfl⟩, fun hmem' => ?_⟩
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hmem'
    have hcancel : X.presheaf.stalkSpecializes hspq g' = X.presheaf.germ c.U e hec h * v := by
      apply mul_left_cancel₀ (pow_ne_zero k hhe0)
      rw [hv]
      ring
    have hin : X.presheaf.stalkSpecializes hspq g' ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk e) := by
      rw [hcancel]
      exact Ideal.mul_mem_right _ _ hhe
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hin)) hunit
  refine ⟨k, hk.symm, ?_⟩
  rw [← algebraMap_stalkSpecializes_functionField hspq g]
  exact scheme_ord_regular_eq_localAdicOrder_nat (⟨e, he⟩ : CodimensionOnePoint X) _ hne k hord

end AdaptedPoint

section LemmaOne

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y U : Scheme.{u}}
  [IsIntegral Y] [IsIntegral U] [IsLocallyNoetherian U]
  [Y.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Lemma 1 along a prime divisor (lct ≥ 1/mult): for a birational morphism σ : U → Y of smooth
varieties and a prime divisor e of U there is a closed point x of Y in the closure of σ(e) such
that the relative canonical divisor has nonnegative coefficient at e and, for every Cartier divisor
D of Y and nonzero section s, ord_e(σ* div s) ≤ (1 + ord_e(K_{U/Y})) mult_x(s). -/
theorem exists_closedPoint_cartierPullback_coefficient_le (c₀ : EtaleChart K Y n)
    (cU₀ : EtaleChart K U n) (e : CodimensionOnePoint U) :
    ∃ x : Y, IsClosed ({x} : Set Y) ∧ x ∈ closure ({σ (e : U)} : Set Y) ∧
      0 ≤ cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover cU₀
        etaleCharts_cover) (e : U) ∧
      ∀ (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0),
        cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U) ≤
          (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover
            cU₀ etaleCharts_cover) (e : U)) *
            ((cartierSectionVanishingOrder D x s).toNat : ℤ) := by
  classical
  have hsmY : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmU : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨q, hqcl, hsp, c', hq, β', j, htest⟩ :=
    exists_adapted_closedPoint_ord_eq_weightedOrder (K := K) (n := n) (e : U) e.property
  -- the image of the closed point is closed
  have hjacY : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (CommRingCat.of K))
  have hσft : LocallyOfFiniteType σ := by
    have : LocallyOfFiniteType (σ ≫ (Y ↘ Spec (CommRingCat.of K))) := by
      rw [HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K))]
      infer_instance
    exact locallyOfFiniteType_of_comp σ (Y ↘ Spec (CommRingCat.of K))
  have hxcl : IsClosed ({σ q} : Set Y) := mem_closedPoints_iff.mp
    (σ.closedPoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hqcl))
  have hspσ : σ (e : U) ⤳ σ q := hsp.map σ.continuous
  -- charts and completion coordinates
  obtain ⟨cY, hcY⟩ : ∃ cY : EtaleChart K Y n, σ q ∈ cY.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top (σ q))
  obtain ⟨ep, hep, hjac⟩ := etaleChart_testValuation_jacobian_weightedOrder σ q cY hcY c' hq
    (β'.comp (schemeStalkMapAlgHom (K := K) σ q)) β'
  obtain ⟨ez, -, -⟩ := etaleChart_exists_taylorCoordinates cY (σ q) hcY
    (β'.comp (schemeStalkMapAlgHom (K := K) σ q))
  have := smoothScheme_stalk_isNoetherianRing (K := K) (σ q)
  -- the Jacobian determinant and the relative canonical divisor at e
  have hΔimg : algebraMap (U.presheaf.stalk q) U.functionField
      (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) σ q)
        (etaleChartStalkCoords cY (σ q) hcY) (etaleChartStalkCoords c' q hq)
        (etaleChartStalkCoords_formallyEtale c' q hq)).det = chartRelativeJacobianDet σ cY c' :=
    (chartRelativeJacobianDet_eq_stalk σ q cY hcY c' hq).symm
  have hΔ0 : (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) σ q)
      (etaleChartStalkCoords cY (σ q) hcY) (etaleChartStalkCoords c' q hq)
      (etaleChartStalkCoords_formallyEtale c' q hq)).det ≠ 0 := by
    intro h0
    have hu := isUnit_chartRelativeJacobianDet_of_bijective σ hσ cY c'
    rw [← hΔimg, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨m, hm, hordm⟩ := htest ep hep _ hΔ0
  have hjacm : (powerSeriesJacobian (schemeCompletedStalkMap σ q ez ep)).det.weightedOrder
      (Pi.single j 1) = (m : ℕ∞) := by
    rw [hjac ez (Pi.single j 1)]
    exact hm
  have heU : (e : U) ∈ c'.U := hsp.mem_open c'.U.isOpen hq
  have hσe : σ (e : U) ∈ cY.U := hspσ.mem_open cY.U.isOpen hcY
  have hK : cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover cU₀
      etaleCharts_cover) (e : U) = (m : ℤ) := by
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt σ c₀
      etaleCharts_cover cU₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective σ hσ c₀ cU₀) (e : U) cY hσe c' heU),
      IsUnit.unit_spec, ← hΔimg]
    exact hordm
  refine ⟨σ q, hxcl, specializes_iff_mem_closure.mp hspσ, by rw [hK]; exact_mod_cast Nat.zero_le m,
    fun D s hs => ?_⟩
  have hL1 := cartierPullbackMonomialValuation_le D σ q ez ep (Pi.single j 1) hs
  -- the pulled back local coefficient of the section
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (σ q)
  have himg : algebraMap (Y.presheaf.stalk (σ q)) Y.functionField
      (cartierLocalCoefficient D (σ q) f hf s) =
      ((f * cartierSectionUnit D s hs : Y.functionFieldˣ) : Y.functionField) := by
    simpa only [Units.val_mul, cartierSectionUnit_val] using
      cartierLocalCoefficient_image D (σ q) f hf s
  have heq : (cartierSectionZeroDivisor D s hs).IsLocalEquationAt (σ q)
      (f * cartierSectionUnit D s hs) := cartierSectionZeroDivisor_localEquation D s hs (σ q) f hf
  have hgimg : algebraMap (U.presheaf.stalk q) U.functionField
      (σ.stalkMap q (cartierLocalCoefficient D (σ q) f hf s)) =
      ((Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom
        (f * cartierSectionUnit D s hs) : U.functionFieldˣ) : U.functionField) := by
    rw [← dominantFunctionFieldMap_algebraMap, himg]
    rfl
  have hg0 : σ.stalkMap q (cartierLocalCoefficient D (σ q) f hf s) ≠ 0 := by
    intro h0
    have h1 : algebraMap (U.presheaf.stalk q) U.functionField
        (σ.stalkMap q (cartierLocalCoefficient D (σ q) f hf s)) ≠ 0 := by
      rw [hgimg]
      exact Units.ne_zero _
    exact h1 (by rw [h0, map_zero])
  obtain ⟨k, hk, hordk⟩ := htest ep hep _ hg0
  -- the coefficient of the pullback of the zero divisor at e
  have hloc_e : (cartierPullback σ (cartierSectionZeroDivisor D s hs)).IsLocalEquationAt (e : U)
      (Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom (f * cartierSectionUnit D s hs)) := by
    obtain ⟨V, hqV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp
      (cartierPullback_isLocalEquationAt σ (cartierSectionZeroDivisor D s hs) q heq)
    exact CartierDivisor.isLocalEquationAt_iff.mpr ⟨V, hsp.mem_open V.isOpen hqV, hV⟩
  have hcoef : cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U) =
      (k : ℤ) := by
    rw [cartierCoefficient_eq_ord hloc_e, ← hgimg]
    exact hordk
  have hval : cartierPullbackMonomialValuation D σ q ep (Pi.single j 1) s = (k : ℕ∞) := by
    rw [cartierPullbackMonomialValuation_eq D σ q ep (Pi.single j 1) s f hf,
      cartierStalkPullbackCoefficient_apply, ← stalkTaylorExpansion_apply]
    exact hk
  have hsum : ((∑ i, (Pi.single j 1 : Fin n → ℕ) i : ℕ) : ℕ∞) = 1 := by
    rw [Finset.sum_pi_single']
    simp
  rw [hval, hjacm, hsum] at hL1
  obtain ⟨μ, hμ⟩ := ENat.ne_top_iff_exists.mp
    ((cartierSectionVanishingOrder_lt_top_iff D (σ q) s).mpr hs).ne
  rw [← hμ] at hL1 ⊢
  rw [hcoef, hK, ENat.toNat_natCast]
  exact_mod_cast hL1

end LemmaOne

section Ample

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 1 for the prime divisors over a smooth variety with an ample divisor A: one constant
c ≥ 1 such that for every smooth birational model σ : U → Y, every prime divisor e of U, every
j ≥ 1 and every nonzero section s of j A, ord_e(σ* div s) ≤ c j (1 + ord_e(K_{U/Y})). -/
theorem cartierIsAmpleProj_prime_coefficient_le {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
      [U.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
      (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (c₀ : EtaleChart K Y n) (cU₀ : EtaleChart K U n) (e : CodimensionOnePoint U) (j : ℕ),
      1 ≤ j → ∀ (s : Γ((j • A).sheaf, ⊤)) (hs : s ≠ 0),
        cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • A) s hs)) (e : U) ≤
          ((c * j : ℕ) : ℤ) * (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ
            c₀ etaleCharts_cover cU₀ etaleCharts_cover) (e : U)) := by
  have hsmY : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨c, hc⟩ := cartierIsAmpleProj_vanishingOrder_le (K := K) hn hd hA
  refine ⟨c + 1, Nat.le_add_left 1 c, fun U _ _ _ _ σ _ _ hσ c₀ cU₀ e j hj s hs => ?_⟩
  obtain ⟨x, hxcl, -, hK0, hle⟩ := exists_closedPoint_cartierPullback_coefficient_le σ hσ c₀ cU₀ e
  have hmult : (cartierSectionVanishingOrder (j • A) x s).toNat ≤ (c + 1) * j :=
    (ENat.toNat_le_of_le_natCast (hc x hxcl j hj s hs)).trans
      (Nat.mul_le_mul_right j (Nat.le_add_right c 1))
  have hmult' : ((cartierSectionVanishingOrder (j • A) x s).toNat : ℤ) ≤ (((c + 1) * j : ℕ) : ℤ) := by
    exact_mod_cast hmult
  calc cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (j • A) s hs)) (e : U)
      ≤ (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover
          cU₀ etaleCharts_cover) (e : U)) *
          ((cartierSectionVanishingOrder (j • A) x s).toNat : ℤ) := hle (j • A) s hs
    _ ≤ (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover
          cU₀ etaleCharts_cover) (e : U)) * (((c + 1) * j : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hmult' (by linarith)
    _ = (((c + 1) * j : ℕ) : ℤ) * (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ
          hσ c₀ etaleCharts_cover cU₀ etaleCharts_cover) (e : U)) := mul_comm _ _

end Ample

end MixedFujita
