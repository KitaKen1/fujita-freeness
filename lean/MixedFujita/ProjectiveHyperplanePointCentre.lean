/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveTangentChartExistence
public import MixedFujita.ProfilePolytopeWeight
public import MixedFujita.GlobalMinimizerData
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.ClosedPointsDenseOver

/-!
The conclusion of section 5 for the hyperplane class: along a degree sequence realizing the
liminf of the normalized infimum, the minimizing profile data eventually have the point-centre
property.

Let Y be a closed subscheme of projective space with hyperplane divisor J (cut by a form g not
vanishing at the closed point x), with a klt boundary. Fix s with s b = n + 1 and a > 0. Assume:

* every point w specializing to x has finite dimension at most n, and every such w other than x
  whose closure has dimension D' has degree at least s^D' (as the limit of D'! h^0(W, D J)/D^D');
* the specialization comparison (6) in open form: for every such w, every degree j and every t,
  the infima at the closed points of a neighbourhood of w in the closure of w are at least the
  infimum at x;
* the minimizing profile data have log discrepancy at least a.

Then there is t in [t₀, b) such that, for every degree sequence m_k → ∞ along which the
normalized infimum f_j = inf_j(x)/h^0(j J) tends to its liminf c > 0 (with h^0(j J)/j^n → ν > 0
and f bounded below), eventually every minimizing profile datum of degree m_k at x has the
point-centre property `SNCWeightProfileHasPointCentre`.

The theorem is proved as `projectiveHyperplane_pointCentre_along_sequence_of_dense`, in which (6)
is asked only at the closed points of a set G whose closed points are dense over each generization
of x (`ClosedPointsDenseOver`; for example an open set, or the complement of countably many proper
closed subsets over an uncountable field, as in section 2.3 of the manuscript). Its open form
`projectiveHyperplane_pointCentre_along_sequence` asks (6) and the
bound a ≤ A only for the large members of the degree sequence and the chosen t (in this form it
is used for the data of the minimizer, where the bound comes from the interior condition (7) at
those degrees); `projectiveHyperplane_eventually_pointCentre` is the form with both for all
degrees and all t.

Proof: the limit `exists_parameter_point_centers` excludes, eventually, the inequalities of one
degree for every positive dimension. A point of a model, not over x, whose closure meets the
fibre of x and whose polytope contains the normalized profile gives a weight with the same datum
supported on the members through it (`exists_weight_of_inSNCProfilePolytope`), whose centre has
an image of positive dimension; the chart data at a general closed point of that centre
(`projectiveHyperplane_exists_closedPoint_tangent_chart`) and the inequalities of one degree
(`projectiveHyperplane_centerDegreeInequalities`) contradict the limit.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [IsLocallyNoetherian Y] in
/-- The point-centre property along a degree sequence realizing the liminf, for the hyperplane
class, when the specialization comparison (6) holds at the closed points of a set G whose closed
points are dense over each generization w ≠ x of x (`ClosedPointsDenseOver`), and (6) and the
bound a ≤ A of the minimizing profile data are only known for the large members of the sequence
and the chosen t. -/
theorem projectiveHyperplane_pointCentre_along_sequence_of_dense
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    {dd : ℕ} (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (hdd : 1 ≤ dd)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY dd D₀)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hn : 0 < n) {a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = n + 1) (ht₀ : t₀ < b)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ n ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧
      ∀ {ν c : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
          atTop (𝓝 ν) →
        0 < c →
        liminf (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop = c →
        IsBoundedUnder (· ≥ ·) atTop (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) →
        ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
        Tendsto (fun k => sncWeightInfimum cY fY dd D₀
          (m k • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t (m k) /
            Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop (𝓝 c) →
        (∀ᶠ k in atTop, ∀ w : Y, w ⤳ x → w ≠ x → ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
          ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ G → w ⤳ y →
            sncWeightInfimum cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
                (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t
                (m k) ≤
              sncWeightInfimum cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) y
                (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t
                (m k)) →
        (∀ᶠ k in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
              B', (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
                ∑ i, Real.exp (p'.1 / t - p'.2 i / (m k : ℝ))) →
          a ≤ p.1) →
        ∀ᶠ k in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
              B', (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
                ∑ i, Real.exp (p'.1 / t - p'.2 i / (m k : ℝ))) →
          SNCWeightProfileHasPointCentre cY fY dd D₀
            (m k • projectiveHyperplaneCartier e g hg hggen) x B p := by
  obtain ⟨t, ht₀', ht, htb, l, hl, hlim⟩ :=
    exists_parameter_point_centers n hn ha hb (lam := (s : ℝ)) hsb ht₀
  refine ⟨t, ht₀', ht, htb, fun {ν c} hν hN hc hliminf hbdd m hm hfm h6ev hAev => ?_⟩
  -- the limit excludes the inequalities of one degree for every positive dimension
  have hev := hlim (fun j => Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) hν hN
    (fun j : ℕ => sncWeightInfimum cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    hc hliminf hbdd m hm hfm (fun D : ℕ => (s : ℝ) * ((s : ℝ) ^ D - 1) + (s : ℝ) * (D : ℕ))
    (fun _ => 0)
    (fun k D => ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities
      (fun j => Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
      (fun j : ℕ => sncWeightInfimum cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen)
        x (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
          Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
      t s ((s : ℝ) * ((s : ℝ) ^ D - 1) + (s : ℝ) * (D : ℕ)) a l (m k) D Q T A)
    (fun _ _ _ _ hP _ => hP)
  -- eventually the sections of m_k J are nonzero
  have hNpos : ∀ᶠ k in atTop, 0 < Module.finrank K
      Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    have h1 : ∀ᶠ j : ℕ in atTop, ν / 2 < (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n :=
      hN.eventually (lt_mem_nhds (half_lt_self hν))
    have h2 : ∀ᶠ j : ℕ in atTop, 0 < Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
      refine h1.mono fun j hj => Nat.pos_of_ne_zero fun h0 => ?_
      rw [h0, Nat.cast_zero, zero_div] at hj
      linarith
    exact hm.eventually h2
  -- eventually the degrees exceed the thresholds of all dimensions
  have hMev : ∀ᶠ k in atTop, l * (2 * s ^ n + 2 ^ n * n.factorial + n + s ^ n) ≤ m k :=
    hm.eventually (eventually_ge_atTop _)
  filter_upwards [hev, hNpos, hMev, h6ev, hAev] with k hk hNk hMk h6k hAk
  intro B p hp hpmin hBs X _ _ _ _ π _ _ _ hπ cX r ξ _ hinj hξ hsnc hBsupp hGsupp _ _ _ _ pt hpt
    hpoly
  by_contra hptx
  -- the datum of a minimizing profile has positive log discrepancy
  have hap : a ≤ p.1 := hAk B p hp hpmin
  have hp1 : 0 < p.1 := lt_of_lt_of_le ha hap
  -- the members of the model have positive log discrepancy
  have hApos : ∀ j, 0 < ((dd : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ j)) / dd := by
    intro j
    have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY dd D₀ hklt cX
      ⟨ξ j, hξ j⟩
    have h2 : ((cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ j) : ℤ) : ℝ) <
        (dd : ℝ) := by exact_mod_cast h1
    have hdd' : (0 : ℝ) < dd := by exact_mod_cast hdd
    exact div_pos (by linarith) hdd'
  -- a weight with the same datum on the members through pt
  obtain ⟨w', hw'0, hw'ne, hw'supp, hw'A, hw'v⟩ := exists_weight_of_inSNCProfilePolytope ξ dd
    (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover)
    (fun i => cartierPullback π (cartierSectionZeroDivisor
      (m k • projectiveHyperplaneCartier e g hg hggen) (B i) (hBs i))) p hp1 pt hApos hpoly
  -- the generic point of its stratum and the chart data
  obtain ⟨η, hη, hηpt, hmax, hall⟩ := projectiveHyperplane_exists_closedPoint_tangent_chart_dense π
    e he ξ hsnc w' pt hw'supp
  obtain ⟨q, hqpt, hqx⟩ := hpt
  have hqx' : π q = x := hqx
  have hptq : pt ⤳ q := specializes_iff_mem_closure.mpr hqpt
  have hηx : π η ⤳ x := by
    rw [← hqx']
    exact π.base.hom.map_specializes (hηpt.trans hptq)
  have hηne : π η ≠ x := by
    intro heq
    apply hptx
    have h1 : π η ⤳ π pt := π.base.hom.map_specializes hηpt
    rw [heq] at h1
    have h2 : π pt ∈ ({x} : Set Y) := by
      rw [← hxc.closure_eq]
      exact specializes_iff_mem_closure.mp h1
    exact h2
  -- a coordinate chart of projective space containing π(η)
  obtain ⟨i₀, hi₀⟩ := polynomialProjective_exists_coordinate_chart N K (e (π η))
  have hηk : π η ∈ projectivePullbackCoordinateOpen e i₀ := hi₀
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)},
      k₀.val = i₀ := ⟨⟨i₀, ⟨⟨π η, hηk⟩⟩⟩, rfl⟩
  have hηk₀ : π η ∈ projectivePullbackCoordinateOpen e k₀.val := by
    rw [hk₀]
    exact hηk
  -- the set of closed points of the specialization comparison, and a closed point over it
  obtain ⟨G, hGdense, hG6⟩ := h6k (π η) hηx hηne
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨z, hzcl, hηz, -, hzG, hzU, c, σc, hz, hηc, Tan, ez, hc, hez, hiff, hTanfree, hTanU,
    hsat, hTanne⟩ := hall k₀ hηk₀ Set.univ isOpen_univ (Set.mem_univ η) (π ⁻¹' G)
      fun O hO hηO => by
        obtain ⟨z', hzO, hzc, hzη, hzG'⟩ := hGdense X π η rfl O hO hηO
        exact ⟨z', hzG', hzc, hzη, hzO⟩
  -- π(z) is a closed point different from π(η)
  have hπzcl : IsClosed ({π z} : Set Y) := by
    have h1 := π.isClosedMap _ hzcl
    rwa [Set.image_singleton] at h1
  have hηz' : π η ⤳ π z := π.base.hom.map_specializes hηz
  have hneπ : π η ≠ π z := by
    intro heq
    apply hηne
    have h1 : x ∈ closure ({π η} : Set Y) := specializes_iff_mem_closure.mp hηx
    rw [heq, hπzcl.closure_eq] at h1
    rw [heq]
    exact (Set.mem_singleton_iff.mp h1).symm
  obtain ⟨d, hTan⟩ : ∃ d, Tan.card = d + 1 :=
    ⟨Tan.card - 1, by have := Finset.card_pos.mpr (hTanne hneπ); omega⟩
  have hdn : d + 1 ≤ n := by
    have h1 := Finset.card_le_univ Tan
    rw [Fintype.card_fin, hTan] at h1
    exact h1
  -- the dimension and the degree of the image of the centre
  obtain ⟨D', hD'n, hD'⟩ := hdim (π η) hηx
  have hgW : g ∉ ((pointClosureι (π η) ≫ e)
      (genericPoint (pointClosureScheme (π η)))).asHomogeneousIdeal := by
    rw [Scheme.Hom.comp_apply, pointClosureι_genericPoint]
    exact (Proj.mem_basicOpen _ _ _).mp ((e.base.hom.map_specializes hηx).mem_open
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) K) g).isOpen
      ((Proj.mem_basicOpen _ _ _).mpr hgx))
  -- the thresholds
  have hM : l * (2 * s ^ D' + 2 ^ D' * D'.factorial + (d + 1) + s ^ (d + 1)) ≤ m k := by
    refine le_trans (Nat.mul_le_mul_left l ?_) hMk
    have h1 : s ^ D' ≤ s ^ n := Nat.pow_le_pow_right hs hD'n
    have h2 : 2 ^ D' * D'.factorial ≤ 2 ^ n * n.factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hD'n) (Nat.factorial_le hD'n)
    have h3 : s ^ (d + 1) ≤ s ^ n := Nat.pow_le_pow_right hs hdn
    omega
  -- the objective of the new weight is the objective of the datum
  have hobj : (∑ i, Real.exp ((∑ k', w' k' * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY dd D₀ cX etaleCharts_cover) (ξ k')) / dd)) / t -
      (∑ k', w' k' * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
        (m k • projectiveHyperplaneCartier e g hg hggen) (B i) (B.ne_zero i))) (ξ k') : ℝ)) /
          (m k : ℝ))) = ∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hw'A, ← hw'v i]
  have hmin : (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
      sncWeightInfimum cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
        (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t
          (m k) :=
    le_sncWeightInfimum _ _ _ _ _ _ _ _ _ ⟨_, B, p, hp, rfl⟩ fun B' p' hp' => hpmin B' p' hp'
  have hspec := hG6 (π z) hπzcl hzG hηz'
  have hineq := projectiveHyperplane_centerDegreeInequalities π hπ e g hg hggen he k₀ cY fY hdd
    D₀ cX ξ hinj hξ hsnc hBsupp c σc hc w' hw'0 hw'ne η hηc hη hmax x hηx z hz hηz hzU ez hez
    hiff Tan hTan hTanfree hTanU hsat MonomialOrder.lex s hs hD' hgW
    (hdeg (π η) hgW D' hηx hηne hD') l (m k) (by omega) hM B hGsupp hNk ht a
    (by rw [← hw'A]; exact hap) (by rw [hobj]; exact hmin)
    (by rw [hobj]; exact hmin.trans hspec)
  exact hk (d + 1) (Nat.succ_pos d) hdn ⟨_, _, _, hineq⟩


omit [IsLocallyNoetherian Y] in
/-- The point-centre property along a degree sequence realizing the liminf, for the hyperplane
class, when the specialization comparison (6) and the bound a ≤ A of the minimizing profile data
are only known for the large members of the sequence and the chosen t. -/
theorem projectiveHyperplane_pointCentre_along_sequence
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    {dd : ℕ} (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (hdd : 1 ≤ dd)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY dd D₀)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hn : 0 < n) {a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = n + 1) (ht₀ : t₀ < b)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ n ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧
      ∀ {ν c : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
          atTop (𝓝 ν) →
        0 < c →
        liminf (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop = c →
        IsBoundedUnder (· ≥ ·) atTop (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) →
        ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
        Tendsto (fun k => sncWeightInfimum cY fY dd D₀
          (m k • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t (m k) /
            Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop (𝓝 c) →
        (∀ᶠ k in atTop, ∀ w : Y, w ⤳ x → w ≠ x → ∃ U : Y.Opens, w ∈ U ∧
          ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ U → w ⤳ y →
            sncWeightInfimum cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
                (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t
                (m k) ≤
              sncWeightInfimum cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) y
                (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t
                (m k)) →
        (∀ᶠ k in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
              B', (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
                ∑ i, Real.exp (p'.1 / t - p'.2 i / (m k : ℝ))) →
          a ≤ p.1) →
        ∀ᶠ k in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
              B', (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
                ∑ i, Real.exp (p'.1 / t - p'.2 i / (m k : ℝ))) →
          SNCWeightProfileHasPointCentre cY fY dd D₀
            (m k • projectiveHyperplaneCartier e g hg hggen) x B p := by
  obtain ⟨t, ht₀', ht, htb, h⟩ := projectiveHyperplane_pointCentre_along_sequence_of_dense e g hg
    hggen he cY fY hdd D₀ hklt x hxc hgx hn ha hb s hs hsb ht₀ hdim hdeg
  exact ⟨t, ht₀', ht, htb, fun hν hN hc hliminf hbdd m hm hfm h6ev hAev =>
    h hν hN hc hliminf hbdd m hm hfm (h6ev.mono fun k hk w hwx hne => by
      obtain ⟨U, hwU, hU⟩ := hk w hwx hne
      exact ⟨U, closedPointsDenseOver_of_isOpen U.isOpen hwU,
        fun y hyc hyU hwy => hU y hyc hyU hwy⟩) hAev⟩

omit [IsLocallyNoetherian Y] in
/-- The point-centre property along a degree sequence realizing the liminf, for the hyperplane
class. -/
theorem projectiveHyperplane_eventually_pointCentre
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    [∀ j : ℕ, FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)]
    {dd : ℕ} (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (hdd : 1 ≤ dd)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY dd D₀)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hn : 0 < n) {a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = n + 1) (ht₀ : t₀ < b)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ n ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (h6 : ∀ w : Y, w ⤳ x → w ≠ x → ∀ (j : ℕ) (t : ℝ), ∃ U : Y.Opens, w ∈ U ∧
      ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ U → w ⤳ y →
        sncWeightInfimum cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) x
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j ≤
          sncWeightInfimum cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) y
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j)
    (hA : ∀ (j : ℕ) (t : ℝ) (B : Module.Basis (Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
      ∀ p ∈ sncWeightProfiles cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) x B,
      (∀ (B' : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (j • projectiveHyperplaneCartier e g hg hggen) x B',
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
      a ≤ p.1) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧
      ∀ {ν c : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
          atTop (𝓝 ν) →
        0 < c →
        liminf (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop = c →
        IsBoundedUnder (· ≥ ·) atTop (fun j : ℕ => sncWeightInfimum cY fY dd D₀
          (j • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
            Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) →
        ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
        Tendsto (fun k => sncWeightInfimum cY fY dd D₀
          (m k • projectiveHyperplaneCartier e g hg hggen) x
          (Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t (m k) /
            Module.finrank K Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
          atTop (𝓝 c) →
        ∀ᶠ k in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x B,
          (∀ (B' : Module.Basis (Fin (Module.finrank K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
              Γ((m k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
            ∀ p' ∈ sncWeightProfiles cY fY dd D₀ (m k • projectiveHyperplaneCartier e g hg hggen) x
              B', (∑ i, Real.exp (p.1 / t - p.2 i / (m k : ℝ))) ≤
                ∑ i, Real.exp (p'.1 / t - p'.2 i / (m k : ℝ))) →
          SNCWeightProfileHasPointCentre cY fY dd D₀
            (m k • projectiveHyperplaneCartier e g hg hggen) x B p := by
  obtain ⟨t, ht₀', ht, htb, h⟩ := projectiveHyperplane_pointCentre_along_sequence e g hg hggen
    he cY fY hdd D₀ hklt x hxc hgx hn ha hb s hs hsb ht₀ hdim hdeg
  exact ⟨t, ht₀', ht, htb, fun hν hN hc hliminf hbdd m hm hfm => h hν hN hc hliminf hbdd m hm hfm
    (Eventually.of_forall fun k w hw hne => h6 w hw hne (m k) t)
    (Eventually.of_forall fun k B p hp hmin => hA (m k) t B p hp hmin)⟩

end MixedFujita
