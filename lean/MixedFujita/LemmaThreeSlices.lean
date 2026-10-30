/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedPointRealizationFromLemmaThree

/-!
Lemma 3 at closed points and on affine space as slices of Lemma 3 in the model form on the affine
opens of smooth varieties (step 9).

* At a closed point x, the finitely many coefficients of a polynomial family with coefficients in
  the local ring at x are germs of sections over one affine open V; Lemma 3 on V restricted to
  y = x is the closedness of the parameters of the family at x
  (`idealThresholdZariskiClosed_of_smoothAffineLemmaThree`).
* On affine space, V is the whole space and the sections are the polynomials; the zero set of an
  ideal of Γ(A^N)[c] at the closed point x is the zero set at (x, c) of the corresponding ideal of
  K[x, c] (`affineLemmaThreeStatement_of_smoothAffineLemmaThree`).

So F1 follows from sum KV (or the usual KV and big plus nef) and Lemma 3 in the model form on
affine opens alone (`mixedFujitaFreeness_of_kvSum_of_smoothAffineLemmaThree`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Germs

variable {Y : Scheme.{u}}

/-- Finitely many germs at a point are germs of sections over one affine open. -/
theorem exists_affine_sections_of_germs (x : Y) {T : Type*} [Finite T]
    (t : T → Y.presheaf.stalk x) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (hx : x ∈ V) (s : T → Γ(Y, V)),
      ∀ k, Y.presheaf.germ V x hx (s k) = t k := by
  classical
  choose W hxW s' hs' using fun k => Y.presheaf.exists_germ_eq (t k)
  set O : Y.Opens := ⨅ k, W k with hO
  have hxO : x ∈ O := by
    rw [hO, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact fun k => hxW k
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxO O.isOpen
  have hVW : ∀ k, V ≤ W k := fun k y hy => by
    have h := hVO hy
    rw [hO, Opens.coe_iInf, Set.mem_iInter] at h
    exact h k
  refine ⟨V, hV, hxV, fun k => Y.presheaf.map (homOfLE (hVW k)).op (s' k), fun k => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply, hs' k]

end Germs

section ClosedPoint

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 3 at a closed point, for polynomial families with coefficients in the local ring, as the
slice of Lemma 3 in the model form on affine opens. -/
theorem idealThresholdZariskiClosed_of_smoothAffineLemmaThree
    (hL3 : SmoothAffineLemmaThreeStatement K) (cY : EtaleChart K Y n) (x : Y)
    (hx : IsClosed ({x} : Set Y)) :
    IdealThresholdZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) x := by
  classical
  intro ι J _ _ G M hM
  obtain ⟨V, hV, hxV, s, hs⟩ := exists_affine_sections_of_germs x
    (fun k : (Σ j : J, (G j).support) => (G k.1).coeff k.2)
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  let G' : J → MvPolynomial ι Γ(Y, V) := fun j =>
    ∑ d ∈ (G j).support.attach, MvPolynomial.monomial d.1 (s ⟨j, d⟩)
  have hmap : ∀ j, MvPolynomial.map (Y.presheaf.germ V x hxV).hom (G' j) = G j := by
    intro j
    simp only [G', map_sum, MvPolynomial.map_monomial]
    conv_rhs => rw [(G j).as_sum]
    rw [← Finset.sum_attach (G j).support]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hs ⟨j, d⟩]
  obtain ⟨I', hI'⟩ := hL3 Y n cY V hV G' M (by omega)
  have hFT : Algebra.FiniteType K Γ(Y, V) := smooth_affineOpen_finiteType (n := n) hV
  have hmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  let ev : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hev : ∀ a, ev a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := fun a =>
    closedPointEvaluation_eq_zero_iff (K := K) _ a
  have hcomp : ∀ (c : ι → K) (g : MvPolynomial ι Γ(Y, V)),
      ev (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g) =
        MvPolynomial.eval c (MvPolynomial.map ev.toRingHom g) := by
    intro c g
    rw [MvPolynomial.eval_map]
    have h : ev.toRingHom.comp (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i))) =
        MvPolynomial.eval₂Hom ev.toRingHom c := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        simp
    exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* K => φ g) h
  have hgerm : ∀ (c : ι → K) (j : J),
      Y.germToFunctionField V (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G' j)) =
        algebraMap (Y.presheaf.stalk x) Y.functionField
          (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j)) := by
    intro c j
    rw [← Y.algebraMap_germ_eq_germToFunctionField hxV]
    congr 1
    rw [← hmap j, MvPolynomial.eval_map]
    have h : (Y.presheaf.germ V x hxV).hom.comp
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i))) =
        MvPolynomial.eval₂Hom (Y.presheaf.germ V x hxV).hom
          (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        have h1 := (sectionStalkAlgHom (K := K) V x hxV).commutes (c i)
        rw [sectionStalkAlgHom_apply] at h1
        simpa using h1
    exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* Y.presheaf.stalk x => φ (G' j)) h
  refine ⟨Ideal.map (MvPolynomial.map ev.toRingHom) I', ?_⟩
  ext c
  have hiff := hI' x hxV hx c
  simp only [hgerm] at hiff
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, hval⟩
    have hbad := hiff.mp ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e, hx', hA,
      fun j hj => hval j (fun h0 => hj (by simp only [h0, map_zero]))⟩
    have hle : Ideal.map (MvPolynomial.map ev.toRingHom) I' ≤ RingHom.ker (MvPolynomial.eval c) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomp]
      exact (hev _).mpr (hbad g hg)
    intro p hp
    exact hle hp
  · intro hc
    have h2 : ∀ g ∈ I', MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := fun g hg =>
      (hev _).mp (by rw [hcomp]; exact hc _ (Ideal.mem_map_of_mem _ hg))
    obtain ⟨U, h1, h2', h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, hval⟩ := hiff.mpr h2
    exact ⟨U, h1, h2', h3, h4, σ, h5, h6, hσ, cU, e, hx', hA, fun j hj =>
      hval j ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hj)⟩

end ClosedPoint

section Affine

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specAlgebraOver affineSpace_smoothOfRelativeDimension cartierBaseOpenAlgebra

/-- Lemma 3 in the model form on affine space as the case V = A^N of Lemma 3 in the model form on
affine opens. -/
theorem affineLemmaThreeStatement_of_smoothAffineLemmaThree
    (hL3 : SmoothAffineLemmaThreeStatement K) : AffineLemmaThreeStatement K := by
  classical
  intro N r J _ G M hM
  have := affineSpace_locallyOfFiniteType K N
  have hV : IsAffineOpen (⊤ : (affineSpace K N).Opens) := isAffineOpen_top _
  have hne : Nonempty (⊤ : (affineSpace K N).Opens) := ⟨⟨affineSpacePoint K N 0, trivial⟩⟩
  let ι := specAlgebraCoords (AlgHom.id K (MvPolynomial (Fin N) K))
  have hι : ∀ a, ι a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) K))).inv a :=
    fun a => rfl
  have hιsurj : Function.Surjective ι := by
    intro b
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) K))).hom b, ?_⟩
    rw [hι]
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) K))) b
  let φ : MvPolynomial (Fin N ⊕ Fin r) K →ₐ[K] MvPolynomial (Fin r) (MvPolynomial (Fin N) K) :=
    MvPolynomial.aeval (Sum.elim (fun i => MvPolynomial.C (MvPolynomial.X i)) MvPolynomial.X)
  have hφC : ∀ p : MvPolynomial (Fin N) K, φ (MvPolynomial.rename Sum.inl p) = MvPolynomial.C p := by
    intro p
    have h : φ.comp (MvPolynomial.rename Sum.inl) =
        IsScalarTower.toAlgHom K (MvPolynomial (Fin N) K)
          (MvPolynomial (Fin r) (MvPolynomial (Fin N) K)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [φ]
    exact congrArg (fun ψ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin r)
      (MvPolynomial (Fin N) K) => ψ p) h
  have hφsurj : Function.Surjective φ := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => exact ⟨MvPolynomial.rename Sum.inl a, hφC a⟩
    | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add _ _ _⟩
    | mul_X p k hp =>
      obtain ⟨p', rfl⟩ := hp
      exact ⟨p' * MvPolynomial.X (Sum.inr k), by simp [φ]⟩
  let Ψ : MvPolynomial (Fin N ⊕ Fin r) K →+* MvPolynomial (Fin r) Γ(affineSpace K N, ⊤) :=
    (MvPolynomial.map ι.toRingHom).comp φ.toRingHom
  have hΨsurj : Function.Surjective Ψ :=
    (MvPolynomial.map_surjective _ hιsurj).comp hφsurj
  let G' : J → MvPolynomial (Fin r) Γ(affineSpace K N, ⊤) := fun j => Ψ (G j)
  obtain ⟨I', hI'⟩ := hL3 (affineSpace K N) N (affineSpaceEtaleChart K N) ⊤ hV G' M hM
  refine ⟨Ideal.comap Ψ I', fun x c => ?_⟩
  -- the evaluation of the parameters commutes with the identification
  have hevalΨ : ∀ g : MvPolynomial (Fin N ⊕ Fin r) K,
      MvPolynomial.eval (fun k => ι (MvPolynomial.C (c k))) (Ψ g) =
        ι (MvPolynomial.aeval (Sum.elim MvPolynomial.X fun k => MvPolynomial.C (c k)) g) := by
    intro g
    have h1 : (MvPolynomial.eval (fun k => ι (MvPolynomial.C (c k)))).comp Ψ =
        ι.toRingHom.comp
          (MvPolynomial.aeval (Sum.elim MvPolynomial.X fun k => MvPolynomial.C (c k))).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [Ψ, φ]
      · intro v
        cases v with
        | inl i => simp [Ψ, φ]
        | inr k => simp [Ψ, φ]
    exact congrArg (fun ψ : MvPolynomial (Fin N ⊕ Fin r) K →+* Γ(affineSpace K N, ⊤) => ψ g) h1
  -- the prime of the point x
  set y := affineSpacePoint K N x with hy
  have hmax : (RingHom.ker (MvPolynomial.eval x)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun k => ⟨MvPolynomial.C k, MvPolynomial.eval_C k⟩
  have hyc : IsClosed ({y} : Set (affineSpace K N)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hmax
  have hprime : ∀ a : MvPolynomial (Fin N) K,
      ι a ∈ (hV.primeIdealOf ⟨y, trivial⟩).asIdeal ↔ MvPolynomial.eval x a = 0 := by
    intro a
    rw [← not_iff_not, ← mem_basicOpen_iff_notMem_primeIdealOf hV y trivial, hι,
      basicOpen_eq_of_affine]
    change a ∉ y.asIdeal ↔ _
    rw [affineSpacePoint_mem_iff]
  have hfun : (fun j => (affineSpace K N).germToFunctionField ⊤
      (MvPolynomial.eval (fun k => ι (MvPolynomial.C (c k))) (G' j))) =
      fun j => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K N)
        (MvPolynomial.aeval (Sum.elim MvPolynomial.X fun k => MvPolynomial.C (c k)) (G j)) := by
    funext j
    rw [show G' j = Ψ (G j) from rfl, hevalΨ]
    rfl
  have h := hI' y trivial hyc c
  simp only [← ι.commutes, MvPolynomial.algebraMap_eq] at h
  rw [hfun] at h
  rw [h]
  have hpt : ∀ g : MvPolynomial (Fin N ⊕ Fin r) K,
      MvPolynomial.eval x (MvPolynomial.aeval (Sum.elim MvPolynomial.X fun k => MvPolynomial.C (c k)) g) =
        MvPolynomial.eval (Sum.elim x c) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases v <;> simp
  constructor
  · intro hI g hg
    have h1 := hI (Ψ g) (Ideal.mem_comap.mp hg)
    rw [hevalΨ, hprime, hpt] at h1
    exact h1
  · intro hI g hg
    obtain ⟨g', rfl⟩ := hΨsurj g
    rw [hevalΨ, hprime, hpt]
    exact hI g' (Ideal.mem_comap.mpr hg)

end Affine

section Freeness

/-- F1 from sum KV and Lemma 3 in the model form on affine opens of smooth varieties: every other
form of Lemma 3 used in step 9 is a slice of it. -/
theorem mixedFujitaFreeness_of_kvSum_of_smoothAffineLemmaThree
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothAffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_smoothAffineLemmaThree hKV
    (fun K _ _ _ _ X _ _ n _ c₀ x hx => by
      have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
      have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) := inferInstance
      exact @idealThresholdZariskiClosed_of_smoothAffineLemmaThree K _ _ _ X _ _ _ n _ (hL3 K) c₀ x hx)
    hL3 (fun K _ _ _ => affineLemmaThreeStatement_of_smoothAffineLemmaThree (hL3 K))

/-- F1 from the usual KV, big plus nef and Lemma 3 in the model form on affine opens of smooth
varieties. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_smoothAffineLemmaThree
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothAffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_smoothAffineLemmaThree hKV hba
    (fun K _ _ _ _ X _ _ n _ c₀ x hx => by
      have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
      have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) := inferInstance
      exact @idealThresholdZariskiClosed_of_smoothAffineLemmaThree K _ _ _ X _ _ _ n _ (hL3 K) c₀ x hx)
    hL3 (fun K _ _ _ => affineLemmaThreeStatement_of_smoothAffineLemmaThree (hL3 K))

end Freeness

end MixedFujita
