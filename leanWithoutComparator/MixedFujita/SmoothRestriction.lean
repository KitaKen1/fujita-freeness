/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericRestriction

/-!
Restriction to smooth closed subvarieties (step 9).

`SmoothRestrictionStatement` is the model form of the restriction theorem for log canonical
thresholds: for a smooth affine variety X = Spec A, a smooth closed subvariety Z = Spec A' of
positive dimension (a surjection A → A') and a K-point of Z, if the threshold of a family on X at
the point is at most 1/M, then so is the threshold of the restricted family on Z
(lct_x(Z, a|_Z) ≤ lct_x(X, a); Lazarsfeld, Positivity II, 9.5.1). Restriction to the fibres of a
product V × Spec B is the case of the surjection id ⊗ w : Γ(V) ⊗ B → Γ(V)
(`fibreRestrictionStatement_of_smoothRestriction`), so F1 follows from sum KV and the restriction
theorem (`mixedFujitaFreeness_of_kvSum_of_smoothRestriction`).

On the way: a test model of an open subscheme is a test model of the ambient scheme with the same
log discrepancies, because the relative canonical divisor of an open immersion has unit local
equations (`logDiscrepancy_coefficient_comp_openImmersion`); hence bad points of an open subscheme
are bad points of the ambient scheme (`modelThresholdBadAt_of_openImmersion`).
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

section OpenImmersion

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {U Y : Scheme.{u}} [IsIntegral U] [IsIntegral Y]
  [U.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  (j : U ⟶ Y) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

include hj in
/-- The log discrepancies of a test model of an open subscheme do not change when it is regarded
as a test model of the ambient scheme. -/
theorem logDiscrepancy_coefficient_comp_openImmersion (cY : EtaleChart K Y n)
    (cU : EtaleChart K U n) {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (σ : T ⟶ U) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cT : EtaleChart K T n)
    (e : T) :
    cartierCoefficient (logDiscrepancyDivisor n (σ ≫ j)
      (dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ) cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cT
      etaleCharts_cover) e =
    cartierCoefficient (logDiscrepancyDivisor n σ hσ cU (1 : U.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cU + principalCartierDivisor U (1 : U.functionFieldˣ))) cT
      etaleCharts_cover) e := by
  rw [logDiscrepancyDivisor_comp_eq_pullback_add_relative j σ hj hσ cY 1 1 _ cU etaleCharts_cover
      cT etaleCharts_cover, logDiscrepancyDivisor_boundary_zero j hj cY 1 1 cU,
    logDiscrepancyDivisor_boundary_zero σ hσ cU 1 1 cT, cartierCoefficient_add,
    cartierPullback_nsmul, cartierCoefficient_nsmul]
  suffices h : cartierCoefficient (cartierPullback σ (birationalRelativeCanonicalDivisor n j hj cY
      etaleCharts_cover cU etaleCharts_cover)) e = 0 by
    rw [h]
    simp
  -- the relative canonical divisor of j has a unit local equation at σ(e)
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K Y n, j (σ e) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top _)
  obtain ⟨c', hc'⟩ : ∃ c : EtaleChart K U n, σ e ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := U) (n := n)).symm ▸ Opens.mem_top _)
  have hbij : Function.Bijective (j.stalkMap (σ e)) := ConcreteCategory.bijective_of_isIso _
  have hf := relativeCanonicalDivisor_isLocalEquationAt j cY etaleCharts_cover cU etaleCharts_cover
    (isUnit_chartRelativeJacobianDet_of_bijective j hj cY cU) (σ e) c hc c' hc'
  have h2 := cartierPullback_isLocalEquationAt σ _ e hf
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord h2]
  have hu := chartRelativeJacobianDet_stalk_isUnit_of_bijective j (σ e) hbij c hc c' hc'
  have h3 : ((Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom
      (isUnit_chartRelativeJacobianDet j cY cU
        (isUnit_chartRelativeJacobianDet_of_bijective j hj cY cU) c c').unit :
      T.functionFieldˣ) : T.functionField) =
      algebraMap (T.presheaf.stalk e) T.functionField
        (σ.stalkMap e (hu.unit : U.presheaf.stalk (σ e))) := by
    change (dominantFunctionFieldMap σ).hom (chartRelativeJacobianDet j c c') = _
    rw [chartRelativeJacobianDet_eq_stalk j (σ e) c hc c' hc']
    exact dominantFunctionFieldMap_algebraMap σ e _
  rw [h3]
  exact scheme_ord_stalk_unit e (hu.unit.map (σ.stalkMap e).hom.toMonoidHom)

include hj in
/-- A bad point of an open subscheme is a bad point of the ambient scheme. -/
theorem modelThresholdBadAt_of_openImmersion (cY : EtaleChart K Y n) (cU : EtaleChart K U n)
    (u : U) {J : Type*} (gY : J → Y.functionField) (gU : J → U.functionField)
    (hg : ∀ i, (dominantFunctionFieldMap j).hom (gY i) = gU i) (M : ℕ)
    (h : ModelThresholdBadAt cU (1 : U.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cU + principalCartierDivisor U (1 : U.functionFieldˣ))) u gU
      M) :
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) (j u)
      gY M := by
  obtain ⟨T, hTi, hTn, hTo, hTs, σ, hσd, hσo, hσ, cT, e, hue, hApos, hineq⟩ := h
  refine ⟨T, hTi, hTn, hTo, hTs, σ ≫ j, inferInstance, inferInstance,
    dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ, cT, e, ?_, ?_, ?_⟩
  · exact map_mem_closure j.continuous hue fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      rfl
  · rw [logDiscrepancy_coefficient_comp_openImmersion j hj cY cU σ hσ cT (e : T)]
    exact hApos
  · intro i hi
    rw [logDiscrepancy_coefficient_comp_openImmersion j hj cY cU σ hσ cT (e : T)]
    have hi' : gU i ≠ 0 := by
      rw [← hg i]
      exact (map_ne_zero _).mpr hi
    have h2 : (dominantFunctionFieldMap (σ ≫ j)).hom (gY i) =
        (dominantFunctionFieldMap σ).hom (gU i) := by
      rw [dominantFunctionFieldMap_comp, ← hg i]
      rfl
    rw [h2]
    exact hineq i hi'

end OpenImmersion

section Statement

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specAlgebraOver

/-- Restriction to smooth closed subvarieties, in the model form: for a surjection π : A → A' of
smooth finitely generated K-domains of dimensions N + d and N ≥ 1 and a K-point χ of A', if the
threshold of a family g on Spec A at the point χ ∘ π is at most 1/M, then so is the threshold of
π ∘ g on Spec A' at χ (lct_x(Z, a|_Z) ≤ lct_x(X, a) for the smooth closed subvariety Z of X;
Lazarsfeld, Positivity II, 9.5.1). -/
def SmoothRestrictionStatement : Prop :=
  ∀ (A A' : Type u) [CommRing A] [IsDomain A] [Algebra K A] [CommRing A'] [IsDomain A']
    [Algebra K A'] (N d : ℕ)
    [SmoothOfRelativeDimension (N + d) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension N (Spec (CommRingCat.of A') ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + d))
    (cZ : EtaleChart K (Spec (CommRingCat.of A')) N) (π : A →ₐ[K] A'), Function.Surjective π →
    ∀ {J : Type} [Finite J] (g : J → A) (M : ℕ), 1 ≤ N → 1 ≤ M → ∀ χ : A' →ₐ[K] K,
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
          (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
        (specAlgHomPoint (χ.comp π))
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
      ModelThresholdBadAt cZ (1 : (Spec (CommRingCat.of A')).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor (Spec (CommRingCat.of A'))
          (1 : (Spec (CommRingCat.of A')).functionFieldˣ)))
        (specAlgHomPoint χ)
        (fun j => (Spec (CommRingCat.of A')).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g j)))) M

end Statement

section Reduction

variable {K : Type u} [Field K]

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

/-- Restriction to the fibre over w of a product V × Spec B is restriction to the smooth closed
subvariety V × {w}, cut out by the surjection id ⊗ w : Γ(V) ⊗ B → Γ(V). -/
theorem fibreRestrictionStatement_of_smoothRestriction (hSR : SmoothRestrictionStatement K) :
    FibreRestrictionStatement K := by
  classical
  intro Y _ _ _ n _ cY V hV _ B _ _ _ d _ _ _ cX J _ g M hn hM y hy ψ hψ w hbad
  haveI hsmV : SmoothOfRelativeDimension n
      (Spec (CommRingCat.of Γ(Y, V)) ↘ Spec (CommRingCat.of K)) :=
    smoothOfRelativeDimension_spec_sections hV
  have : Smooth (Spec (CommRingCat.of Γ(Y, V)) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth n _
  -- the fibre over w as a smooth closed subvariety of the product
  have hsurj : Function.Surjective (fibreAt w : Γ(Y, V) ⊗[K] B →ₐ[K] Γ(Y, V)) := fun a =>
    ⟨a ⊗ₜ[K] (1 : B), by rw [fibreAt_tmul, map_one, map_one, mul_one]⟩
  have hpair : ψ.comp (fibreAt w) = pairAlgHom ψ w := by
    refine AlgHom.ext fun r => ?_
    change ψ (fibreAt w r) = pairAlgHom ψ w r
    induction r with
    | tmul a b => rw [fibreAt_tmul, pairAlgHom_tmul, map_mul, AlgHom.commutes]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  obtain ⟨cZ, -⟩ : ∃ c : EtaleChart K (Spec (CommRingCat.of Γ(Y, V))) n,
      specAlgHomPoint ψ ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Spec (CommRingCat.of Γ(Y, V)))
      (n := n)).symm ▸ Opens.mem_top _)
  have h1 := hSR (Γ(Y, V) ⊗[K] B) Γ(Y, V) n d cX cZ (fibreAt w) hsurj g M hn hM ψ
    (by rw [hpair]; exact hbad)
  -- from Spec Γ(V) to Y along the open immersion onto V
  let jV : Spec (CommRingCat.of Γ(Y, V)) ⟶ Y := hV.fromSpec
  haveI : IsOpenImmersion jV := (inferInstance : IsOpenImmersion hV.fromSpec)
  haveI : IsDominant jV := ⟨jV.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI : jV.IsOver (Spec (CommRingCat.of K)) := ⟨affineOpen_fromSpec_over_eq_specMap hV⟩
  have hjV : Function.Bijective (dominantFunctionFieldAlgHom (K := K) jV) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion jV
  have hy' : jV (specAlgHomPoint ψ) = y := by
    have h0 : specAlgHomPoint ψ = hV.primeIdealOf ⟨y, hy⟩ := by
      apply PrimeSpectrum.ext
      ext a
      exact (RingHom.mem_ker).trans (hψ a)
    rw [h0]
    exact hV.fromSpec_primeIdealOf ⟨y, hy⟩
  have hx : jV (specAlgHomPoint ψ) ∈ V := by
    rw [hy']
    exact hy
  haveI : Nonempty (⊤ : (Spec (CommRingCat.of Γ(Y, V))).Opens) :=
    ⟨⟨specAlgHomPoint ψ, trivial⟩⟩
  have hg : ∀ i, (dominantFunctionFieldMap jV).hom (Y.germToFunctionField V (fibreAt w (g i))) =
      (Spec (CommRingCat.of Γ(Y, V))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of Γ(Y, V))).inv (fibreAt w (g i))) := by
    intro i
    rw [← Y.algebraMap_germ_eq_germToFunctionField hx, dominantFunctionFieldMap_algebraMap,
      ← (Spec (CommRingCat.of Γ(Y, V))).algebraMap_germ_eq_germToFunctionField
        (show specAlgHomPoint ψ ∈ (⊤ : (Spec (CommRingCat.of Γ(Y, V))).Opens) from trivial)]
    congr 1
    exact fromSpec_stalkMap_germ hV (specAlgHomPoint ψ) hx (fibreAt w (g i))
  have h2 := modelThresholdBadAt_of_openImmersion jV hjV cY cZ (specAlgHomPoint ψ)
    (fun i => Y.germToFunctionField V (fibreAt w (g i)))
    (fun i => (Spec (CommRingCat.of Γ(Y, V))).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of Γ(Y, V))).inv (fibreAt w (g i)))) hg M h1
  rw [hy'] at h2
  exact h2

/-- F1 from sum KV and the restriction theorem for smooth closed subvarieties. -/
theorem mixedFujitaFreeness_of_kvSum_of_smoothRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hSR : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_fibreRestriction hKV
    (fun _ _ _ _ => fibreRestrictionStatement_of_smoothRestriction (hSR _))

/-- F1 from the usual KV, big plus nef and the restriction theorem for smooth closed
subvarieties. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_smoothRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hSR : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_fibreRestriction hKV hba
    (fun _ _ _ _ => fibreRestrictionStatement_of_smoothRestriction (hSR _))

end Reduction

end MixedFujita
