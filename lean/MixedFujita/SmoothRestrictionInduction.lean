/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RingKernelCoordinates

/-!
Localizing a restriction situation, and the induction on the codimension (step 9, restriction
theorem).

For a surjection π : A → A' of smooth K-domains, a K-point χ of A' and b ∈ A with χ(π b) ≠ 0, the
localized map π_b : A_b → A'_{π b} is again a surjection (`IsLocalization.Away.mapₐ`), χ extends to
a K-point χ_b of A'_{π b} (`awayPoint`), and if the restriction holds for π_b at χ_b, it holds for
π at χ (`modelThresholdBad_restrict_of_away`): badness on Spec A and on Spec A_b, and on Spec A'
and Spec A'_{π b}, agree at the points (check-317). So in the induction on the codimension in the
restriction theorem one may shrink to basic open neighbourhoods of the point on both sides.

The induction (`smoothRestrictionStatement_of_hypersurface`): the restriction theorem for smooth
closed subvarieties follows from its codimension-one case (`SmoothRestrictionCodim K 1`, smooth
hypersurfaces). Codimension zero holds outright (check-322). In codimension d + 1, étale coordinates
(t, u) on A_b with t ∈ ker π (check-323) cut out the hypersurface C = A_b/(t), étale over affine
space of dimension N + d (check-320), which is a smooth K-domain on a basic open D(c) of the point
(check-321); localizing at a lift c' of c on both sides, the localized map factors as
(A_b)_{c'} → C_c → (A'_{π b})_{π c'}, a hypersurface followed by a codimension d restriction. Hence
F1 follows from sum KV and the restriction theorem for smooth hypersurfaces
(`mixedFujitaFreeness_of_kvSum_of_hypersurfaceRestriction`).
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

section AwaySituation

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- A K-point nonzero at b extends to the localization at b. -/
noncomputable def awayPoint {A : Type u} [CommRing A] [Algebra K A] (χ : A →ₐ[K] K) (b : A)
    (hb : χ b ≠ 0) : Localization.Away b →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom b (f := χ) (isUnit_iff_ne_zero.mpr hb)

theorem awayPoint_algebraMap {A : Type u} [CommRing A] [Algebra K A] (χ : A →ₐ[K] K) (b : A)
    (hb : χ b ≠ 0) (a : A) : awayPoint χ b hb (algebraMap A (Localization.Away b) a) = χ a :=
  IsLocalization.Away.lift_eq b (isUnit_iff_ne_zero.mpr hb) a

/-- If the restriction holds for the localized surjection A_b → A'_{π b} at the extended point, it
holds for A → A' at χ. -/
theorem modelThresholdBad_restrict_of_away {A A' : Type u} [CommRing A] [IsDomain A]
    [Algebra K A] [CommRing A'] [IsDomain A'] [Algebra K A'] {n n' : ℕ}
    [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n' (Spec (CommRingCat.of A') ↘ Spec (CommRingCat.of K))]
    (π : A →ₐ[K] A') (χ : A' →ₐ[K] K) (b : A) (hb : χ (π b) ≠ 0)
    [IsDomain (Localization.Away b)] [IsDomain (Localization.Away (π b))]
    [SmoothOfRelativeDimension n
      (Spec (CommRingCat.of (Localization.Away b)) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n'
      (Spec (CommRingCat.of (Localization.Away (π b))) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) n)
    (cZ : EtaleChart K (Spec (CommRingCat.of A')) n')
    (cXb : EtaleChart K (Spec (CommRingCat.of (Localization.Away b))) n)
    (cZb : EtaleChart K (Spec (CommRingCat.of (Localization.Away (π b)))) n')
    {J : Type} (g : J → A) (M : ℕ)
    (h : ModelThresholdBadAt cXb (1 : (Spec (CommRingCat.of (Localization.Away b))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cXb + principalCartierDivisor
          (Spec (CommRingCat.of (Localization.Away b)))
          (1 : (Spec (CommRingCat.of (Localization.Away b))).functionFieldˣ)))
        (specAlgHomPoint ((awayPoint χ (π b) hb).comp
          (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b)))
        (fun j => (Spec (CommRingCat.of (Localization.Away b))).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away b))).inv
            (algebraMap A (Localization.Away b) (g j)))) M →
      ModelThresholdBadAt cZb
        (1 : (Spec (CommRingCat.of (Localization.Away (π b)))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cZb + principalCartierDivisor
          (Spec (CommRingCat.of (Localization.Away (π b))))
          (1 : (Spec (CommRingCat.of (Localization.Away (π b)))).functionFieldˣ)))
        (specAlgHomPoint (awayPoint χ (π b) hb))
        (fun j => (Spec (CommRingCat.of (Localization.Away (π b)))).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (π b)))).inv
            (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b
              (algebraMap A (Localization.Away b) (g j))))) M)
    (hbad : ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
          (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
        (specAlgHomPoint (χ.comp π))
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M) :
    ModelThresholdBadAt cZ (1 : (Spec (CommRingCat.of A')).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor (Spec (CommRingCat.of A'))
        (1 : (Spec (CommRingCat.of A')).functionFieldˣ)))
      (specAlgHomPoint χ)
      (fun j => (Spec (CommRingCat.of A')).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g j)))) M := by
  -- the points
  have hptA : ((awayPoint χ (π b) hb).comp
      (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b)).comp
      (IsScalarTower.toAlgHom K A (Localization.Away b)) = χ.comp π := by
    ext a
    change awayPoint χ (π b) hb (IsLocalization.Away.map (Localization.Away b)
      (Localization.Away (π b)) π.toRingHom b (algebraMap A (Localization.Away b) a)) = χ (π a)
    rw [IsLocalization.Away.map, IsLocalization.map_eq, awayPoint_algebraMap]
    rfl
  have hptA' : (awayPoint χ (π b) hb).comp (IsScalarTower.toAlgHom K A' (Localization.Away (π b))) =
      χ := by
    ext a
    exact awayPoint_algebraMap χ (π b) hb a
  -- badness on A_b
  have h1 := (modelThresholdBadAt_away_iff (K := K) b cX cXb
    ((awayPoint χ (π b) hb).comp
      (IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b)) g M).mpr
    (by rw [hptA]; exact hbad)
  -- the restriction on the localization, and back to A'
  have h2 := h h1
  have hfam : ∀ j, IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b
      (algebraMap A (Localization.Away b) (g j)) =
      algebraMap A' (Localization.Away (π b)) (π (g j)) := by
    intro j
    change IsLocalization.Away.map (Localization.Away b) (Localization.Away (π b)) π.toRingHom b
      (algebraMap A (Localization.Away b) (g j)) = _
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  simp only [hfam] at h2
  have h3 := (modelThresholdBadAt_away_iff (K := K) (π b) cZ cZb (awayPoint χ (π b) hb)
    (fun j => π (g j)) M).mp h2
  rw [hptA'] at h3
  exact h3

end AwaySituation

section Helpers

variable {K : Type u} [Field K]

attribute [local instance] specAlgebraOver

/-- The spectrum of a K-algebra is smooth over K exactly when the algebra is smooth. -/
theorem algebraSmooth_of_smoothOfRelativeDimension {A : Type u} [CommRing A] [Algebra K A] {n : ℕ}
    [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))] :
    Algebra.Smooth K A := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
    SmoothOfRelativeDimension.smooth n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

/-- The spectrum of a smooth K-domain has an étale chart. -/
theorem nonempty_etaleChart_spec {A : Type u} [CommRing A] [IsDomain A] [Algebra K A] {n : ℕ}
    [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))] :
    Nonempty (EtaleChart K (Spec (CommRingCat.of A)) n) := by
  have : Smooth (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth n _
  obtain ⟨c, -⟩ := Opens.mem_iSup.mp
    ((etaleCharts_cover (K := K) (X := Spec (CommRingCat.of A)) (n := n)).symm ▸
      Opens.mem_top (Classical.choice inferInstance : Spec (CommRingCat.of A)))
  exact ⟨c⟩

end Helpers

section Induction

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- `SmoothRestrictionStatement` in a fixed codimension d. -/
def SmoothRestrictionCodim (d : ℕ) : Prop :=
  ∀ (A A' : Type u) [CommRing A] [IsDomain A] [Algebra K A] [CommRing A'] [IsDomain A']
    [Algebra K A'] (N : ℕ)
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
        (specAlgHomPoint (χ))
        (fun j => (Spec (CommRingCat.of A')).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g j)))) M

variable {K}

theorem smoothRestrictionStatement_of_forall_codim (h : ∀ d, SmoothRestrictionCodim K d) :
    SmoothRestrictionStatement K := by
  intro A A' _ _ _ _ _ _ N d _ _ cX cZ π hπ J _ g M hN hM χ hbad
  exact h d A A' N cX cZ π hπ g M hN hM χ hbad

/-- The restriction theorem in codimension zero. -/
theorem smoothRestrictionCodim_zero : SmoothRestrictionCodim K 0 := by
  intro A A' _ _ _ _ _ _ N _ _ cX cZ π hπ J _ g M hN hM χ hbad
  exact smoothRestriction_codim_zero cX cZ π hπ g M χ hbad

/-- The induction step: codimension d + 1 from codimension 1 and codimension d. -/
theorem smoothRestrictionCodim_succ {d : ℕ} (hH : SmoothRestrictionCodim K 1)
    (ih : SmoothRestrictionCodim K d) : SmoothRestrictionCodim K (d + 1) := by
  classical
  intro A A' _ _ _ _ _ _ N _ _ cX cZ π hπ J _ g M hN hM χ hbad
  haveI : SmoothOfRelativeDimension (N + d + 1)
      (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    ‹SmoothOfRelativeDimension (N + (d + 1)) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))›
  obtain ⟨t, b, u, ht, hb, hφ⟩ := exists_away_etale_coordinates_through_kernel (N := N) (d := d)
    π hπ χ
  -- localize at b on both sides
  have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
  have hπb0 : π b ≠ 0 := fun h0 => hb (by change χ (π b) = 0; rw [h0, map_zero])
  haveI : IsDomain (Localization.Away b) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)
  haveI : IsDomain (Localization.Away (π b)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hπb0)
  haveI := smoothOfRelativeDimension_spec_away (K := K) (n := N + (d + 1)) b
  haveI := smoothOfRelativeDimension_spec_away (K := K) (n := N) (π b)
  obtain ⟨cXb⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away b) (n := N + (d + 1))
  obtain ⟨cZb⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away (π b)) (n := N)
  refine modelThresholdBad_restrict_of_away π χ b hb cX cZ cXb cZb g M ?_ hbad
  intro hbadb
  -- the hypersurface t = 0 in A_b
  let πb := IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b
  let χb := awayPoint χ (π b) hb
  have hπb : Function.Surjective πb := IsLocalization.Away.mapₐ_surjective_of_surjective b hπ
  have hπb_alg : ∀ a, πb (algebraMap A (Localization.Away b) a) =
      algebraMap A' (Localization.Away (π b)) (π a) := by
    intro a
    change IsLocalization.Away.map (Localization.Away b) (Localization.Away (π b)) π.toRingHom b
      (algebraMap A (Localization.Away b) a) = _
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  let φ : MvPolynomial (Fin (N + d + 1)) K →ₐ[K] Localization.Away b :=
    MvPolynomial.aeval (R := K) (fun l => algebraMap A (Localization.Away b)
      ((Fin.cons t u : Fin (N + d + 1) → A) l))
  have hφ0 : φ (MvPolynomial.X 0) = algebraMap A (Localization.Away b) t := by
    simp only [φ, MvPolynomial.aeval_X, Fin.cons_zero]
  let I : Ideal (Localization.Away b) := Ideal.span {φ (MvPolynomial.X 0)}
  have hψ := formallyEtale_quotient_of_formallyEtale_succ φ hφ
  have hπbI : ∀ a ∈ I, (χb.comp πb) a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hφ0]
    change χb (πb r) * χb (πb (algebraMap A (Localization.Away b) t)) = 0
    rw [hπb_alg, ht, map_zero, map_zero, mul_zero]
  let χC : (Localization.Away b ⧸ I) →ₐ[K] K := Ideal.Quotient.liftₐ I (χb.comp πb) hπbI
  haveI : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (n := N + (d + 1))
  haveI : Algebra.FinitePresentation A (Localization.Away b) :=
    IsLocalization.Away.finitePresentation b
  haveI : Algebra.FinitePresentation K (Localization.Away b) :=
    Algebra.FinitePresentation.trans K A (Localization.Away b)
  haveI : Algebra.FinitePresentation K (Localization.Away b ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  obtain ⟨c, hcχ, hdomc, hsmc⟩ := exists_away_isDomain_smoothOfRelativeDimension (N := N + d) _
    hψ χC
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  -- localize at a lift c' of c on both sides
  have hc' : χb (πb c') ≠ 0 := hcχ
  have hc'0 : c' ≠ 0 := fun h0 => hc' (by rw [h0, map_zero, map_zero])
  have hπc'0 : πb c' ≠ 0 := fun h0 => hc' (by rw [h0, map_zero])
  haveI : IsDomain (Localization.Away c') :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hc'0)
  haveI : IsDomain (Localization.Away (πb c')) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hπc'0)
  haveI := smoothOfRelativeDimension_spec_away (K := K) (A := Localization.Away b)
    (n := N + (d + 1)) c'
  haveI := smoothOfRelativeDimension_spec_away (K := K) (A := Localization.Away (π b)) (n := N)
    (πb c')
  obtain ⟨cXbc⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away c')
    (n := N + (d + 1))
  obtain ⟨cZbc⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away (πb c')) (n := N)
  refine modelThresholdBad_restrict_of_away πb χb c' hc' cXb cZb cXbc cZbc
    (fun j => algebraMap A (Localization.Away b) (g j)) M ?_ hbadb
  intro hbadbc
  -- factor the localized map through the localized hypersurface
  let Cc := Localization.Away (Ideal.Quotient.mk I c')
  let πbc := IsLocalization.Away.mapₐ (Localization.Away c') (Localization.Away (πb c')) πb c'
  let χbc := awayPoint χb (πb c') hc'
  haveI : IsLocalization.Away ((Ideal.Quotient.mkₐ K I) c') Cc :=
    (inferInstance : IsLocalization.Away (Ideal.Quotient.mk I c') Cc)
  let π₁ : Localization.Away c' →ₐ[K] Cc :=
    IsLocalization.Away.mapₐ (Localization.Away c') Cc (Ideal.Quotient.mkₐ K I) c'
  have hπ₁ : Function.Surjective π₁ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective c' (Ideal.Quotient.mkₐ_surjective K I)
  let πbar : (Localization.Away b ⧸ I) →ₐ[K] Localization.Away (π b) :=
    Ideal.Quotient.liftₐ I πb (fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hφ0, hπb_alg, ht, map_zero, mul_zero])
  have hπbar : Function.Surjective πbar := Ideal.Quotient.lift_surjective_of_surjective _ _ hπb
  haveI : IsLocalization.Away (πbar (Ideal.Quotient.mk I c')) (Localization.Away (πb c')) :=
    (inferInstance : IsLocalization.Away (πb c') (Localization.Away (πb c')))
  let π₂ : Cc →ₐ[K] Localization.Away (πb c') :=
    IsLocalization.Away.mapₐ Cc (Localization.Away (πb c')) πbar (Ideal.Quotient.mk I c')
  have hπ₂ : Function.Surjective π₂ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective (Ideal.Quotient.mk I c') hπbar
  have hcomp : ∀ x, π₂ (π₁ x) = πbc x := by
    have h1 : (π₂.comp π₁).toRingHom = πbc.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers c')
      ext a
      change IsLocalization.Away.map Cc (Localization.Away (πb c')) πbar.toRingHom
        (Ideal.Quotient.mk I c') (IsLocalization.Away.map (Localization.Away c') Cc
          (Ideal.Quotient.mkₐ K I).toRingHom c' (algebraMap _ (Localization.Away c') a)) =
        IsLocalization.Away.map (Localization.Away c') (Localization.Away (πb c')) πb.toRingHom c'
          (algebraMap _ (Localization.Away c') a)
      simp only [IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    intro x
    exact congrArg (fun f : Localization.Away c' →+* Localization.Away (πb c') => f x) h1
  -- the hypersurface step and the induction hypothesis
  have hpt : (χbc.comp π₂).comp π₁ = χbc.comp πbc :=
    AlgHom.ext fun x => congrArg χbc (hcomp x)
  obtain ⟨cCc⟩ := nonempty_etaleChart_spec (K := K) (A := Cc) (n := N + d)
  have h1 := hH (Localization.Away c') Cc (N + d) cXbc cCc π₁ hπ₁
    (fun j => algebraMap (Localization.Away b) (Localization.Away c')
      (algebraMap A (Localization.Away b) (g j))) M (by omega) hM (χbc.comp π₂)
    (by rw [hpt]; exact hbadbc)
  have h2 := ih Cc (Localization.Away (πb c')) N cCc cZbc π₂ hπ₂
    (fun j => π₁ (algebraMap (Localization.Away b) (Localization.Away c')
      (algebraMap A (Localization.Away b) (g j)))) M hN hM χbc h1
  simp only [hcomp] at h2
  exact h2

/-- The restriction theorem for smooth closed subvarieties follows from the case of smooth
hypersurfaces. -/
theorem smoothRestrictionStatement_of_hypersurface (hH : SmoothRestrictionCodim K 1) :
    SmoothRestrictionStatement K := by
  apply smoothRestrictionStatement_of_forall_codim
  intro d
  induction d with
  | zero => exact smoothRestrictionCodim_zero
  | succ d ih => exact smoothRestrictionCodim_succ hH ih

end Induction

section Conclusion

/-- F1 from sum KV and the restriction theorem for smooth hypersurfaces. -/
theorem mixedFujitaFreeness_of_kvSum_of_hypersurfaceRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hH : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothRestrictionCodim K 1) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_smoothRestriction hKV
    (fun _ _ _ _ => smoothRestrictionStatement_of_hypersurface (hH _))

/-- F1 from the usual KV, big plus nef and the restriction theorem for smooth hypersurfaces. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_hypersurfaceRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hH : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothRestrictionCodim K 1) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_smoothRestriction hKV hba
    (fun _ _ _ _ => smoothRestrictionStatement_of_hypersurface (hH _))

end Conclusion

end MixedFujita
