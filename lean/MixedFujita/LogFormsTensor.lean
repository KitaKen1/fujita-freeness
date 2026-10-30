/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogFormsCoherent
public import MixedFujita.TwistedFormsTensor

/-!
`𝒪_X(E) ⊗ Ω^b_X(log G)(F) ≅ Ω^b_X(log G)(E + F)` (step 10, R2).

The argument of check 419 uses only the local condition defining the twisted forms and its
stability under the local rings, so it applies to the logarithmic forms of check 476. A section of
`𝒪_X(E)` times a section of `Ω^b_X(log G)(F)` is a section of `Ω^b_X(log G)(E + F)`
(`logFormsMul_mem`). On an open subset carrying an equation `g` of `E`, `ω ↦ g⁻¹ ⊗ g ω` retracts the
multiplication, which is therefore locally bijective, and its sheafification is an isomorphism
(`logTensorSheafIso`).

With the coherence of `Ω^b_X(log G)` (check 480), every `Ω^b_X(log G)(F)` is coherent
(`isCoherent_logFormsSheaf`), and the Serre vanishing theorem applies: for `H` ample,
`Hⁱ(Ω^b_X(log G)(m H + F)) = 0` for `i > 0` and `m ≫ 0` (`logFormsSheaf_serreVanishing`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {r : ℕ} {G : Fin r → CartierDivisor X}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- **A section of `𝒪_X(E)` times a logarithmic form with poles bounded by `F` is one with poles
bounded by `E + F`.** -/
theorem logFormsMul_mem {E F : CartierDivisor X} {b : ℕ} {U : X.Opens}
    {a : Γ(rationalFunctions X, U)} {t : Γ(rationalFormsSheaf K X b, U)}
    (ha : a ∈ E.sections U) (ht : t ∈ logFormsSections K G F b U) :
    formsMul K b U a t ∈ logFormsSections K G (E + F) b U := by
  refine (mem_logFormsSections_iff_exists _).mpr fun x hx => ?_
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨f, hf⟩ := E.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := F.exists_isLocalEquationAt x
  refine ⟨f * g, hf.mul hg, ?_⟩
  obtain ⟨c, hc⟩ := (CartierDivisor.mem_sections.mp ha) x hx f hf
  have hgt := ht x hx g hg
  rw [rationalFormsSectionsEquiv_formsMul, smul_smul, Units.val_mul,
    show (f : X.functionField) * g * rationalFunctionsEquiv U a =
      (f * rationalFunctionsEquiv U a) * g by ring, mul_smul, ← hc, algebraMap_smul]
  exact Submodule.smul_mem _ c hgt

variable (K G) in
/-- Multiplication of sections,
`Γ(𝒪_X(E), U) × Γ(Ω^b_X(log G)(F), U) → Γ(Ω^b_X(log G)(E + F), U)`. -/
noncomputable def logSectionsMul (E F : CartierDivisor X) (b : ℕ) (U : X.Opens)
    (s : Γ(E.sheaf, U)) (t : Γ(logFormsSheaf K G F b, U)) :
    Γ(logFormsSheaf K G (E + F) b, U) :=
  ⟨formsMul K b U (Scheme.Modules.Hom.app E.sheafι U s) t.1,
    logFormsMul_mem (CartierDivisor.sheafι_app_mem E U s) t.2⟩

theorem logSectionsMul_val (E F : CartierDivisor X) (b : ℕ) (U : X.Opens)
    (s : Γ(E.sheaf, U)) (t : Γ(logFormsSheaf K G F b, U)) :
    (logSectionsMul K G E F b U s t).1 = formsMul K b U (Scheme.Modules.Hom.app E.sheafι U s) t.1 :=
  rfl

variable {E F : CartierDivisor X} {b : ℕ} {U : X.Opens}

theorem logSectionsMul_add_left (s s' : Γ(E.sheaf, U)) (t : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMul K G E F b U (s + s') t =
      logSectionsMul K G E F b U s t + logSectionsMul K G E F b U s' t :=
  Subtype.ext (by
    rw [Submodule.coe_add, logSectionsMul_val, logSectionsMul_val, logSectionsMul_val,
      map_add, formsMul_add_left])

theorem logSectionsMul_add_right (s : Γ(E.sheaf, U)) (t t' : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMul K G E F b U s (t + t') =
      logSectionsMul K G E F b U s t + logSectionsMul K G E F b U s t' :=
  Subtype.ext (by
    rw [Submodule.coe_add, logSectionsMul_val, logSectionsMul_val, logSectionsMul_val,
      Submodule.coe_add, formsMul_add_right])

theorem logSectionsMul_smul_left (r : Γ(X, U)) (s : Γ(E.sheaf, U))
    (t : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMul K G E F b U (r • s) t = r • logSectionsMul K G E F b U s t :=
  Subtype.ext (by
    rw [Submodule.coe_smul, logSectionsMul_val, logSectionsMul_val,
      Scheme.Modules.Hom.app_smul, formsMul_smul_left])

theorem logSectionsMul_smul_right (r : Γ(X, U)) (s : Γ(E.sheaf, U))
    (t : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMul K G E F b U s (r • t) = r • logSectionsMul K G E F b U s t :=
  Subtype.ext (by
    rw [Submodule.coe_smul, logSectionsMul_val, logSectionsMul_val, Submodule.coe_smul,
      formsMul_smul_right])

/-- Restriction commutes with multiplication of sections. -/
theorem logSectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(E.sheaf, U))
    (t : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMul K G E F b V (E.sheaf.presheaf.map i.op s)
        ((logFormsSheaf K G F b).presheaf.map i.op t) =
      (logFormsSheaf K G (E + F) b).presheaf.map i.op (logSectionsMul K G E F b U s t) := by
  apply Subtype.ext
  have h := NatTrans.naturality_apply (CartierDivisor.sheafι E).mapPresheaf i.op s
  simp only [Scheme.Modules.mapPresheaf_app] at h
  change formsMul K b V (Scheme.Modules.Hom.app E.sheafι V (E.sheaf.presheaf.map i.op s))
      ((rationalFormsSheaf K X b).presheaf.map i.op t.1) =
    (rationalFormsSheaf K X b).presheaf.map i.op (formsMul K b U
      (Scheme.Modules.Hom.app E.sheafι U s) t.1)
  rw [h, formsMul_map]

variable (K G E F b U) in
/-- Multiplication, linear on the tensor product of the sections. -/
noncomputable def logSectionsMulLift :
    TensorProduct Γ(X, U) Γ(E.sheaf, U) Γ(logFormsSheaf K G F b, U) →ₗ[Γ(X, U)]
      Γ(logFormsSheaf K G (E + F) b, U) :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, U) (logSectionsMul K G E F b U)
    (fun s s' t ↦ logSectionsMul_add_left s s' t)
    (fun r s t ↦ logSectionsMul_smul_left r s t)
    (fun s t t' ↦ logSectionsMul_add_right s t t')
    (fun r s t ↦ logSectionsMul_smul_right r s t)

theorem logSectionsMulLift_tmul (s : Γ(E.sheaf, U)) (t : Γ(logFormsSheaf K G F b, U)) :
    logSectionsMulLift K G E F b U (s ⊗ₜ t) = logSectionsMul K G E F b U s t :=
  rfl

variable (K G E F b) in
/-- The multiplication morphism of presheaves of modules. -/
noncomputable def logTensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) E.sheaf.val
      (logFormsSheaf K G F b).val ⟶ (logFormsSheaf K G (E + F) b).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ logSectionsMul K G E F b U.unop s t)
    (fun s s' t ↦ logSectionsMul_add_left s s' t)
    (fun r s t ↦ logSectionsMul_smul_left r s t)
    (fun s t t' ↦ logSectionsMul_add_right s t t')
    (fun r s t ↦ logSectionsMul_smul_right r s t)
  naturality f := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ logSectionsMul_map f.unop s t

theorem logTensorPresheafHom_app :
    ModuleCat.Hom.hom (R := X.sheaf.obj.obj (op U)) ((logTensorPresheafHom K G E F b).app (op U)) =
      logSectionsMulLift K G E F b U :=
  TensorProduct.ext' fun s t ↦ (logSectionsMulLift_tmul s t).symm

section LocalEquation

variable {V : X.Opens} [Nonempty V] {g : X.functionFieldˣ}
  (hg : ∀ x ∈ V, E.IsLocalEquationAt x g)

include hg

/-- Multiplying a form with poles bounded by `E + F` by an equation of `E` bounds its poles by
`F`. -/
theorem smul_localEquation_mem_log (ω : Γ(rationalFormsSheaf K X b, V))
    (hω : ω ∈ logFormsSections K G (E + F) b V) :
    (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω) ∈
      logFormsSections K G F b V := by
  intro x hx h hh
  rw [AddEquiv.apply_symm_apply, smul_smul, mul_comm]
  have := hω x hx (g * h) ((hg x hx).mul hh)
  rwa [Units.val_mul] at this

variable (K G F b) in
/-- The section `g • ω` of `Ω^b_X(log G)(F)` for a section `ω` of `Ω^b_X(log G)(E + F)`. -/
noncomputable def logLocalEquationSmulSection (ω : Γ(logFormsSheaf K G (E + F) b, V)) :
    Γ(logFormsSheaf K G F b, V) :=
  ⟨(rationalFormsSectionsEquiv K b V).symm
      ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1),
    smul_localEquation_mem_log hg ω.1 ω.2⟩

theorem logSectionsMul_inv_smul (ω : Γ(logFormsSheaf K G (E + F) b, V)) :
    logSectionsMul K G E F b V (invLocalEquationSection hg)
        (logLocalEquationSmulSection K G F b hg ω) = ω := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b V).injective
  rw [logSectionsMul_val, rationalFormsSectionsEquiv_formsMul,
    rationalFunctionsEquiv_invLocalEquationSection]
  change ((g : X.functionField))⁻¹ • rationalFormsSectionsEquiv K b V
    ((rationalFormsSectionsEquiv K b V).symm ((g : X.functionField) •
      rationalFormsSectionsEquiv K b V ω.1)) = _
  rw [AddEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ g.ne_zero, one_smul]

/-- Multiplication of sections is surjective on a domain of an equation of `E`. -/
theorem exists_logSectionsMul_eq (ω : Γ(logFormsSheaf K G (E + F) b, V)) :
    ∃ (a : Γ(E.sheaf, V)) (t : Γ(logFormsSheaf K G F b, V)),
      logSectionsMul K G E F b V a t = ω :=
  ⟨_, _, logSectionsMul_inv_smul hg ω⟩

variable (K G F b) in
/-- Multiplication by the equation `g` gives a linear retraction of the multiplication. -/
noncomputable def logRetraction :
    Γ(logFormsSheaf K G (E + F) b, V) →ₗ[Γ(X, V)]
      TensorProduct Γ(X, V) Γ(E.sheaf, V) Γ(logFormsSheaf K G F b, V) where
  toFun ω := invLocalEquationSection hg ⊗ₜ logLocalEquationSmulSection K G F b hg ω
  map_add' ω ω' := by
    rw [← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V (ω.1 + ω'.1))) =
      rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1) +
        (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω'.1))
    rw [map_add, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, smul_add]
  map_smul' r ω := by
    rw [RingHom.id_apply, ← TensorProduct.tmul_smul]
    congr 1
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V (r • ω.1))) =
      rationalFormsSectionsEquiv K b V (r • (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1))
    rw [AddEquiv.apply_symm_apply, rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_smul,
      AddEquiv.apply_symm_apply, smul_comm]

/-- Multiplication by the equation `g` retracts the multiplication. -/
theorem logRetraction_logSectionsMul (a : Γ(E.sheaf, V))
    (t : Γ(logFormsSheaf K G F b, V)) :
    logRetraction K G F b hg (logSectionsMul K G E F b V a t) = a ⊗ₜ t := by
  obtain ⟨r, hr⟩ := exists_germ_eq_localEquation_mul hg a
  have h1 : logLocalEquationSmulSection K G F b hg (logSectionsMul K G E F b V a t) = r • t := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V
          (logSectionsMul K G E F b V a t).1)) = rationalFormsSectionsEquiv K b V (r • t.1)
    rw [AddEquiv.apply_symm_apply, logSectionsMul_val, rationalFormsSectionsEquiv_formsMul,
      rationalFormsSectionsEquiv_smul, hr, smul_smul]
  have h2 : r • invLocalEquationSection hg = a := by
    apply CartierDivisor.sheafι_app_injective E V
    apply (rationalFunctionsEquiv V).injective
    rw [Scheme.Modules.Hom.app_smul, map_smul, rationalFunctionsEquiv_invLocalEquationSection,
      Algebra.smul_def]
    change X.germToFunctionField V r * _ = _
    rw [hr, mul_comm (g : X.functionField), mul_assoc, mul_inv_cancel₀ g.ne_zero, mul_one]
  change invLocalEquationSection hg ⊗ₜ
    logLocalEquationSmulSection K G F b hg (logSectionsMul K G E F b V a t) = a ⊗ₜ t
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', h2]

/-- Multiplication is injective on a domain of an equation of `E`. -/
theorem logSectionsMulLift_injective : Function.Injective (logSectionsMulLift K G E F b V) := by
  have key : Function.LeftInverse (logRetraction K G F b hg) (logSectionsMulLift K G E F b V) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a t =>
      rw [logSectionsMulLift_tmul]
      exact logRetraction_logSectionsMul hg a t
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  exact key.injective

end LocalEquation

variable (K G E F b) in
theorem isLocallySurjective_logTensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (logTensorPresheafHom K G E F b)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_forall_isLocalEquationAt_le E U hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, t, hat⟩ := exists_logSectionsMul_eq (K := K) (F := F) (b := b) hg
      ((logFormsSheaf K G (E + F) b).presheaf.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨a ⊗ₜ t, hat⟩, hxV⟩

variable (K G E F b) in
theorem isLocallyInjective_logTensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (logTensorPresheafHom K G E F b)) where
  equalizerSieve_mem {U} z z' h x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_forall_isLocalEquationAt_le E U.unop hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    refine ⟨V, homOfLE hVU, logSectionsMulLift_injective (K := K) (F := F) (b := b) hg ?_, hxV⟩
    exact (PresheafOfModules.naturality_apply (logTensorPresheafHom K G E F b) (homOfLE hVU).op
      z).trans ((congrArg ((logFormsSheaf K G (E + F) b).val.map (homOfLE hVU).op) h).trans
        (PresheafOfModules.naturality_apply (logTensorPresheafHom K G E F b) (homOfLE hVU).op
          z').symm)

variable (K G E F b) in
theorem isIso_sheafification_map_logTensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (logTensorPresheafHom K G E F b)) := by
  have := isLocallySurjective_logTensorPresheafHom K G E F b
  have := isLocallyInjective_logTensorPresheafHom K G E F b
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (logTensorPresheafHom K G E F b)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

variable (K G E F b) in
/-- **`𝒪_X(E) ⊗ Ω^b_X(log G)(F) ≅ Ω^b_X(log G)(E + F)`.** -/
noncomputable def logTensorSheafIso :
    E.sheaf ⊗ logFormsSheaf K G F b ≅ logFormsSheaf K G (E + F) b :=
  E.sheaf.tensorUnderlyingIso (logFormsSheaf K G F b) ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_logTensorPresheafHom K G E F b) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (logFormsSheaf K G (E + F) b)

variable (K G) in
/-- **`𝒪_X(F) ⊗ Ω^b_X(log G) ≅ Ω^b_X(log G)(F)`.** -/
noncomputable def cartierTensorLogFormsIso (F : CartierDivisor X) (b : ℕ) :
    F.sheaf ⊗ logFormsSheaf K G 0 b ≅ logFormsSheaf K G F b :=
  logTensorSheafIso K G F 0 b ≪≫ eqToIso (congrArg (fun D => logFormsSheaf K G D b) (add_zero F))

section Coherent

variable {n : ℕ} [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (hGc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (G k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hsnc : IsSNCFamily K n ξ)

include hnorm hinj hξ hGc hsnc in
/-- **`Ω^b_X(log G)(F)` is coherent.** -/
theorem isCoherent_logFormsSheaf (F : CartierDivisor X) (b : ℕ) :
    (logFormsSheaf K G F b).IsCoherent := by
  have := isCoherent_logFormsSheaf_zero hnorm ξ hinj hξ G hGc hsnc b
  have := cartierTensorModule_isCoherent F (logFormsSheaf K G 0 b)
  let a := cartierTensorLogFormsIso K G F b
  have : (F.sheaf ⊗ logFormsSheaf K G 0 b).IsQuasicoherent :=
    Scheme.Modules.IsCoherent.isQuasicoherent
  have : (F.sheaf ⊗ logFormsSheaf K G 0 b).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩

include hnorm hinj hξ hGc hsnc in
/-- **Serre vanishing for `Ω^b_X(log G)(m H + F)`**, `H` ample: `Hⁱ = 0` for `i > 0` and
`m ≫ 0`. -/
theorem logFormsSheaf_serreVanishing (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (F : CartierDivisor X) (b : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ q : ℕ,
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (logFormsSheaf K G (m • H + F) b) (q + 1)) := by
  have := isCoherent_logFormsSheaf hnorm ξ hinj hξ hGc hsnc F b
  obtain ⟨m₀, hm₀⟩ := cartierIsAmpleProj_coherent_tensor_serreVanishing H hH
    (logFormsSheaf K G F b)
  refine ⟨m₀, fun m hm q => ?_⟩
  have h := hm₀ m hm q
  let e := ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X (q + 1)).mapIso
    (logTensorSheafIso K G (m • H) F b)).addCommGroupIsoToAddEquiv
  exact @Equiv.subsingleton _ _ e.symm.toEquiv h

end Coherent

end MixedFujita
