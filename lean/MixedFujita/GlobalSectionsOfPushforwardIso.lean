module
public import MixedFujita.ComparisonImagePushbackRecovery
public import MixedFujita.ClosedImmersionCohomology

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

noncomputable def moduleIsoGlobalSectionsBaseLinearEquiv
    (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))]
    {M N : X.Modules} (e : M ≅ N) : Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) where
  toAddEquiv := (Scheme.Modules.sectionsLinearEquiv e ⊤).toAddEquiv
  map_smul' r x := by
    simp only [Scheme.Modules.base_smul_globalSections]
    exact (Scheme.Modules.sectionsLinearEquiv e ⊤).map_smul
      (Scheme.Modules.baseRingToGlobalSections R X r) x

/-- Actual scheme pushforward preserves global sections over the base ring,
using the actual over-base morphism to identify scalar multiplication. -/
noncomputable def pushforwardGlobalSectionsBaseLinearEquiv
    (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of R))] (M : X.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) where
  toAddEquiv := AddEquiv.refl _
  map_smul' r x := by
    simp only [Scheme.Modules.base_smul_globalSections]
    change f.appTop (Scheme.Modules.baseRingToGlobalSections R Y r) •
        (show Γ(M, ⊤) from x) =
      Scheme.Modules.baseRingToGlobalSections R X r • (show Γ(M, ⊤) from x)
    rw [scheme_appTop_baseRingToGlobalSections R]

noncomputable def pushforwardIsoGlobalSectionsBaseLinearEquiv
    (R : Type u) [CommRing R] {X Y B : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    [B.Over (Spec (CommRingCat.of R))]
    (q : X ⟶ B) [q.IsOver (Spec (CommRingCat.of R))]
    (β : Y ⟶ B) [β.IsOver (Spec (CommRingCat.of R))]
    (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pushforward q).obj M ≅ (Scheme.Modules.pushforward β).obj N) :
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
  (pushforwardGlobalSectionsBaseLinearEquiv R q M).symm.trans
    ((moduleIsoGlobalSectionsBaseLinearEquiv R e).trans
      (pushforwardGlobalSectionsBaseLinearEquiv R β N))

theorem pushforwardIso_global_finrank_eq
    (K : Type u) [Field K] {X Y B : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [B.Over (Spec (CommRingCat.of K))]
    (q : X ⟶ B) [q.IsOver (Spec (CommRingCat.of K))]
    (β : Y ⟶ B) [β.IsOver (Spec (CommRingCat.of K))]
    (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pushforward q).obj M ≅ (Scheme.Modules.pushforward β).obj N) :
    Module.finrank K Γ(M, ⊤) = Module.finrank K Γ(N, ⊤) :=
  (pushforwardIsoGlobalSectionsBaseLinearEquiv K q β M N e).finrank_eq

variable {K : Type u} [Field K] {B B' T T' : Scheme.{u}}
    [IsIntegral B] [IsIntegral B'] [IsIntegral T] [IsIntegral T']
    [B.Over (Spec (CommRingCat.of K))] [B'.Over (Spec (CommRingCat.of K))]
    [T.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian B']

theorem actualRelativeAdjointMultiple_principalized_globalSections_linearEquiv
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf)) :
    ∀ j : ℕ, Nonempty (Γ((j • L + E).sheaf, ⊤) ≃ₗ[K]
      Γ((j • cartierPullback β A + (cartierPullback β C - P)).sheaf, ⊤)) := by
  intro j
  obtain ⟨i⟩ := actualRelativeAdjointMultiple_principalized_pushforward_iso
    (β := β) hProj hProj' q q' τ hsquare A C L E E' χ hL I hI s P hP hIP e j
  exact ⟨pushforwardIsoGlobalSectionsBaseLinearEquiv K q β _ _ i⟩

theorem actualRelativeAdjointMultiple_principalized_h0_eq
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (hProj' : ∃ A : CartierDivisor B', CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] [q.IsOver (Spec (CommRingCat.of K))]
    (β : B' ⟶ B) [IsDominant β] [β.IsOver (Spec (CommRingCat.of K))]
    (q' : T' ⟶ B') [IsDominant q'] (τ : T' ⟶ T) [IsDominant τ]
    (hsquare : τ ≫ q = q' ≫ β)
    (A C : CartierDivisor B) (L E : CartierDivisor T) (E' : CartierDivisor T')
    (χ : T.functionFieldˣ)
    (hL : L = cartierPullback q A + principalCartierDivisor T χ)
    (I : B.IdealSheafData) (hI : I ≠ ⊥) [(idealSheafDataModule I).IsQuasicoherent]
    (s : (Scheme.Modules.pushforward q).obj E.sheaf ≅ C.sheaf ⊗ idealSheafDataModule I)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E'.sheaf)) :
    ∀ j : ℕ, Module.finrank K Γ((j • L + E).sheaf, ⊤) =
      Module.finrank K Γ((j • cartierPullback β A + (cartierPullback β C - P)).sheaf, ⊤) := by
  intro j
  obtain ⟨i⟩ := actualRelativeAdjointMultiple_principalized_globalSections_linearEquiv
    hProj hProj' q β q' τ hsquare A C L E E' χ hL I hI s P hP hIP e j
  exact i.finrank_eq

end MixedFujita
