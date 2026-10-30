/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtalePolynomialDifferentials
public import MixedFujita.EtalePointBlowupExceptionalRestriction
public import MixedFujita.PointBlowupDifferentialDeterminant

/-! Constructed differential bases on actual étale base-change blow-up charts.
The determinant of the actual pulled-back source coordinates is x_k^(n-1),
with no supplied differential basis. The field action is induced by the actual
chart projection to polynomial affine space. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {n : ℕ}
  {f : X ⟶ Spec (.of K)} {Z : X.IdealSheafData} {x : X}

noncomputable def etalePointBlowupStalkCoords (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) :
    MvPolynomial (Fin n) K →+* (etalePointBlowupChart E k).presheaf.stalk p :=
  ((etalePointBlowupChart E k).presheaf.germ V.1 p hp).hom.comp
    (sectionsHom (pullback.snd (etalePointBlowupModelMap E)
      (CoordinateSubspace.modelChart K n n k k.isLt)) V.1)

theorem etalePointBlowupStalkCoords_formallyEtale (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) :
    (etalePointBlowupStalkCoords E k V p hp).FormallyEtale :=
  etalePolynomial_stalkMap_formallyEtale _ V p hp

noncomputable def etalePointBlowupStalkDifferentialBasis (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) :
    let τ := etalePointBlowupStalkCoords E k V p hp
    let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
      (τ.comp MvPolynomial.C).toAlgebra
    Module.Basis (Fin n) ((etalePointBlowupChart E k).presheaf.stalk p)
      Ω[((etalePointBlowupChart E k).presheaf.stalk p)⁄K] := by
  let τ := etalePointBlowupStalkCoords E k V p hp
  let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
    (τ.comp MvPolynomial.C).toAlgebra
  exact polynomialRingHomDifferentialBasis τ (etalePointBlowupStalkCoords_formallyEtale E k V p hp)

theorem etalePointBlowupStalkDifferentialBasis_apply (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) (i : Fin n) :
    let τ := etalePointBlowupStalkCoords E k V p hp
    let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
      (τ.comp MvPolynomial.C).toAlgebra
    etalePointBlowupStalkDifferentialBasis E k V p hp i =
      KaehlerDifferential.D K ((etalePointBlowupChart E k).presheaf.stalk p) (τ (MvPolynomial.X i)) := by
  let τ := etalePointBlowupStalkCoords E k V p hp
  let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
    (τ.comp MvPolynomial.C).toAlgebra
  exact polynomialRingHomDifferentialBasis_apply τ _ i

noncomputable def etalePointBlowupSourceStalkCoords (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) :
    MvPolynomial (Fin n) K →+* (etalePointBlowupChart E k).presheaf.stalk p :=
  ((etalePointBlowupChart E k).presheaf.germ V.1 p hp).hom.comp
    (sectionsHom (pullback.fst (etalePointBlowupModelMap E)
      (CoordinateSubspace.modelChart K n n k k.isLt) ≫
        Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι) ≫ toAffineSpace f E.U.1 E.v) V.1)

theorem etalePointBlowupSourceStalkCoords_substitution (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) (V : (etalePointBlowupChart E k).affineOpens)
    (p : etalePointBlowupChart E k) (hp : p ∈ V.1) (g : MvPolynomial (Fin n) K) :
    etalePointBlowupSourceStalkCoords E k V p hp g =
      etalePointBlowupStalkCoords E k V p hp (polynomialPointBlowupMap k g) :=
  congrArg ((etalePointBlowupChart E k).presheaf.germ V.1 p hp)
    (etalePointBlowupChart_coordinatePolynomial_pullback E k V.1 g)

theorem formallyEtale_pointBlowup_determinant {A : Type*} [CommRing A]
    (τ : MvPolynomial (Fin n) K →+* A) (hτ : τ.FormallyEtale) (k : Fin n) :
    let : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
    (polynomialRingHomDifferentialBasis τ hτ).det
      (fun i => KaehlerDifferential.D K A (τ (polynomialPointBlowupMap k (MvPolynomial.X i)))) =
        τ (MvPolynomial.X k) ^ (n - 1) := by
  classical
  let : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
  apply pointBlowup_kaehler_determinant (K := K) (fun i => τ (MvPolynomial.X i))
    (fun i => τ (polynomialPointBlowupMap k (MvPolynomial.X i))) k _
    (polynomialRingHomDifferentialBasis τ hτ) (polynomialRingHomDifferentialBasis_apply τ hτ)
  intro i
  by_cases hi : i = k
  · subst i
    rw [polynomialPointBlowupMap_X_self, ite_eq_left rfl]
  · rw [polynomialPointBlowupMap_X_other k i hi, map_mul, ite_eq_right hi]

theorem etalePointBlowupStalk_actual_differential_determinant
    (E : EtaleCoordinatesAdapted f n n Z x) (k : Fin n)
    (V : (etalePointBlowupChart E k).affineOpens) (p : etalePointBlowupChart E k) (hp : p ∈ V.1) :
    let τ := etalePointBlowupStalkCoords E k V p hp
    let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
      (τ.comp MvPolynomial.C).toAlgebra
    (etalePointBlowupStalkDifferentialBasis E k V p hp).det
      (fun i => KaehlerDifferential.D K ((etalePointBlowupChart E k).presheaf.stalk p)
        (etalePointBlowupSourceStalkCoords E k V p hp (MvPolynomial.X i))) =
          τ (MvPolynomial.X k) ^ (n - 1) := by
  let τ := etalePointBlowupStalkCoords E k V p hp
  let : Algebra K ((etalePointBlowupChart E k).presheaf.stalk p) :=
    (τ.comp MvPolynomial.C).toAlgebra
  simp only [etalePointBlowupSourceStalkCoords_substitution]
  exact formallyEtale_pointBlowup_determinant τ (etalePointBlowupStalkCoords_formallyEtale E k V p hp) k

end MixedFujita
