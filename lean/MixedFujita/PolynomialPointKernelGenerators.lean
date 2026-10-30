/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialLocalLinearGenerators

@[expose] public section
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
theorem polynomial_surjection_point_kernel_generators
    {K R σ : Type*} [Field K] [CommRing R] [Algebra K R]
    (φ : MvPolynomial σ K →ₐ[K] R) (hφ : Function.Surjective φ)
    (β : R →ₐ[K] K) :
    RingHom.ker β.toRingHom = Ideal.span (Set.range fun i =>
      φ (MvPolynomial.X i) - algebraMap K R (β (φ (MvPolynomial.X i)))) := by
  have h := polynomial_algHom_kernel_eq_linearIdeal (β.comp φ)
  have he : (RingHom.ker β.toRingHom).comap φ.toRingHom =
      RingHom.ker (β.comp φ).toRingHom := rfl
  calc
    RingHom.ker β.toRingHom =
        ((RingHom.ker β.toRingHom).comap φ.toRingHom).map φ.toRingHom :=
      (Ideal.map_comap_of_surjective φ.toRingHom hφ _).symm
    _ = Ideal.span (Set.range fun i =>
        φ (MvPolynomial.X i) - algebraMap K R (β (φ (MvPolynomial.X i)))) := by
      rw [he, h, Ideal.map_span, ← Set.range_comp']
      congr 1
      ext i
      simp

end MixedFujita
