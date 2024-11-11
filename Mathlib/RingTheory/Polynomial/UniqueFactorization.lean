/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Content

/-!
# Unique factorization for univariate and multivariate polynomials

## Main results
* `Polynomial.uniqueFactorizationMonoid`, `MvPolynomial.uniqueFactorizationMonoid`:
  If an integral domain is a `UniqueFactorizationMonoid`, then so is its polynomial ring (of any
  number of variables).
-/

noncomputable section

open Polynomial

universe u v

section UniqueFactorizationDomain

variable (σ : Type v) {D : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]

open UniqueFactorizationMonoid

namespace Polynomial

instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] := by
  letI := Classical.arbitrary (NormalizedGCDMonoid D)
  exact ufm_of_decomposition_of_wfDvdMonoid

/-- If `D` is a unique factorization domain, `f` is a non-zero polynomial in `D[X]`, then `f` has
only finitely many monic factors.
(Note that its factors up to unit may be more than monic factors.)
See also `UniqueFactorizationMonoid.fintypeSubtypeDvd`. -/
noncomputable def fintypeSubtypeMonicDvd (f : D[X]) (hf : f ≠ 0) :
    Fintype { g : D[X] // g.Monic ∧ g ∣ f } := by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y ≠ 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G → H := fun x ↦ ⟨Associates.mk x.1, Associates.mk_dvd_mk.2 x.2.2⟩
  refine Fintype.ofInjective i fun x y heq ↦ ?_
  rw [Subtype.mk.injEq] at heq ⊢
  exact eq_of_monic_of_associated x.2.1 y.2.1 (Associates.mk_eq_mk_iff_associated.mp heq)

end Polynomial

namespace MvPolynomial
variable (d : ℕ)

private theorem uniqueFactorizationMonoid_of_fintype [Fintype σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  (renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid <| by
    induction' Fintype.card σ with d hd
    · apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    · apply (finSuccEquiv D d).toMulEquiv.symm.uniqueFactorizationMonoid
      exact Polynomial.uniqueFactorizationMonoid

instance (priority := 100) uniqueFactorizationMonoid :
    UniqueFactorizationMonoid (MvPolynomial σ D) := by
  rw [iff_exists_prime_factors]
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
  obtain ⟨w, h, u, hw⟩ :=
    iff_exists_prime_factors.1 (uniqueFactorizationMonoid_of_fintype s) a' fun h =>
      ha <| by simp [h]
  exact
    ⟨w.map (rename (↑)), fun b hb =>
      let ⟨b', hb', he⟩ := Multiset.mem_map.1 hb
      he ▸ (prime_rename_iff ↑s).2 (h b' hb'),
      Units.map (@rename s σ D _ (↑)).toRingHom.toMonoidHom u, by
      erw [Multiset.prod_hom, ← map_mul, hw]⟩

end MvPolynomial

end UniqueFactorizationDomain

/-- A polynomial over a field which is not a unit must have a monic irreducible factor.
See also `WfDvdMonoid.exists_irreducible_factor`. -/
theorem Polynomial.exists_monic_irreducible_factor {F : Type*} [Field F] (f : F[X])
    (hu : ¬IsUnit f) : ∃ g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f := by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
  have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _ <|
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨_, monic_mul_leadingCoeff_inv hi.ne_zero, ha.irreducible hi, ha.dvd_iff_dvd_left.1 hf⟩
