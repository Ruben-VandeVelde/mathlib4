/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.Order
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Asymptotics.Theta

-- import Mathlib.Analysis.Complex.Basic

/-!
# Lemmas about asymptotics and the natural embedding `ℝ → ℂ`

In this file we prove several trivial lemmas about `Asymptotics.IsBigO` etc and `(↑) : ℝ → ℂ`.
-/

namespace Complex

noncomputable section
instance : Norm ℂ :=
  ⟨abs⟩
@[simp]
theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z :=
  rfl
#align complex.norm_eq_abs Complex.norm_eq_abs

instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
    { abs with
      map_zero' := map_zero abs
      neg' := abs.map_neg
      eq_zero_of_map_eq_zero' := fun _ => abs.eq_zero.1 }

instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul' := map_mul abs

instance : DenselyNormedField ℂ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_eq_abs, abs_ofReal, abs_of_pos (h₀.trans_lt h.1)]⟩


variable {α E : Type*} [Norm E] {l : Filter α}

theorem isTheta_ofReal (f : α → ℝ) (l : Filter α) : (f · : α → ℂ) =Θ[l] f :=
  .of_norm_left <| by simpa only [norm_eq_abs, abs_ofReal, Real.norm_eq_abs] using
    (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]
theorem isLittleO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =o[l] g ↔ f =o[l] g :=
  (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]
theorem isLittleO_ofReal_right {f : α → E} {g : α → ℝ} : f =o[l] (g · : α → ℂ) ↔ f =o[l] g :=
  (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]
theorem isBigO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =O[l] g ↔ f =O[l] g :=
  (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]
theorem isBigO_ofReal_right {f : α → E} {g : α → ℝ} : f =O[l] (g · : α → ℂ) ↔ f =O[l] g :=
  (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]
theorem isTheta_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =Θ[l] g ↔ f =Θ[l] g :=
  (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]
theorem isTheta_ofReal_right {f : α → E} {g : α → ℝ} : f =Θ[l] (g · : α → ℂ) ↔ f =Θ[l] g :=
  (isTheta_ofReal g l).isTheta_congr_right

end Complex
