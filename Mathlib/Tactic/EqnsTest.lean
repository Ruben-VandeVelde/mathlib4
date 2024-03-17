import Mathlib.Tactic.Eqns
import Mathlib.Tactic.EqnsTest2
universe u₁ u₂ u₃ u₄ u₅

namespace Function

-- Porting note: fix the universe of `ζ`, it used to be `u₁`
variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}

theorem flip_def {f : α → β → φ} : flip f = fun b a => f a b := rfl

attribute [eqns flip_def] flip

theorem Rel.extracted_1 {α : Type _} {β : Type _} :
    (flip fun (_ : α) (_ : β) ↦ True) = fun _ _ ↦ True := by
  simp [flip]

example : True := by
  have (f : Nat → Nat → Nat) (a b : Nat) : flip f a = (f · a) := by simp [flip]
  trivial
