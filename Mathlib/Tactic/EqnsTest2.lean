
theorem Rel.extracted_2 (f : Nat → Nat → Nat) (a b : Nat) : flip f a b = (f b a) := by rw [flip]
