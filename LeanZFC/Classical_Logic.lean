import LeanZFC.Minimal_Logic

namespace ZFC

-- Double Negation Elimination
axiom double_neg_elim (A : Prop) : ¬¬A → A

-- Theorems

theorem exc_mid (A : Prop) : A ∨ ¬A := by
  sorry
