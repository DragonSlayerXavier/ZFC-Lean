import Propositional.Prop_Minimal

namespace Propositional.Intuitionistic

export Propositional.Minimal(Formula is_provable aff_cons dist_imp conj_intro conj_elim_left conj_elim_right
  disj_intro_left disj_intro_right disj_elim trivial neg_intro neg_elim
  iff_intro iff_elim_left iff_elim_right mp deduction)

open Propositional.Minimal

-- Axioms specific to Intuitionistic Logic
axiom ex_falso (A : Formula) : is_provable (Formula.bot → A)

-- Theorems
theorem bot_iff_conj_neg (A : Formula) : is_provable (Formula.bot ↔ (A ∧ ¬A)) := by
  sorry

theorem neg_to_imp (A B : Formula) : is_provable (¬A → (A → B)) := by
  sorry

theorem neg_disj_to_imp (A B : Formula) : is_provable ((¬A ∨ B) → (A → B)) := by
  sorry

theorem disj_to_neg_imp (A B : Formula) : is_provable ((A ∨ B) → (¬A → B)) := by
  sorry

theorem neg_imp_to_double_neg (A B : Formula) : is_provable (¬(A → B) → ¬¬A) := by
  sorry

theorem double_neg_imp_equiv (A B : Formula) : is_provable (¬¬(A → B) ↔ (¬¬A → ¬¬B)) := by
  sorry

theorem disj_bot_iff_self (A : Formula) : is_provable ((A ∨ Formula.bot) ↔ A) := by
  sorry

theorem conj_bot_iff_bot (A : Formula) : is_provable ((A ∧ Formula.bot) ↔ Formula.bot) := by
  sorry

end Propositional.Intuitionistic
