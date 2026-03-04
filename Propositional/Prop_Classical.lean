import Propositional.Prop_Intuitionistic

namespace Propositional.Classical

export Propositional.Intuitionistic(Formula is_provable aff_cons dist_imp conj_intro conj_elim_left conj_elim_right
  disj_intro_left disj_intro_right disj_elim trivial neg_intro neg_elim
  iff_intro iff_elim_left iff_elim_right mp deduction)

open Propositional.Minimal
open Propositional.Intuitionistic

-- Axioms specific to Classical Logic
axiom double_neg_elim (A : Formula) : is_provable (¬¬A → A)

-- Theorems
theorem proof_by_contradiction (A : Formula) : is_provable ((¬A → Formula.bot) → A) := by
  sorry

theorem excluded_middle (A : Formula) : is_provable (A ∨ ¬A) := by
  sorry

theorem ex_falso_classical (A : Formula) : is_provable (Formula.bot → A) := by
  sorry

theorem double_neg_equiv (A : Formula) : is_provable (A ↔ ¬¬A) := by
  sorry

theorem disj_iff_not_conj_not (A B : Formula) : is_provable ((A ∨ B) ↔ ¬(¬A ∧ ¬B)) := by
  sorry

theorem conj_iff_not_disj_not (A B : Formula) : is_provable ((A ∧ B) ↔ ¬(¬A ∨ ¬B)) := by
  sorry

theorem imp_iff_not_disj (A B : Formula) : is_provable ((A → B) ↔ (¬A ∨ B)) := by
  sorry

theorem de_morgan_conj (A B : Formula) : is_provable (¬(A ∧ B) ↔ (¬A ∨ ¬B)) := by
  sorry

theorem neg_imp_iff_conj_neg (A B : Formula) : is_provable (¬(A → B) ↔ (A ∧ ¬B)) := by
  sorry

theorem contrapositive_equiv (A B : Formula) : is_provable ((A → B) ↔ (¬B → ¬A)) := by
  sorry

theorem dist_imp_conj (A B C : Formula) : is_provable ((A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))) := by
  sorry

theorem peirce_law (A B : Formula) : is_provable (((A → B) → A) → A) := by
  sorry

end Propositional.Classical
