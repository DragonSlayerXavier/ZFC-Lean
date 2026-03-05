import First_Order.FOL_Minimal

namespace FOL.Classical

export FOL.Minimal (Formula is_provable mp deduction aff_cons dist_imp conj_intro conj_elim_left conj_elim_right disj_intro_left disj_intro_right disj_elim
  forall_elim exists_intro rule_gen rule_exists_elim substF is_free_for is_free_in)

open FOL.Minimal

axiom double_neg_elim (A : Formula) : is_provable (¬¬A → A)

theorem ex_falso_classical (A : Formula) : is_provable (Formula.bot → A) := by
  sorry

theorem proof_by_contradiction (A : Formula) : is_provable ((¬A → Formula.bot) → A) := by
  sorry

theorem exists_not_iff_not_forall (A : Formula) (x : String) : is_provable ((∃ x, ¬A) ↔ ¬(∀ x, A)) := by
  sorry

theorem forall_iff_not_exists_not (A : Formula) (x : String) : is_provable ((∀ x, A) ↔ ¬(∃ x, ¬A)) := by
  sorry

theorem forall_disj_dist_left (A B : Formula) (x : String) : is_free_in x B = false -> is_provable ((∀ x, (A ∨ B)) ↔ ((∀ x, A) ∨ B)) := by
  sorry

theorem exists_imp_dist_left (A B : Formula) (x : String) : is_free_in x B = false -> is_provable ((∃ x, (A → B)) ↔ ((∀ x, A) → B)) := by
  sorry

theorem exists_imp_dist_right (A B : Formula) (x : String) : is_free_in x A = false -> is_provable ((∃ x, (A → B)) ↔ (A → (∃ x, B))) := by
  sorry


end FOL.Classical
