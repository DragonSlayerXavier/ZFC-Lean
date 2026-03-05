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
  have hfwd : is_provable (Formula.bot → (A ∧ ¬A)) := by
    exact ex_falso (A ∧ ¬A)
  have hbwd : is_provable ((A ∧ ¬A) → Formula.bot) := by
    apply deduction
    intro ana
    have ha: is_provable (A) := by
      exact mp (conj_elim_left A (¬A)) ana
    have hna: is_provable (¬A) := by
      exact mp (conj_elim_right A (¬A)) ana
    exact mp (mp (neg_elim A) hna) ha
  exact mp (mp (iff_intro (Formula.bot) ((A ∧ ¬A))) hfwd) hbwd

theorem neg_to_imp (A B : Formula) : is_provable (¬A → (A → B)) := by
  apply deduction
  intro hna
  apply deduction
  intro ha
  have hf: is_provable (Formula.bot) := by
    exact mp (mp (neg_elim A) hna) ha
  exact mp (ex_falso B) hf

theorem neg_disj_to_imp (A B : Formula) : is_provable ((¬A ∨ B) → (A → B)) := by
  apply deduction
  intro h
  apply deduction
  intro ha
  have h_cases : is_provable ((¬A → B) → ((B → B) → ((¬A ∨ B) → B))) := by
    exact disj_elim (¬A) B B
  have h_case_na : is_provable (¬A → B) := by
    apply deduction
    intro hna
    exact mp (mp (neg_to_imp A B) hna) ha
  have h_case_b : is_provable (B → B) := by
    apply deduction
    intro hb
    exact hb
  exact mp (mp (mp h_cases h_case_na) h_case_b) h

theorem disj_to_neg_imp (A B : Formula) : is_provable ((A ∨ B) → (¬A → B)) := by
  apply deduction
  intro h
  apply deduction
  intro hna
  have h_cases : is_provable ((A → (¬A → B)) → ((B → (¬A → B)) → ((A ∨ B) → (¬A → B)))) := by
    exact disj_elim A B (¬A → B)
  have h_case_a : is_provable (A → (¬A → B)) := by
    apply deduction
    intro ha
    apply deduction
    intro hna
    have hf: is_provable (Formula.bot) := by
      exact mp (mp (neg_elim A) hna) ha
    exact mp (ex_falso B) hf
  have h_case_b : is_provable (B → (¬A → B)) := by
    apply deduction
    intro hb
    apply deduction
    intro hna
    exact hb
  have h_imp_na_b: is_provable (¬A → B) := by
    exact mp (mp (mp h_cases h_case_a) h_case_b) h
  exact mp h_imp_na_b hna

theorem neg_imp_to_double_neg (A B : Formula) : is_provable (¬(A → B) → ¬¬A) := by
  apply deduction
  intro h
  apply mp (neg_intro (¬A))
  apply deduction
  intro hna
  have hab: is_provable (A → B) := by
    apply deduction
    intro ha
    have hf: is_provable (Formula.bot) := by
      exact mp (mp (neg_elim A) hna) ha
    exact mp (ex_falso B) hf
  exact mp (mp (neg_elim (A → B)) h) hab

theorem double_neg_imp_equiv (A B : Formula) : is_provable (¬¬(A → B) ↔ (¬¬A → ¬¬B)) := by
  have hfwd : is_provable (¬¬(A → B) → (¬¬A → ¬¬B)) := by
    apply deduction
    intro hnnab
    apply deduction
    intro hnna
    apply mp (neg_intro (¬B))
    apply deduction
    intro hnb
    have hnb_to_hnab : is_provable (¬B → ¬(A → B)) := by
      apply deduction
      intro hnb'
      apply mp (neg_intro (A → B))
      apply deduction
      intro hab
      have hna : is_provable (¬A) := by
        exact mp (mp (imp_contrapositive A B) hab) hnb'
      exact mp (mp (neg_elim (¬A)) hnna) hna
    have hnab : is_provable (¬(A → B)) := by
      exact mp hnb_to_hnab hnb
    exact mp (mp (neg_elim (¬(A → B))) hnnab) hnab
  have hbwd : is_provable ((¬¬A → ¬¬B) → ¬¬(A → B)) := by
    apply deduction
    intro hnn_imp
    apply mp (neg_intro (¬(A → B)))
    apply deduction
    intro hnab
    have hnna : is_provable (¬¬A) := by
      exact mp (neg_imp_to_double_neg A B) hnab
    have hnnb : is_provable (¬¬B) := by
      exact mp hnn_imp hnna
    have hnb : is_provable (¬B) := by
      exact mp (imp_neg_elim A B) hnab
    exact mp (mp (neg_elim (¬B)) hnnb) hnb
  exact mp (mp (iff_intro (¬¬(A → B)) (¬¬A → ¬¬B)) hfwd) hbwd

theorem disj_bot_iff_self (A : Formula) : is_provable ((A ∨ Formula.bot) ↔ A) := by
  have hfwd : is_provable ((A ∨ Formula.bot) → A) := by
    apply deduction
    intro h
    have h_cases : is_provable ((A → A) → (Formula.bot → A) → (A ∨ Formula.bot) → A) := by
      exact disj_elim A (Formula.bot) A
    have h_id : is_provable (A → A) := by
      apply Propositional.Minimal.self_imp
    have h_bot : is_provable (Formula.bot → A) := by
      exact ex_falso A
    exact mp (mp (mp h_cases h_id) h_bot) h
  have hbwd : is_provable (A → (A ∨ Formula.bot)) := by
    apply deduction
    intro ha
    exact mp (disj_intro_left A (Formula.bot)) ha
  exact mp (mp (iff_intro (A ∨ Formula.bot) A) hfwd) hbwd

theorem conj_bot_iff_bot (A : Formula) : is_provable ((A ∧ Formula.bot) ↔ Formula.bot) := by
  have hfwd : is_provable ((A ∧ Formula.bot) → Formula.bot) := by
    apply deduction
    intro h
    exact mp (conj_elim_right A Formula.bot) h
  have hbwd : is_provable (Formula.bot → (A ∧ Formula.bot)) := by
    apply deduction
    intro hf
    exact mp (ex_falso (A ∧ Formula.bot)) hf
  exact mp (mp (iff_intro (A ∧ Formula.bot) Formula.bot) hfwd) hbwd

end Propositional.Intuitionistic
