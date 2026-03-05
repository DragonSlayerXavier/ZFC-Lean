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
  apply deduction
  intro h
  have hnna: is_provable (¬¬A) := by
    apply mp (neg_intro (¬A))
    apply deduction
    intro hna
    exact mp h hna
  exact mp (double_neg_elim A) hnna

theorem ex_falso_classical (A : Formula) : is_provable (Formula.bot → A) := by
  apply deduction
  intro h
  have hnna: is_provable (¬¬A) := by
    apply mp (neg_intro (¬A))
    apply deduction
    intro hna
    exact h
  exact mp (double_neg_elim A) hnna

theorem excluded_middle (A : Formula) : is_provable (A ∨ ¬A) := by
  apply mp (proof_by_contradiction (A ∨ ¬A))
  apply deduction
  intro h
  have hna: is_provable (¬A) := by
    apply mp (neg_intro A)
    apply deduction
    intro ha
    have h_or: is_provable (A ∨ ¬A) := by
      exact mp (disj_intro_left A (¬A)) ha
    exact mp (mp (neg_elim (A ∨ ¬A)) h) h_or
  have h_or: is_provable (A ∨ ¬A) := by
    exact mp (disj_intro_right A (¬A)) hna
  exact mp (mp (neg_elim (A ∨ ¬A)) h) h_or

theorem double_neg_equiv (A : Formula) : is_provable (A ↔ ¬¬A) := by
  have hfwd : is_provable (A → ¬¬A) := by
    apply deduction
    intro ha
    apply mp (neg_intro (¬A))
    apply deduction
    intro hna
    exact mp (mp (neg_elim A) hna) ha
  have hbwd : is_provable (¬¬A → A) := by
    exact double_neg_elim A
  exact mp (mp (iff_intro A (¬¬A)) hfwd) hbwd

theorem disj_iff_not_conj_not (A B : Formula) : is_provable ((A ∨ B) ↔ ¬(¬A ∧ ¬B)) := by
  have hfwd : is_provable ((A ∨ B) → ¬(¬A ∧ ¬B)) := by
    apply deduction
    intro hor
    apply mp (neg_intro (¬A ∧ ¬B))
    apply deduction
    intro hnanb
    have hna : is_provable (¬A) := mp (conj_elim_left (¬A) (¬B)) hnanb
    have hnb : is_provable (¬B) := mp (conj_elim_right (¬A) (¬B)) hnanb
    have ha_bot : is_provable (A → Formula.bot) := by
      apply deduction
      intro ha
      exact mp (mp (neg_elim A) hna) ha
    have hb_bot : is_provable (B → Formula.bot) := by
      apply deduction
      intro hb
      exact mp (mp (neg_elim B) hnb) hb
    exact mp (mp (mp (disj_elim A B Formula.bot) ha_bot) hb_bot) hor
  have hbwd : is_provable (¬(¬A ∧ ¬B) → (A ∨ B)) := by
    apply deduction
    intro h
    apply mp (proof_by_contradiction (A ∨ B))
    apply deduction
    intro n_aorb
    have hna : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      exact mp (mp (neg_elim (A ∨ B)) n_aorb) (mp (disj_intro_left A B) ha)
    have hnb : is_provable (¬B) := by
      apply mp (neg_intro B)
      apply deduction
      intro hb
      exact mp (mp (neg_elim (A ∨ B)) n_aorb) (mp (disj_intro_right A B) hb)
    have hnanb : is_provable (¬A ∧ ¬B) := mp (mp (conj_intro (¬A) (¬B)) hna) hnb
    exact mp (mp (neg_elim (¬A ∧ ¬B)) h) hnanb
  exact mp (mp (iff_intro (A ∨ B) (¬(¬A ∧ ¬B))) hfwd) hbwd

theorem conj_iff_not_disj_not (A B : Formula) : is_provable ((A ∧ B) ↔ ¬(¬A ∨ ¬B)) := by
  have hfwd : is_provable ((A ∧ B) → ¬(¬A ∨ ¬B)) := by
    apply deduction
    intro hab
    apply mp (neg_intro (¬A ∨ ¬B))
    apply deduction
    intro hnanb
    have ha : is_provable A := mp (conj_elim_left A B) hab
    have hb : is_provable B := mp (conj_elim_right A B) hab
    have hna_bot : is_provable (¬A → Formula.bot) := by
      apply deduction
      intro hna
      exact mp (mp (neg_elim A) hna) ha
    have hnb_bot : is_provable (¬B → Formula.bot) := by
      apply deduction
      intro hnb
      exact mp (mp (neg_elim B) hnb) hb
    exact mp (mp (mp (disj_elim (¬A) (¬B) Formula.bot) hna_bot) hnb_bot) hnanb
  have hbwd : is_provable (¬(¬A ∨ ¬B) → (A ∧ B)) := by
    apply deduction
    intro h
    have ha : is_provable A := by
      apply mp (proof_by_contradiction A)
      apply deduction
      intro hna
      exact mp (mp (neg_elim (¬A ∨ ¬B)) h) (mp (disj_intro_left (¬A) (¬B)) hna)
    have hb : is_provable B := by
      apply mp (proof_by_contradiction B)
      apply deduction
      intro hnb
      exact mp (mp (neg_elim (¬A ∨ ¬B)) h) (mp (disj_intro_right (¬A) (¬B)) hnb)
    exact mp (mp (conj_intro A B) ha) hb
  exact mp (mp (iff_intro (A ∧ B) (¬(¬A ∨ ¬B))) hfwd) hbwd

theorem imp_iff_not_disj (A B : Formula) : is_provable ((A → B) ↔ (¬A ∨ B)) := by
  have hfwd : is_provable ((A → B) → (¬A ∨ B)) := by
    apply deduction
    intro hab
    apply mp (proof_by_contradiction (¬A ∨ B))
    apply deduction
    intro h_not_disj
    have hna : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      have hb : is_provable B := mp hab ha
      exact mp (mp (neg_elim (¬A ∨ B)) h_not_disj) (mp (disj_intro_right (¬A) B) hb)
    exact mp (mp (neg_elim (¬A ∨ B)) h_not_disj) (mp (disj_intro_left (¬A) B) hna)
  have hbwd : is_provable ((¬A ∨ B) → (A → B)) := by
    apply deduction
    intro hor
    apply mp (mp (mp (disj_elim (¬A) B (A → B)) ?case_na) ?case_b) hor
    case case_na =>
      apply deduction
      intro hna
      apply deduction
      intro ha
      exact mp (ex_falso_classical B) (mp (mp (neg_elim A) hna) ha)
    case case_b =>
      apply deduction
      intro hb
      apply deduction
      intro _
      exact hb
  exact mp (mp (iff_intro (A → B) (¬A ∨ B)) hfwd) hbwd

theorem de_morgan_conj (A B : Formula) : is_provable (¬(A ∧ B) ↔ (¬A ∨ ¬B)) := by
  have hfwd : is_provable (¬(A ∧ B) → (¬A ∨ ¬B)) := by
    apply deduction
    intro hnab
    apply mp (proof_by_contradiction (¬A ∨ ¬B))
    apply deduction
    intro nnanb
    have ha : is_provable A := by
      apply mp (proof_by_contradiction A)
      apply deduction
      intro hna
      exact mp (mp (neg_elim (¬A ∨ ¬B)) nnanb) (mp (disj_intro_left (¬A) (¬B)) hna)
    have hb : is_provable B := by
      apply mp (proof_by_contradiction B)
      apply deduction
      intro hnb
      exact mp (mp (neg_elim (¬A ∨ ¬B)) nnanb) (mp (disj_intro_right (¬A) (¬B)) hnb)
    have hab : is_provable (A ∧ B) := mp (mp (conj_intro A B) ha) hb
    exact mp (mp (neg_elim (A ∧ B)) hnab) hab
  have hbwd : is_provable ((¬A ∨ ¬B) → ¬(A ∧ B)) := by
    exact disj_neg A B
  exact mp (mp (iff_intro (¬(A ∧ B)) (¬A ∨ ¬B)) hfwd) hbwd

theorem neg_imp_iff_conj_neg (A B : Formula) : is_provable (¬(A → B) ↔ (A ∧ ¬B)) := by
  have hfwd : is_provable (¬(A → B) → (A ∧ ¬B)) := by
    apply deduction
    intro hnab
    have ha : is_provable A := by
      apply mp (proof_by_contradiction A)
      apply deduction
      intro hna
      have hab : is_provable (A → B) := by
        apply deduction
        intro ha'
        exact mp (ex_falso_classical B) (mp (mp (neg_elim A) hna) ha')
      exact mp (mp (neg_elim (A → B)) hnab) hab
    have hnb : is_provable (¬B) := by
      apply mp (neg_intro B)
      apply deduction
      intro hb
      have hab : is_provable (A → B) := by
        apply deduction
        intro _
        exact hb
      exact mp (mp (neg_elim (A → B)) hnab) hab
    exact mp (mp (conj_intro A (¬B)) ha) hnb
  have hbwd : is_provable ((A ∧ ¬B) → ¬(A → B)) := by
    apply deduction
    intro hanb
    have ha : is_provable A := mp (conj_elim_left A (¬B)) hanb
    have hnb : is_provable (¬B) := mp (conj_elim_right A (¬B)) hanb
    apply mp (neg_intro (A → B))
    apply deduction
    intro hab
    have hb : is_provable B := mp hab ha
    exact mp (mp (neg_elim B) hnb) hb
  exact mp (mp (iff_intro (¬(A → B)) (A ∧ ¬B)) hfwd) hbwd

theorem contrapositive_equiv (A B : Formula) : is_provable ((A → B) ↔ (¬B → ¬A)) := by
  have hfwd : is_provable ((A → B) → (¬B → ¬A)) := by
    exact imp_contrapositive A B
  have hbwd : is_provable ((¬B → ¬A) → (A → B)) := by
    apply deduction
    intro hna_nb
    apply deduction
    intro ha
    apply mp (proof_by_contradiction B)
    apply deduction
    intro hnb
    have hna : is_provable (¬A) := mp hna_nb hnb
    exact mp (mp (neg_elim A) hna) ha
  exact mp (mp (iff_intro (A → B) (¬B → ¬A)) hfwd) hbwd

theorem dist_imp_conj (A B C : Formula) : is_provable ((A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))) := by
  have hfwd : is_provable ((A → (B ∧ C)) → ((A → B) ∧ (A → C))) := by
    apply deduction
    intro h
    have hab : is_provable (A → B) := by
      apply deduction
      intro ha
      exact mp (conj_elim_left B C) (mp h ha)
    have hac : is_provable (A → C) := by
      apply deduction
      intro ha
      exact mp (conj_elim_right B C) (mp h ha)
    exact mp (mp (conj_intro (A → B) (A → C)) hab) hac
  have hbwd : is_provable (((A → B) ∧ (A → C)) → (A → (B ∧ C))) := by
    apply deduction
    intro h
    apply deduction
    intro ha
    have hb : is_provable B := mp (mp (conj_elim_left (A → B) (A → C)) h) ha
    have hc : is_provable C := mp (mp (conj_elim_right (A → B) (A → C)) h) ha
    exact mp (mp (conj_intro B C) hb) hc
  exact mp (mp (iff_intro (A → (B ∧ C)) ((A → B) ∧ (A → C))) hfwd) hbwd

theorem peirce_law (A B : Formula) : is_provable (((A → B) → A) → A) := by
  apply deduction
  intro h_peirce
  apply mp (proof_by_contradiction A)
  apply deduction
  intro hna
  have hab : is_provable (A → B) := by
    apply deduction
    intro ha
    exact mp (ex_falso_classical B) (mp (mp (neg_elim A) hna) ha)
  have ha : is_provable A := mp h_peirce hab
  exact mp (mp (neg_elim A) hna) ha

end Propositional.Classical
