import Lean

namespace Propositional.Minimal

inductive Formula where

  | var   : String → Formula
  | bot   : Formula
  | top   : Formula

  | imp   : Formula → Formula → Formula
  | conj  : Formula → Formula → Formula
  | disj  : Formula → Formula → Formula

  | neg   : Formula → Formula
  | iff   : Formula → Formula → Formula

-- The Provability Predicate
axiom is_provable : Formula → Prop

--Notation for readability
prefix:75 "¬" => Formula.neg
infixr:35 " ∧ " => Formula.conj
infixr:30 " ∨ " => Formula.disj
infixr:25 " → " => Formula.imp
infix:20 " ↔ " => Formula.iff


-- Hilbert's Axioms
axiom aff_cons (A B : Formula) : is_provable (A → (B → A))
axiom dist_imp (A B C : Formula) : is_provable ((A → (B → C)) → ((A → B) → (A → C)))
axiom conj_intro (A B : Formula) : is_provable (A → (B → (A ∧ B)))
axiom conj_elim_left (A B : Formula) : is_provable ((A ∧ B) → A)
axiom conj_elim_right (A B : Formula) : is_provable ((A ∧ B) → B)
axiom disj_intro_left (A B : Formula) : is_provable (A → (A ∨ B))
axiom disj_intro_right (A B : Formula) : is_provable (B → (A ∨ B))
axiom disj_elim (A B C : Formula) : is_provable ((A → C) → ((B → C) → ((A ∨ B) → C)))

axiom trivial : is_provable Formula.top
axiom neg_intro (A : Formula) : is_provable ((A → Formula.bot) → ¬A)
axiom neg_elim (A : Formula) : is_provable (¬A → (A → Formula.bot))
axiom iff_intro (A B : Formula) : is_provable ((A → B) → ((B → A) → (A ↔ B)))
axiom iff_elim_left (A B : Formula) : is_provable ((A ↔ B) → (A → B))
axiom iff_elim_right (A B : Formula) : is_provable ((A ↔ B) → (B → A))

-- Rules of Inference
axiom mp {A B : Formula} (h: is_provable (.imp A B)) (h': is_provable A) : is_provable B
axiom deduction {A B : Formula} : (is_provable A -> is_provable B) → is_provable (A → B)

-- Theorems
theorem self_imp (A : Formula) : is_provable (A → A) := by
  have h1 : is_provable (A → (A → A)) := aff_cons A A
  have h2 : is_provable (A → ((A → A) → A)) := aff_cons A (A → A)
  --have h3 : is_provable (A → ((A → A) → A)) → ((A → (A → A)) → (A → A)) := dist_imp A (A → A) A
  have h3 : is_provable (A → ((A → A) → A)) -> is_provable ((A → (A → A)) → (A → A)) := by
    intro h_pre
    exact mp (dist_imp A (A → A) A) h_pre
  have h4 : is_provable ((A → (A → A)) → (A → A)) := h3 h2
  exact mp h4 h1

theorem imp_trans (A B C : Formula) : is_provable ((A → B) → ((B → C) → (A → C))) := by
  apply deduction
  intro hab
  apply deduction
  intro hbc
  apply deduction
  intro ha
  have hb : is_provable B := mp hab ha
  have hc : is_provable C := mp hbc hb
  exact hc

theorem conj_symm (A B : Formula) : is_provable ((A ∧ B) → (B ∧ A)) := by
  apply deduction
  intro hab
  have ha : is_provable A := mp (conj_elim_left A B) hab
  have hb : is_provable B := mp (conj_elim_right A B) hab
  have hintro: is_provable (B → (A → (B ∧ A))) := conj_intro B A
  have hmid: is_provable (A → (B ∧ A)) := mp hintro hb
  exact mp hmid ha

theorem disj_symm (A B : Formula) : is_provable ((A ∨ B) → (B ∨ A)) := by
  apply deduction
  intro hab
  have h1 : is_provable (A → (B ∨ A)) := disj_intro_right B A
  have h2 : is_provable (B → (B ∨ A)) := disj_intro_left B A
  have helim: is_provable ((A → (B ∨ A)) → ((B → (B ∨ A)) → ((A ∨ B) → (B ∨ A)))) := disj_elim A B (B ∨ A)
  have hmid: is_provable ((B → (B ∨ A)) → ((A ∨ B) → (B ∨ A))) := mp helim h1
  have hfinal: is_provable ((A ∨ B) → (B ∨ A)) := mp hmid h2
  exact mp hfinal hab

theorem conj_assoc (A B C : Formula) : is_provable (((A ∧ (B ∧ C)) → ((A ∧ B) ∧ C))) := by
  apply deduction
  intro habc
  have ha : is_provable A := mp (conj_elim_left A (B ∧ C)) habc
  have hbc : is_provable (B ∧ C) := mp (conj_elim_right A (B ∧ C)) habc
  have hb : is_provable B := mp (conj_elim_left B C) hbc
  have hc : is_provable C := mp (conj_elim_right B C) hbc
  have h_ab_intro : is_provable (A → (B → (A ∧ B))) := conj_intro A B
  have h_b_to_ab : is_provable (B → (A ∧ B)) := mp h_ab_intro ha
  have hab : is_provable (A ∧ B) := mp h_b_to_ab hb
  have h_final_intro : is_provable ((A ∧ B) → (C → ((A ∧ B) ∧ C))) := conj_intro (A ∧ B) C
  have h_final_mid : is_provable (C → ((A ∧ B) ∧ C)) := mp h_final_intro hab
  exact mp h_final_mid hc

theorem disj_assoc (A B C : Formula) : is_provable (((A ∨ (B ∨ C)) → ((A ∨ B) ∨ C))) := by
  apply deduction
  intro habc
  have ha_res: is_provable (A → ((A ∨ B) ∨ C)) := by
    apply deduction
    intro ha
    have hab: is_provable (A ∨ B) := mp (disj_intro_left A B) ha
    exact mp (disj_intro_left (A ∨ B) C) hab
  have hbc_res: is_provable ((B ∨ C) → ((A ∨ B) ∨ C)) := by
    apply deduction
    intro hbc
    have hb_res: is_provable (B → ((A ∨ B) ∨ C)) := by
      apply deduction
      intro hb
      have hab: is_provable (A ∨ B) := mp (disj_intro_right A B) hb
      exact mp (disj_intro_left (A ∨ B) C) hab
    have hc_res: is_provable (C → ((A ∨ B) ∨ C)) := by
      apply deduction
      intro hc
      exact mp (disj_intro_right (A ∨ B) C) hc
    have h_elim_inner := disj_elim B C ((A ∨ B) ∨ C)
    exact mp (mp (mp h_elim_inner hb_res) hc_res) hbc
  have h_elim := disj_elim A (B ∨ C) ((A ∨ B) ∨ C)
  exact mp (mp (mp h_elim ha_res) hbc_res) habc

theorem dist_conj_disj (A B C : Formula) : is_provable ((A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C))) := by
  apply deduction
  intro habc
  have ha : is_provable A := mp (conj_elim_left A (B ∨ C)) habc
  have hbc : is_provable (B ∨ C) := mp (conj_elim_right A (B ∨ C)) habc
  have hb_res: is_provable (B → ((A ∧ B) ∨ (A ∧ C))) := by
    apply deduction
    intro hb
    have hab: is_provable (A ∧ B) := mp (mp (conj_intro A B) ha) hb
    exact mp (disj_intro_left (A ∧ B) (A ∧ C)) hab
  have hc_res: is_provable (C → ((A ∧ B) ∨ (A ∧ C))) := by
    apply deduction
    intro hc
    have hac: is_provable (A ∧ C) := mp (mp (conj_intro A C) ha) hc
    exact mp (disj_intro_right (A ∧ B) (A ∧ C)) hac
  have h_elim: is_provable ((B → ((A ∧ B) ∨ (A ∧ C))) → ((C → ((A ∧ B) ∨ (A ∧ C))) → ((B ∨ C) → ((A ∧ B) ∨ (A ∧ C))))) :=
    disj_elim B C ((A ∧ B) ∨ (A ∧ C))
  exact mp (mp (mp h_elim hb_res) hc_res) hbc

theorem dist_disj_conj (A B C : Formula) : is_provable ((A ∨ (B ∧ C)) → ((A ∨ B) ∧ (A ∨ C))) := by
  apply deduction
  intro habc
  have ha_res: is_provable (A → ((A ∨ B) ∧ (A ∨ C))) := by
    apply deduction
    intro ha
    have hab: is_provable (A ∨ B) := mp (disj_intro_left A B) ha
    have hac: is_provable (A ∨ C) := mp (disj_intro_left A C) ha
    have h_final_intro: is_provable ((A ∨ B) → ((A ∨ C) → ((A ∨ B) ∧ (A ∨ C)))) := conj_intro (A ∨ B) (A ∨ C)
    have h_final_mid: is_provable ((A ∨ C) → ((A ∨ B) ∧ (A ∨ C))) := mp h_final_intro hab
    exact mp h_final_mid hac
  have hbc_res: is_provable ((B ∧ C) → ((A ∨ B) ∧ (A ∨ C))) := by
    apply deduction
    intro hbc
    have hb: is_provable B := mp (conj_elim_left B C) hbc
    have hc: is_provable C := mp (conj_elim_right B C) hbc
    have hab: is_provable (A ∨ B) := mp (disj_intro_right A B) hb
    have hac: is_provable (A ∨ C) := mp (disj_intro_right A C) hc
    have h_final_intro: is_provable ((A ∨ B) → ((A ∨ C) → ((A ∨ B) ∧ (A ∨ C)))) := conj_intro (A ∨ B) (A ∨ C)
    have h_final_mid: is_provable ((A ∨ C) → ((A ∨ B) ∧ (A ∨ C))) := mp h_final_intro hab
    exact mp h_final_mid hac
  have h_elim: is_provable ((A → ((A ∨ B) ∧ (A ∨ C))) → (((B ∧ C) → ((A ∨ B) ∧ (A ∨ C))) → ((A ∨ (B ∧ C)) → ((A ∨ B) ∧ (A ∨ C))))) :=
    disj_elim A (B ∧ C) ((A ∨ B) ∧ (A ∨ C))
  exact mp (mp (mp h_elim ha_res) hbc_res) habc

theorem iff_conj (A B C : Formula) : is_provable ((A → (B → C)) ↔ ((A ∧ B) → C)) := by
  have hfwd : is_provable ((A → (B → C)) → ((A ∧ B) → C)) := by
    apply deduction
    intro habc
    apply deduction
    intro hab
    have ha : is_provable A := mp (conj_elim_left A B) hab
    have hb : is_provable B := mp (conj_elim_right A B) hab
    have hbc : is_provable (B → C) := mp habc ha
    exact mp hbc hb
  have hbwd : is_provable (((A ∧ B) → C) → (A → (B → C))) := by
    apply deduction
    intro habc
    apply deduction
    intro ha
    apply deduction
    intro hb
    have hab : is_provable (A ∧ B) := mp (mp (conj_intro A B) ha) hb
    exact mp habc hab
  exact mp (mp (iff_intro (A → (B → C)) ((A ∧ B) → C)) hfwd) hbwd

theorem iff_disj (A B C : Formula) : is_provable (((A ∨ B) → C) ↔ ((A → C) ∧ (B → C))) := by
  have hfwd : is_provable (((A ∨ B) → C) → ((A → C) ∧ (B → C))) := by
    apply deduction
    intro habc
    have hac: is_provable (A → C) := by
      apply deduction
      intro ha
      have hab: is_provable (A ∨ B) := mp (disj_intro_left A B) ha
      exact mp habc hab
    have hbc: is_provable (B → C) := by
      apply deduction
      intro hb
      have hab: is_provable (A ∨ B) := mp (disj_intro_right A B) hb
      exact mp habc hab
    have h_final_intro: is_provable ((A → C) → ((B → C) → ((A → C) ∧ (B → C)))) := conj_intro (A → C) (B → C)
    have h_final_mid: is_provable ((B → C) → ((A → C) ∧ (B → C))) := mp h_final_intro hac
    exact mp h_final_mid hbc
  have hbwd : is_provable (((A → C) ∧ (B → C)) → ((A ∨ B) → C)) := by
    apply deduction
    intro habc
    have hac: is_provable (A → C) := mp (conj_elim_left (A → C) (B → C)) habc
    have hbc: is_provable (B → C) := mp (conj_elim_right (A → C) (B → C)) habc
    apply deduction
    intro hab
    have h_elim: is_provable ((A → C) → ((B → C) → ((A ∨ B) → C))) := disj_elim A B C
    exact mp (mp (mp h_elim hac) hbc) hab
  exact mp (mp (iff_intro ((A ∨ B) → C) ((A → C) ∧ (B → C))) hfwd) hbwd

theorem non_contradiction (A : Formula) : is_provable (¬((A ∧ ¬A))) := by
  apply mp (neg_intro (A ∧ ¬A))
  apply deduction
  intro h
  have ha : is_provable A := mp (conj_elim_left A (¬A)) h
  have hna : is_provable (¬A) := mp (conj_elim_right A (¬A)) h
  have h_contr : is_provable (A → Formula.bot) := mp (neg_elim A) hna
  exact mp h_contr ha

theorem imp_neg_elim (A B : Formula) : is_provable (¬(A → B) → ¬B) := by
  apply deduction
  intro hn_imp
  apply mp (neg_intro B)
  apply deduction
  intro hb
  have hn_imp_bot : is_provable ((A → B) → Formula.bot) := mp (neg_elim (A → B)) hn_imp
  have himp: is_provable (A → B) := by
    apply deduction
    intro ha
    exact hb
  exact mp hn_imp_bot himp

theorem imp_contrapositive (A B : Formula) : is_provable ((A → B) → (¬B → ¬A)) := by
  apply deduction
  intro hAB
  apply deduction
  intro h_notB
  apply mp (neg_intro A)
  apply deduction
  intro hA
  have hB : is_provable B := mp hAB hA
  have h_notB_imp : is_provable (B → Formula.bot) := mp (neg_elim B) h_notB
  exact mp h_notB_imp hB

theorem double_neg_intro (A : Formula) : is_provable (A → ¬¬A) := by
  apply deduction
  intro hA
  apply mp (neg_intro (¬A))
  apply deduction
  intro h_notA
  have h_imp_bot : is_provable (A → Formula.bot) := mp (neg_elim A) h_notA
  exact mp h_imp_bot hA

theorem disj_neg (A B : Formula) : is_provable ((¬A ∨ ¬B) → ¬(A ∧ B)) := by
  apply deduction
  intro h_disj_not
  apply mp (neg_intro (A ∧ B))
  apply deduction
  intro h_conj
  have hA : is_provable A := mp (conj_elim_left A B) h_conj
  have hB : is_provable B := mp (conj_elim_right A B) h_conj
  have h_caseA : is_provable (¬A → Formula.bot) := by
    apply deduction
    intro h_notA
    exact mp (mp (neg_elim A) h_notA) hA
  have h_caseB : is_provable (¬B → Formula.bot) := by
    apply deduction
    intro h_notB
    exact mp (mp (neg_elim B) h_notB) hB
  exact mp (mp (mp (disj_elim (¬A) (¬B) Formula.bot) h_caseA) h_caseB) h_disj_not

theorem de_morgan_disj (A B : Formula) : is_provable (¬(A ∨ B) ↔ (¬A ∧ ¬B)) := by
  have hfwd : is_provable (¬(A ∨ B) → (¬A ∧ ¬B)) := by
    apply deduction
    intro h_not_disj
    have h_notA : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      have h_disj : is_provable (A ∨ B) := mp (disj_intro_left A B) ha
      have h_imp_bot : is_provable ((A ∨ B) → Formula.bot) := mp (neg_elim (A ∨ B)) h_not_disj
      exact mp h_imp_bot h_disj
    have h_notB : is_provable (¬B) := by
      apply mp (neg_intro B)
      apply deduction
      intro hb
      have h_disj : is_provable (A ∨ B) := mp (disj_intro_right A B) hb
      have h_imp_bot : is_provable ((A ∨ B) → Formula.bot) := mp (neg_elim (A ∨ B)) h_not_disj
      exact mp h_imp_bot h_disj
    exact mp (mp (conj_intro (¬A) (¬B)) h_notA) h_notB
  have hbwd : is_provable ((¬A ∧ ¬B) → ¬(A ∨ B)) := by
    apply deduction
    intro h_conj_not
    apply mp (neg_intro (A ∨ B))
    apply deduction
    intro h_disj
    have h_notA : is_provable (¬A) := mp (conj_elim_left (¬A) (¬B)) h_conj_not
    have h_notB : is_provable (¬B) := mp (conj_elim_right (¬A) (¬B)) h_conj_not
    have hA_bot : is_provable (A → Formula.bot) := mp (neg_elim A) h_notA
    have hB_bot : is_provable (B → Formula.bot) := mp (neg_elim B) h_notB
    have h_elim : is_provable ((A → Formula.bot) → ((B → Formula.bot) → ((A ∨ B) → Formula.bot))) := disj_elim A B Formula.bot
    exact mp (mp (mp h_elim hA_bot) hB_bot) h_disj
  exact mp (mp (iff_intro (¬(A ∨ B)) (¬A ∧ ¬B)) hfwd) hbwd

theorem triple_neg_equiv (A : Formula) : is_provable (¬A ↔ ¬¬¬A) := by
  have hfwd : is_provable (¬A → ¬¬¬A) := double_neg_intro (¬A)
  have hbwd : is_provable (¬¬¬A → ¬A) := by
    apply deduction
    intro hnnnA
    apply mp (neg_intro A)
    apply deduction
    intro ha
    have hnnA : is_provable (¬¬A) := mp (double_neg_intro A) ha
    have hnnnA_imp : is_provable (¬¬A → Formula.bot) := mp (neg_elim (¬¬A)) hnnnA
    exact mp hnnnA_imp hnnA
  exact mp (mp (iff_intro (¬A) (¬¬¬A)) hfwd) hbwd

theorem imp_neg_equiv_double_neg (A B : Formula) : is_provable ((A → ¬B) ↔ (¬¬A → ¬B)) := by
  have hfwd : is_provable ((A → ¬B) → (¬¬A → ¬B)) := by
    apply deduction
    intro hAnB
    apply deduction
    intro hnnA
    apply mp (neg_intro B)
    apply deduction
    intro hb
    have h_notA : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      have hnb : is_provable (¬B) := mp hAnB ha
      exact mp (mp (neg_elim B) hnb) hb
    exact mp (mp (neg_elim (¬A)) hnnA) h_notA
  have hbwd : is_provable ((¬¬A → ¬B) → (A → ¬B)) := by
    apply deduction
    intro hnnAnB
    apply deduction
    intro ha
    have hnnA : is_provable (¬¬A) := mp (double_neg_intro A) ha
    exact mp hnnAnB hnnA
  exact mp (mp (iff_intro (A → ¬B) (¬¬A → ¬B)) hfwd) hbwd

theorem double_neg_disj_iff_not_conj_not (A B : Formula) : is_provable (¬¬(A ∨ B) ↔ ¬(¬A ∧ ¬B)) := by
  have h_dm := de_morgan_disj A B
  have hfwd : is_provable (¬¬(A ∨ B) → ¬(¬A ∧ ¬B)) := by
    apply deduction
    intro hnn_disj
    apply mp (neg_intro (¬A ∧ ¬B))
    apply deduction
    intro h_conj_not
    have h_not_disj : is_provable (¬(A ∨ B)) := mp (mp (iff_elim_right (¬(A ∨ B)) (¬A ∧ ¬B)) h_dm) h_conj_not
    have h_disj_imp_bot : is_provable (¬(A ∨ B) → Formula.bot) := mp (neg_elim (¬(A ∨ B))) hnn_disj
    exact mp h_disj_imp_bot h_not_disj
  have hbwd : is_provable (¬(¬A ∧ ¬B) → ¬¬(A ∨ B)) := by
    apply deduction
    intro hn_conj_not
    apply mp (neg_intro (¬(A ∨ B)))
    apply deduction
    intro h_not_disj
    have h_conj_not : is_provable (¬A ∧ ¬B) := mp (mp (iff_elim_left (¬(A ∨ B)) (¬A ∧ ¬B)) h_dm) h_not_disj
    have h_not_not_disj_imp_bot : is_provable ((¬A ∧ ¬B) → Formula.bot) := mp (neg_elim (¬A ∧ ¬B)) hn_conj_not
    exact mp h_not_not_disj_imp_bot h_conj_not
  exact mp (mp (iff_intro (¬¬(A ∨ B)) (¬(¬A ∧ ¬B))) hfwd) hbwd

theorem double_neg_imp_dist (A B : Formula) : is_provable (¬¬(A → B) → (¬¬A → ¬¬B)) := by
  apply deduction
  intro hnn_imp
  apply deduction
  intro hnnA
  apply mp (neg_intro (¬B))
  apply deduction
  intro hnb
  have h_not_imp : is_provable (¬(A → B)) := by
    apply mp (neg_intro (A → B))
    apply deduction
    intro hab
    have h_notA : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      have hb : is_provable B := mp hab ha
      have hnb_imp : is_provable (B → Formula.bot) := mp (neg_elim B) hnb
      exact mp hnb_imp hb
    have hnnA_imp : is_provable (¬A → Formula.bot) := mp (neg_elim (¬A)) hnnA
    exact mp hnnA_imp h_notA
  have hnn_imp_imp_bot : is_provable (¬(A → B) → Formula.bot) := mp (neg_elim (¬(A → B))) hnn_imp
  exact mp hnn_imp_imp_bot h_not_imp

theorem double_neg_conj_dist (A B : Formula) : is_provable (¬¬(A ∧ B) ↔ (¬¬A ∧ ¬¬B)) := by
  have hfwd : is_provable (¬¬(A ∧ B) → (¬¬A ∧ ¬¬B)) := by
    apply deduction
    intro hnn_conj
    have hnnA : is_provable (¬¬A) := by
      apply mp (neg_intro (¬A))
      apply deduction
      intro hna
      have hna_imp : is_provable (A → Formula.bot) := mp (neg_elim A) hna
      have hnn_conj_imp : is_provable (¬(A ∧ B) → Formula.bot) := mp (neg_elim (¬(A ∧ B))) hnn_conj
      have h_not_conj : is_provable (¬(A ∧ B)) := by
        apply mp (neg_intro (A ∧ B))
        apply deduction
        intro hab
        exact mp hna_imp (mp (conj_elim_left A B) hab)
      exact mp hnn_conj_imp h_not_conj
    have hnnB : is_provable (¬¬B) := by
      apply mp (neg_intro (¬B))
      apply deduction
      intro hnb
      have hnb_imp : is_provable (B → Formula.bot) := mp (neg_elim B) hnb
      have hnn_conj_imp : is_provable (¬(A ∧ B) → Formula.bot) := mp (neg_elim (¬(A ∧ B))) hnn_conj
      have h_not_conj : is_provable (¬(A ∧ B)) := by
        apply mp (neg_intro (A ∧ B))
        apply deduction
        intro hab
        exact mp hnb_imp (mp (conj_elim_right A B) hab)
      exact mp hnn_conj_imp h_not_conj
    exact mp (mp (conj_intro (¬¬A) (¬¬B)) hnnA) hnnB
  have hbwd : is_provable ((¬¬A ∧ ¬¬B) → ¬¬(A ∧ B)) := by
    apply deduction
    intro h_conj_nn
    have hnnA := mp (conj_elim_left (¬¬A) (¬¬B)) h_conj_nn
    have hnnB := mp (conj_elim_right (¬¬A) (¬¬B)) h_conj_nn
    apply mp (neg_intro (¬(A ∧ B)))
    apply deduction
    intro h_not_conj
    have h_notA : is_provable (¬A) := by
      apply mp (neg_intro A)
      apply deduction
      intro ha
      have h_notB : is_provable (¬B) := by
        apply mp (neg_intro B)
        apply deduction
        intro hb
        have h_imp_bot : is_provable ((A ∧ B) → Formula.bot) := mp (neg_elim (A ∧ B)) h_not_conj
        exact mp h_imp_bot (mp (mp (conj_intro A B) ha) hb)
      have hnnB_imp : is_provable (¬B → Formula.bot) := mp (neg_elim (¬B)) hnnB
      exact mp hnnB_imp h_notB
    have hnnA_imp : is_provable (¬A → Formula.bot) := mp (neg_elim (¬A)) hnnA
    exact mp hnnA_imp h_notA
  exact mp (mp (iff_intro (¬¬(A ∧ B)) (¬¬A ∧ ¬¬B)) hfwd) hbwd


end Propositional.Minimal
