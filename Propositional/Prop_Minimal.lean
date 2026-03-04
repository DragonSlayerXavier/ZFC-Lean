import Lean

namespace Propositional

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
notation:max A " → " B => Formula.imp A B
notation:max A " ∧ " B => Formula.conj A B
notation:max A " ∨ " B => Formula.disj A B
notation:max "¬" A     => Formula.neg A
notation:max A " ↔ " B => Formula.iff A B

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
  have h3 : is_provable (A → ((A → A) → A)) → ((A → (A → A)) → (A → A)) := dist_imp A (A → A) A
  have h4 : is_provable ((A → (A → A)) → (A → A)) := mp h3 h2
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
      have hres: is_provable (C → ((A ∨ B) ∨ C)) := disj_intro_right (A ∨ B) C
      exact mp hres hc
    have h_elim_inner: is_provable (B → (A ∨ B) ∨ C) → (C → (A ∨ B) ∨ C) → (B ∨ C) → (A ∨ B) ∨ C :=
      disj_elim B C ((A ∨ B) ∨ C)
    exact mp (mp (mp h_elim_inner hb_res) hc_res) hbc
  have h_elim : is_provable ((A → ((A ∨ B) ∨ C)) → (((B ∨ C) → ((A ∨ B) ∨ C)) → ((A ∨ (B ∨ C)) → ((A ∨ B) ∨ C)))) :=
    disj_elim A (B ∨ C) ((A ∨ B) ∨ C)
  exact mp (mp (mp h_elim ha_res) hbc_res) habc

theorem dist_conj_disj (A B C : Formula) : is_provable ((A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C))) := by
  sorry

theorem dist_disj_conj (A B C : Formula) : is_provable ((A ∨ (B ∧ C)) → ((A ∨ B) ∧ (A ∨ C))) := by
  sorry

theorem iff_conj (A B C : Formula) : is_provable ((A → (B → C)) ↔ ((A ∧ B) → C)) := by
  sorry

theorem iff_disj (A B C : Formula) : is_provable (((A ∨ B) → C) ↔ ((A → C) ∧ (B → C))) := by
  sorry

theorem non_contradiction (A : Formula) : is_provable (¬(A ∧ ¬A)) := by
  sorry

theorem imp_neg_elim (A B : Formula) : is_provable (¬(A → B) → ¬B) := by
  sorry

theorem imp_contrapositive (A B : Formula) : is_provable ((A → B) → (¬B → ¬A)) := by
  sorry

theorem double_neg_intro (A : Formula) : is_provable (A → ¬¬A) := by
  sorry

theorem disj_neg (A B : Formula) : is_provable ((¬A ∨ ¬B) → ¬(A ∧ B)) := by
  sorry

theorem de_morgan_disj (A B : Formula) : is_provable (¬(A ∨ B) ↔ (¬A ∧ ¬B)) := by
  sorry

theorem triple_neg_equiv (A : Formula) : is_provable (¬A ↔ ¬¬¬A) := by
  sorry

theorem imp_neg_equiv_double_neg (A B : Formula) : is_provable ((A → ¬B) ↔ (¬¬A → ¬B)) := by
  sorry

theorem double_neg_disj_iff_not_conj_not (A B : Formula) : is_provable (¬¬(A ∨ B) ↔ ¬(¬A ∧ ¬B)) := by
  sorry

theorem double_neg_imp_dist (A B : Formula) : is_provable (¬¬(A → B) → (¬¬A → ¬¬B)) := by
  sorry

theorem double_neg_conj_dist (A B : Formula) : is_provable (¬¬(A ∧ B) ↔ (¬¬A ∧ ¬¬B)) := by
  sorry

end Propositional
