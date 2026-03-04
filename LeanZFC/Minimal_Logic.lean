import Lean

namespace Propositional

-- Hilbert's Axioms
axiom aff_cons (A B : Prop) : A → (B → A) -- Affirmation of the Consequent
axiom dist_imp (A B C : Prop) : (A → (B → C)) → ((A → B) → (A → C)) -- Distribution of Implication
axiom conj_intro (A B : Prop) : A → (B → A ∧ B) -- Conjunction Introduction
axiom conj_elim_left (A B : Prop) : A ∧ B → A -- Conjunction Elimination Left
axiom conj_elim_right (A B : Prop) : A ∧ B → B -- Conjunction Elimination Right
axiom disj_intro_left (A B : Prop) : A → A ∨ B -- Disjunction Introduction Left
axiom disj_intro_right (A B : Prop) : B → A ∨ B -- Disjunction Introduction Right
axiom disj_elim (A B C : Prop) : (A → C) → ((B → C) → (A ∨ B → C)) -- Disjunction Elimination

axiom trivial : True -- Axiom of Truth
axiom neg_intro (A : Prop) : (A → False) → ¬A -- Negation Introduction
axiom neg_elim (A : Prop) : ¬A → (A → False) -- Negation Elimination
axiom iff_intro (A B : Prop) : (A → B) → ((B → A) → (A ↔ B)) -- Biconditional Introduction
axiom iff_elim_left (A B : Prop) : (A ↔ B) → (A → B) -- Biconditional Elimination Left
axiom iff_elim_right (A B : Prop) : (A ↔ B) → (B → A) -- Biconditional Elimination Right

-- Rules of Inference
axiom modus_ponens {P Q : Prop} (h1 : P → Q) (h2 : P) : Q -- Modus Ponens

-- Theorems

theorem self_imp (A : Prop) : A → A := by
  have h1 : A → (A → A) := by apply aff_cons A A
  have h2 : A → ((A → A) → A) := by apply aff_cons A (A → A)
  have h3: (A → ((A → A) → A)) → ((A → (A → A)) → (A → A)) := by apply dist_imp A (A → A) A
  have h4: (A → (A → A)) → (A → A) := by apply modus_ponens h3 h2
  exact modus_ponens h4 h1

theorem imp_trans (A B C : Prop) : (A → B) → (B → C) → (A → C) := by
  intro h1 h2 h3
  have h4 : B := by apply modus_ponens h1 h3
  apply modus_ponens h2 h4

theorem conj_symm (A B : Prop) : A ∧ B → B ∧ A := by
  intro h
  have h1 : A := by apply conj_elim_left A B h
  have h2 : B := by apply conj_elim_right A B h
  apply conj_intro B A
  exact h2
  exact h1

theorem disj_symm (A B : Prop) : A ∨ B → B ∨ A := by
  intro h
  apply disj_elim A B (B ∨ A)
  apply disj_intro_right B A
  apply disj_intro_left B A
  exact h

theorem conj_assoc (A B C : Prop) : A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
  intro h
  have h1 : A := by apply conj_elim_left A (B ∧ C) h
  have h2 : B ∧ C := by apply conj_elim_right A (B ∧ C) h
  have h3 : B := by apply conj_elim_left B C h2
  have h4 : C := by apply conj_elim_right B C h2
  apply conj_intro (A ∧ B) C
  apply conj_intro A B
  exact h1
  exact h3
  exact h4

theorem disj_assoc (A B C : Prop) : A ∨ (B ∨ C) → (A ∨ B) ∨ C := by
  apply disj_elim A (B ∨ C) ((A ∨ B) ∨ C)
  have h1 : A → A ∨ B := by apply disj_intro_left A B
  have h2 : (A ∨ B) → (A ∨ B) ∨ C := by apply disj_intro_left (A ∨ B) C
  have h3 : A → (A ∨ B) ∨ C := by apply imp_trans A (A ∨ B) ((A ∨ B) ∨ C) h1 h2
  exact h3
  apply disj_elim B C ((A ∨ B) ∨ C)
  have h4 : B → A ∨ B := by apply disj_intro_right A B
  have h5 : (A ∨ B) → (A ∨ B) ∨ C := by apply disj_intro_left (A ∨ B) C
  have h6 : B → (A ∨ B) ∨ C := by apply imp_trans B (A ∨ B) ((A ∨ B) ∨ C) h4 h5
  exact h6
  apply disj_intro_right (A ∨ B) C

theorem dist_conj_disj (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro h
  have h1 : A := by apply conj_elim_left A (B ∨ C) h
  have h2 : B ∨ C := by apply conj_elim_right A (B ∨ C) h
  apply disj_elim B C ((A ∧ B) ∨ (A ∧ C))
  have h3 : B → (A ∧ B) := by
    intro hb
    apply conj_intro A B
    exact h1
    exact hb
  have h4 : (A ∧ B) → (A ∧ B) ∨ (A ∧ C) := by apply disj_intro_left (A ∧ B) (A ∧ C)
  have h5 : B → (A ∧ B) ∨ (A ∧ C) := by apply imp_trans B (A ∧ B) ((A ∧ B) ∨ (A ∧ C)) h3 h4
  exact h5
  have h6 : C → (A ∧ C) := by
    intro hc
    apply conj_intro A C
    exact h1
    exact hc
  have h7 : (A ∧ C) → (A ∧ B) ∨ (A ∧ C) := by apply disj_intro_right (A ∧ B) (A ∧ C)
  have h8 : C → (A ∧ B) ∨ (A ∧ C) := by apply imp_trans C (A ∧ C) ((A ∧ B) ∨ (A ∧ C)) h6 h7
  exact h8
  exact h2

theorem dist_disj_conj (A B C : Prop) : A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C) := by
  intro h
  apply disj_elim A (B ∧ C) ((A ∨ B) ∧ (A ∨ C))
  have h1 : A → (A ∨ B) := by apply disj_intro_left A B
  have h2 : A → (A ∨ C) := by apply disj_intro_left A C
  have h3 : A → (A ∨ B) ∧ (A ∨ C) := by
    intro ha
    apply conj_intro (A ∨ B) (A ∨ C)
    exact h1 ha
    exact h2 ha
  exact h3
  intro hbc
  have h4 : A ∨ B := by
    have hb : B := by apply conj_elim_left B C hbc
    apply disj_intro_right A B
    exact hb
  have h5 : A ∨ C := by
    have hc : C := by apply conj_elim_right B C hbc
    apply disj_intro_right A C
    exact hc
  apply conj_intro (A ∨ B) (A ∨ C)
  exact h4
  exact h5
  exact h

theorem iff_conj (A B C : Prop) : (A → (B → C)) ↔ (A ∧ B → C) := by
  apply iff_intro (A → (B → C)) (A ∧ B → C)
  have h1 : (A → (B → C)) → ((A ∧ B) → C) := by
    intro h
    intro hab
    have ha : A := by apply conj_elim_left A B hab
    have hb : B := by apply conj_elim_right A B hab
    have hbc : B → C := by apply modus_ponens h ha
    exact modus_ponens hbc hb
  exact h1
  have h2 : (A ∧ B → C) → (A → (B → C)) := by
    intro h
    intro ha
    intro hb
    have hab : A ∧ B := by apply conj_intro A B ha hb
    exact modus_ponens h hab
  exact h2

theorem iff_disj (A B C : Prop) : (A ∨ B → C) ↔ ((A → C) ∧ (B → C)) := by
  apply iff_intro (A ∨ B → C) ((A → C) ∧ (B → C))
  have h1 : (A ∨ B → C) → ((A → C) ∧ (B → C)) := by
    intro h
    have hac : A → C := by
      intro ha
      apply h
      apply disj_intro_left A B
      exact ha
    have hbc : B → C := by
      intro hb
      apply h
      apply disj_intro_right A B
      exact hb
    apply conj_intro (A → C) (B → C)
    exact hac
    exact hbc
  exact h1
  have h2 : ((A → C) ∧ (B → C)) → (A ∨ B → C) := by
    intro h
    have hac : A → C := by apply conj_elim_left (A → C) (B → C) h
    have hbc : B → C := by apply conj_elim_right (A → C) (B → C) h
    intro hab
    apply disj_elim A B C hac hbc hab
  exact h2

theorem non_contradiction (A : Prop) : ¬(A ∧ ¬A) := by
  intro h
  have ha : A := by apply conj_elim_left A (¬A) h
  have hna : ¬A := by apply conj_elim_right A (¬A) h
  exact neg_elim A hna ha

theorem imp_neg_elim (A B : Prop) : ¬(A → B) → ¬B := by
  intro h
  intro hb
  have hab : A → B := by
    intro ha
    exact hb
  exact h hab

theorem imp_contrapositive (A B : Prop) : (A → B) → (¬B → ¬A) := by
  intro h
  intro hnb
  intro ha
  have hb : B := by apply modus_ponens h ha
  exact hnb hb

theorem imp_neg_neg (A :Prop) : A → ¬¬A := by
  intro ha
  intro hna
  have hana : A ∧ ¬A := by
    apply conj_intro A (¬A)
    exact ha
    exact hna
  exact non_contradiction A hana

theorem disj_neg (A B : Prop) : ¬A ∨ ¬B → ¬(A ∧ B) := by
  intro h
  intro hab
  have ha : A := by apply conj_elim_left A B hab
  have hb : B := by apply conj_elim_right A B hab
  have hcont: ¬(¬A ∨ ¬B) := by
    intro hdisj
    apply disj_elim (¬A) (¬B) False
    intro hna
    exact hna ha
    intro hnb
    exact hnb hb
    exact hdisj
  exact hcont h

theorem de_morgan_disj (A B : Prop) : ¬(A ∨ B) ↔ (¬A ∧ ¬B) := by
  apply iff_intro (¬(A ∨ B)) (¬A ∧ ¬B)
  have h1 : ¬(A ∨ B) → (¬A ∧ ¬B) := by
    intro h
    have hna : ¬A := by
      intro ha
      apply h
      apply disj_intro_left A B
      exact ha
    have hnb : ¬B := by
      intro hb
      apply h
      apply disj_intro_right A B
      exact hb
    apply conj_intro (¬A) (¬B)
    exact hna
    exact hnb
  exact h1
  have h2 : (¬A ∧ ¬B) → ¬(A ∨ B) := by
    intro h
    have hna : ¬A := by apply conj_elim_left (¬A) (¬B) h
    have hnb : ¬B := by apply conj_elim_right (¬A) (¬B) h
    intro hab
    apply disj_elim A B False
    intro ha
    exact hna ha
    intro hb
    exact hnb hb
    exact hab
  exact h2

theorem not_iff_not_not_not (A : Prop) : ¬A ↔ ¬¬¬A := by
  apply iff_intro (¬A) (¬¬¬A)
  have h1 : ¬A → ¬¬¬A := by
    intro hna
    intro hnna
    have hcont : ¬A := by
      intro ha
      exact hna ha
    exact hnna hcont
  exact h1
  have h2 : ¬¬¬A → ¬A := by
    intro hnna
    intro ha
    have hcont : ¬(¬A) := by
      intro hna
      exact hna ha
    exact hnna hcont
  exact h2

theorem imp_neg_iff_neg_neg_imp_neg (A B : Prop) : (A → ¬B) ↔ (¬¬A → ¬B) := by
  apply iff_intro (A → ¬B) (¬¬A → ¬B)
  have h1 : (A → ¬B) → (¬¬A → ¬B) := by
    intro h
    intro hnna
    intro hb
    have hna: ¬A := by
      apply neg_intro A
      intro ha
      have hnb : ¬B := by apply modus_ponens h ha
      exact hnb hb
    have hnanna : ¬A ∧ ¬¬A := by
      exact conj_intro (¬A) (¬¬A) hna hnna
    apply non_contradiction ¬A
    exact hnanna
  exact h1
  have h2 : (¬¬A → ¬B) → (A → ¬B) := by
    intro h
    intro ha
    intro hb
    have hnna : ¬¬A := by
      intro hna
      exact hna ha
    have hnb : ¬B := by apply modus_ponens h hnna
    exact hnb hb
  exact h2

theorem neg_neg_disj_iff_neg_conj_neg (A B : Prop) : ¬¬(A ∨ B) ↔ ¬(¬A ∧ ¬B) := by
  apply iff_intro (¬¬(A ∨ B)) (¬(¬A ∧ ¬B))
  have h1 : ¬¬(A ∨ B) → ¬(¬A ∧ ¬B) := by
    intro hnnaob
    intro hcont
    have hna : ¬A := by apply conj_elim_left (¬A) (¬B) hcont
    have hnb : ¬B := by apply conj_elim_right (¬A) (¬B) hcont
    have hcont2 : ¬(A ∨ B) := by
      intro haob
      apply disj_elim A B False
      intro ha
      exact hna ha
      intro hb
      exact hnb hb
      exact haob
    exact hnnaob hcont2
  exact h1
  have h2 : ¬(¬A ∧ ¬B) → ¬¬(A ∨ B) := by
    intro h
    rw[←de_morgan_disj A B] at h
    exact h
  exact h2

theorem neg_neg_imp (A B : Prop) : ¬¬(A → B) → (¬¬A → ¬¬B) := by
  intro hnnAB
  intro hnnA
  intro hnB
  apply hnnAB
  intro hAB
  apply hnnA
  intro hA
  apply hnB
  apply hAB
  exact hA

theorem neg_neg_conj_iff_conj_neg_neg (A B : Prop) : ¬¬(A ∧ B) ↔ (¬¬A ∧ ¬¬B) := by
  apply iff_intro (¬¬(A ∧ B)) (¬¬A ∧ ¬¬B)
  have h1 : ¬¬(A ∧ B) → (¬¬A ∧ ¬¬B) := by
    intro hnnAB
    have hnnA : ¬¬A := by
      intro hna
      have hcont : ¬(A ∧ B) := by
        intro hab
        have ha : A := by apply conj_elim_left A B hab
        exact hna ha
      exact hnnAB hcont
    have hnnB : ¬¬B := by
      intro hnb
      have hcont : ¬(A ∧ B) := by
        intro hab
        have hb : B := by apply conj_elim_right A B hab
        exact hnb hb
      exact hnnAB hcont
    apply conj_intro (¬¬A) (¬¬B)
    exact hnnA
    exact hnnB
  exact h1
  have h2 : (¬¬A ∧ ¬¬B) → ¬¬(A ∧ B) := by
    intro h
    have hnna : ¬¬A := by apply conj_elim_left (¬¬A) (¬¬B) h
    have hnnb : ¬¬B := by apply conj_elim_right (¬¬A) (¬¬B) h
    intro hcont
    apply hnna
    intro hna
    apply hnnb
    intro hnb
    have hab : A ∧ B := by apply conj_intro A B hna hnb
    exact hcont hab
  exact h2
end Propositional
