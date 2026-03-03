import LeanZFC.Minimal_Logic

namespace ZFC

-- Ex Falso Quodlibet
axiom ex_falso_quodlibet (A : Prop) : False → A -- From False, anything follows

-- Theorems

theorem false_iff_conj_neg (A : Prop) : False ↔ (A ∧ ¬A) := by
  have h1 : False → (A ∧ ¬A) := by
    intro f
    have h2 : A ∧ ¬A := ex_falso_quodlibet (A ∧ ¬A) f
    exact h2
  have h2 : (A ∧ ¬A) → False := by
    intro h
    have h3 : ¬(A ∧ ¬A) := by apply non_contradiction
    apply h3 h
  exact ⟨h1, h2⟩

theorem neg_to_imp (A B : Prop) : ¬A → (A → B) := by
  intro h
  intro a
  have h1 : A ∧ ¬A := by apply conj_intro A (¬A) a h
  rw [←false_iff_conj_neg A] at h1
  apply ex_falso_quodlibet B h1

theorem neg_disj_to_imp (A B : Prop) : ¬(A ∨ B) → (A → B) := by
  intro h
  intro a
  have h1 : A ∨ B := by apply disj_intro_left A B a
  have h2 : (A ∨ B) ∧ ¬(A ∨ B) := by apply conj_intro (A ∨ B) (¬(A ∨ B)) h1 h
  have h3 : False := by rw [←false_iff_conj_neg (A ∨ B)] at h2; exact h2
  apply ex_falso_quodlibet B h3

theorem disj_to_neg_imp (A B : Prop) : (A ∨ B) → (¬A → B) := by
  intro h
  intro hna
  apply disj_elim A B B
  intro ha
  apply neg_to_imp A B hna ha
  intro hb
  exact hb
  exact h

theorem neg_imp_to_neg_neg (A B : Prop) : ¬(A → B) → ¬¬A := by
  intro h
  intro hna
  have h1 : A → B := by apply neg_to_imp A B hna
  apply h h1

theorem neg_neg_imp_iff_imp_neg_neg (A B : Prop) : ¬¬(A → B) ↔ (¬¬A → ¬¬B) := by
  have h1 : ¬¬(A → B) → (¬¬A → ¬¬B) := by
    intro h
    intro hnna
    intro hnb
    have hnab: ¬(A → B) := by
      intro hab
      have hna : ¬A := by
        intro a
        have b : B := hab a
        apply hnb b
      apply hnna hna
    apply h hnab
  have h2 : (¬¬A → ¬¬B) → ¬¬(A → B) := by
    intro hnnannb
    intro hnab
    apply hnnannb
    intro hna
    apply hnab
    intro ha
    apply ex_falso_quodlibet B (hna ha)
    intro hb
    apply hnab
    intro ha
    exact hb
  exact ⟨h1, h2⟩

theorem disj_false_iff_self (A : Prop) : (A ∨ False) ↔ A := by
  have h1 : (A ∨ False) → A := by
    intro h
    apply disj_elim A False A
    intro ha
    exact ha
    intro hf
    have h2 : False := by exact hf
    apply ex_falso_quodlibet A h2
    exact h
  have h2 : A → (A ∨ False) := by
    intro a
    apply disj_intro_left A False a
  exact ⟨h1, h2⟩

theorem conj_false_iff_false (A : Prop) : (A ∧ False) ↔ False := by
  have h1 : (A ∧ False) → False := by
    intro h
    apply conj_elim_right A False h
  have h2 : False → (A ∧ False) := by
    intro f
    apply conj_intro A False (ex_falso_quodlibet A f) f
  exact ⟨h1, h2⟩
end ZFC
