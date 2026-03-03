import LeanZFC.Minimal_Logic
import LeanZFC.Intuionistic_Logic

namespace ZFC

-- Double Negation Elimination
axiom double_neg_elim (A : Prop) : ¬¬A → A

-- Theorems

theorem proof_by_contradiction (A : Prop) : (¬A → False) → A := by
  intro h
  apply double_neg_elim A
  intro hna
  apply h hna

theorem exc_mid (A : Prop) : A ∨ ¬A := by
  apply proof_by_contradiction
  intro h
  have hna : ¬A := by
    intro ha
    apply h
    apply disj_intro_left A (¬A) ha
  apply h
  apply disj_intro_right A (¬A) hna

theorem ex_falso_quod_classical (A : Prop) : False → A := by
  intro f
  apply proof_by_contradiction
  intro h
  apply f

theorem double_neg_equiv (A : Prop) : A ↔ ¬¬A := by
  have h1 : A → ¬¬A := by
    apply imp_neg_neg A
  have h2 : ¬¬A → A := by
    intro h
    apply double_neg_elim A h
  exact ⟨h1, h2⟩

theorem disj_iff_neg_neg_conj (A B : Prop) : (A ∨ B) ↔ ¬(¬A ∧ ¬B) := by
  have h1 : (A ∨ B) → ¬(¬A ∧ ¬B) := by
    intro h
    rw[←de_morgan_disj A B]
    rw[←double_neg_equiv (A ∨ B)]
    exact h
  have h2 : ¬(¬A ∧ ¬B) → (A ∨ B) := by
    have h' : ¬(A ∨ B) → (¬A ∧ ¬B) := by
      intro h
      rw [de_morgan_disj A B] at h
      exact h
    intro h
    rw [←de_morgan_disj A B] at h
    apply double_neg_elim (A ∨ B)
    exact h
  exact ⟨h1, h2⟩

theorem conj_iff_neg_neg_disj (A B : Prop) : (A ∧ B) ↔ ¬(¬A ∨ ¬B) := by
  have h1 : (A ∧ B) → ¬(¬A ∨ ¬B) := by
    intro h
    rw [de_morgan_disj]
    rw [←double_neg_equiv A]
    rw [←double_neg_equiv B]
    exact h
  have h2 : ¬(¬A ∨ ¬B) → (A ∧ B) := by
    intro h
    rw [de_morgan_disj] at h
    rw [←double_neg_equiv A] at h
    rw [←double_neg_equiv B] at h
    exact h
  exact ⟨h1, h2⟩

theorem imp_iff_neg_disj (A B : Prop) : (A → B) ↔ (¬A ∨ B) := by
  have h1 : (A → B) → (¬A ∨ B) := by
    intro h
    apply disj_elim A (¬A) (¬A ∨ B)
    intro ha
    have hb : B := h ha
    apply disj_intro_right (¬A) B hb
    intro hna
    apply disj_intro_left (¬A) B hna
    exact exc_mid A
  have h2 : (¬A ∨ B) → (A → B) := by
    apply neg_disj_to_imp A B
  exact ⟨h1, h2⟩

theorem de_morgan_conj (A B : Prop) : ¬(A ∧ B) ↔ (¬A ∨ ¬B) := by
  have h1 : ¬(A ∧ B) → (¬A ∨ ¬B) := by
    intro h
    apply proof_by_contradiction
    intro h1
    have ha: A := by
      apply proof_by_contradiction
      intro hna
      apply h1
      apply disj_intro_left (¬A) (¬B) hna
    have hb: B := by
      apply proof_by_contradiction
      intro hnb
      apply h1
      apply disj_intro_right (¬A) (¬B) hnb
    apply h
    apply conj_intro A B ha hb
  have h2 : (¬A ∨ ¬B) → ¬(A ∧ B) := by
    intro h
    apply disj_neg A B
    exact h
  exact ⟨h1, h2⟩

theorem neg_imp_iff_conj_neg (A B : Prop) : ¬(A → B) ↔ (A ∧ ¬B) := by
  have h1 : ¬(A → B) → (A ∧ ¬B) := by
    intro h
    rw [imp_iff_neg_disj] at h
    rw [de_morgan_disj] at h
    rw [←double_neg_equiv] at h
    exact h
  have h2 : (A ∧ ¬B) → ¬(A → B) := by
    intro h
    rw [imp_iff_neg_disj]
    rw [de_morgan_disj]
    rw [←double_neg_equiv]
    exact h
  exact ⟨h1, h2⟩

theorem iff_contrapositive (A B : Prop) : (A → B) ↔ (¬B → ¬A) := by
  have h1 : (A → B) → (¬B → ¬A) := by
    apply imp_contrapositive A B
  have h2 : (¬B → ¬A) → (A → B) := by
    intro h
    rw [imp_iff_neg_disj]
    rw [imp_iff_neg_disj] at h
    rw [←double_neg_equiv B] at h
    apply disj_symm
    exact h
  exact ⟨h1, h2⟩

theorem dist_imp_conj (A B C : Prop) : (A → (B ∧ C)) ↔ ((A → B) ∧ (A → C)) := by
  have h1 : (A → (B ∧ C)) → ((A → B) ∧ (A → C)) := by
    intro h
    apply conj_intro
    intro ha
    have hbc : B ∧ C := h ha
    apply conj_elim_left B C hbc
    intro ha
    have hbc : B ∧ C := h ha
    apply conj_elim_right B C hbc
  have h2 : ((A → B) ∧ (A → C)) → (A → (B ∧ C)) := by
    intro h
    intro ha
    apply conj_intro
    have hab : A → B := by apply conj_elim_left (A → B) (A → C) h
    have hbc : B := by apply hab ha
    exact hbc
    have hac : A → C := by apply conj_elim_right (A → B) (A → C) h
    have hbc : C := by apply hac ha
    exact hbc
  exact ⟨h1, h2⟩

theorem peirce (A B : Prop) : (((A → B) → A) → A) := by
  intro h
  apply proof_by_contradiction
  intro hna
  have hab : A → B := by
    intro ha
    apply ex_falso_quod_classical B
    apply hna ha
  have ha : A := by
    apply h hab
  apply hna ha

end ZFC
