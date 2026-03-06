import Propositional.Prop_Minimal

namespace FOL.Minimal

/- 1. Syntax: Terms and Variables -/

inductive Term where

  | var  : String → Term
  | func : String -> List Term -> Term

open Term

/- 2. Syntax: Formulas -/

inductive Formula where

  | atom : String -> List Term -> Formula
  | bot  : Formula
  | top  : Formula
  | imp  : Formula -> Formula -> Formula

  | conj : Formula -> Formula -> Formula
  | disj : Formula -> Formula -> Formula
  | all  : String -> Formula -> Formula

  | exi  : String -> Formula -> Formula

open Formula

/- 3. Notation -/

notation:max A " → " B => Formula.imp A B
notation:max A " ∧ " B => Formula.conj A B
notation:max A " ∨ " B => Formula.disj A B
notation:max "¬" A     => Formula.imp A Formula.bot
notation:max "∀ " x ", " A => Formula.all x A
notation:max "∃ " x ", " A => Formula.exi x A
notation:max A " ↔ " B => Formula.conj (Formula.imp A B) (Formula.imp B A)

/- 4. Substitution Logic -/

def freeVarsTerm (t : Term) : List String :=
  match t with
  | .var y => [y]
  | .func _ ts => ts.flatMap freeVarsTerm

def substT (t : Term) (x : String) (s : Term) : Term :=
  match t with

  | .var y => if x == y then s else .var y
  | .func f ts => .func f (ts.map (substT · x s))

def is_free_in (x : String) (A : Formula) : Bool :=
  match A with

  | .atom _ ts => (ts.flatMap freeVarsTerm).contains x
  | .bot => false
  | .top => false
  | .imp f1 f2 => is_free_in x f1 || is_free_in x f2
  | .conj f1 f2 => is_free_in x f1 || is_free_in x f2
  | .disj f1 f2 => is_free_in x f1 || is_free_in x f2
  | .all y body => if x == y then false else is_free_in x body

  | .exi y body => if x == y then false else is_free_in x body

def substF (A : Formula) (x : String) (s : Term) : Formula :=
  match A with
  | .atom p ts => .atom p (ts.map (substT · x s))
  | .bot => .bot
  | .top => .top
  | .imp f1 f2 => .imp (substF f1 x s) (substF f2 x s)
  | .conj f1 f2 => .conj (substF f1 x s) (substF f2 x s)
  | .disj f1 f2 => .disj (substF f1 x s) (substF f2 x s)

  | .all y body => if x == y then .all y body else .all y (substF body x s)
  | .exi y body => if x == y then .exi y body else .exi y (substF body x s)

notation A "⟦" x " := " t "⟧" => substF A x t

def is_free_for (s : Term) (x : String) (A : Formula) : Bool :=
  match A with

  | .atom _ _ => true
  | .bot => true
  | .top => true
  | .imp f1 f2 => is_free_for s x f1 && is_free_for s x f2

  | .conj f1 f2 => is_free_for s x f1 && is_free_for s x f2
  | .disj f1 f2 => is_free_for s x f1 && is_free_for s x f2
  | .all y body =>
      if x == y then true
      else if (freeVarsTerm s).contains y then false
      else is_free_for s x body

  | .exi y body =>
      if x == y then true
      else if (freeVarsTerm s).contains y then false
      else is_free_for s x body

/- 5. Provability and Axioms -/

axiom is_provable : Formula → Prop

-- Lifting from Propositional
def toFOL : Propositional.Minimal.Formula → Formula
  | .var s    => .atom s []
  | .bot      => .bot

  | .top      => .imp .bot .bot
  | .imp A B  => .imp (toFOL A) (toFOL B)
  | .conj A B => .conj (toFOL A) (toFOL B)

  | .disj A B => .disj (toFOL A) (toFOL B)
  | .neg A    => .imp (toFOL A) .bot
  | .iff A B  => .conj (.imp (toFOL A) (toFOL B)) (.imp (toFOL B) (toFOL A))

-- ==========================================
-- PROPOSITIONAL CORE
-- ==========================================
axiom lift_prop {A : Propositional.Minimal.Formula} :
  Propositional.Minimal.is_provable A -> is_provable (toFOL A)

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

-- ==========================================
-- INFERENCE RULES
-- ==========================================
axiom mp {A B : Formula} : is_provable (A → B) -> is_provable A -> is_provable B
axiom deduction {A B : Formula} : (is_provable A -> is_provable B) -> is_provable (A → B)

-- ==========================================
-- QUANTIFIER AXIOMS & RULES
-- ==========================================
axiom forall_elim (x : String) (A : Formula) (t : Term) :
  (is_free_for t x A = true) → is_provable (∀ x, A) -> is_provable (A⟦x := t⟧)

axiom exists_intro (x : String) (A : Formula) (t : Term) :
  (is_free_for t x A = true) → is_provable (A⟦x := t⟧) -> is_provable (∃ x, A)

axiom rule_gen {A B : Formula} {x : String} :
  is_provable (A → B) -> (is_free_in x A = false) -> is_provable (A → (∀ x, B))

axiom rule_gen_simple {A : Formula} (x : String) :
  is_provable A -> is_provable (∀ x, A)

axiom rule_exists_elim {A B : Formula} {x : String} :
  is_provable (A → B) -> (is_free_in x B = false) -> is_provable ((∃ x, A) → B)

-- ==========================================
-- VARIABLE DYNAMICS
-- ==========================================
axiom is_free_in_imp (x : String) (A B : Formula) :
  is_free_in x (A → B) = (is_free_in x A || is_free_in x B)

axiom is_free_in_conj (x : String) (A B : Formula) :
  is_free_in x (A ∧ B) = (is_free_in x A || is_free_in x B)

axiom is_free_in_disj (x : String) (A B : Formula) :
  is_free_in x (A ∨ B) = (is_free_in x A || is_free_in x B)

axiom is_free_in_all (x : String) (y : String) (A : Formula) :
  is_free_in x (∀ y, A) = (if x == y then false else is_free_in x A)

axiom is_free_in_exi (x : String) (y : String) (A : Formula) :
  is_free_in x (∃ y, A) = (if x == y then false else is_free_in x A)

axiom is_free_for_var (A : Formula) (x : String) :
  is_free_in x A = false -> is_free_for (.var x) x A = true

axiom is_free_for_self (A : Formula) (x : String) :
  is_free_for (.var x) x A = true

-- ==========================================
-- SUBSTITUTION DYNAMICS
-- ==========================================
axiom substF_self (A : Formula) (x : String) :
  A⟦x := .var x⟧ = A

axiom substF_id (A : Formula) (x : String) (s : Term) :
  is_free_in x A = false -> A⟦x := s⟧ = A

axiom substT_id (t : Term) (x : String) (s : Term) :
  (freeVarsTerm t).contains x = false -> substT t x s = t

axiom substF_imp (A B : Formula) (x : String) (s : Term) :
  (A → B)⟦x := s⟧ = (A⟦x := s⟧ → B⟦x := s⟧)

axiom substF_conj (A B : Formula) (x : String) (s : Term) :
  (A ∧ B)⟦x := s⟧ = (A⟦x := s⟧ ∧ B⟦x := s⟧)

axiom substF_disj (A B : Formula) (x : String) (s : Term) :
  (A ∨ B)⟦x := s⟧ = (A⟦x := s⟧ ∨ B⟦x := s⟧)

axiom substF_all_same (A : Formula) (x : String) (s : Term) :
  (∀ x, A)⟦x := s⟧ = (∀ x, A)

axiom substF_all_diff (A : Formula) (x y : String) (s : Term) :
  x ≠ y -> (∀ y, A)⟦x := s⟧ = (∀ y, A⟦x := s⟧)

def exists_intro_self (x : String) (A : Formula) (h_provable : is_provable A) : is_provable (∃ x, A) :=
  let h_ffs := is_free_for_self A x
  let h_subst := Eq.mpr (congrArg is_provable (substF_self A x)) h_provable
  exists_intro x A (.var x) h_ffs h_subst

def forall_elim_self (x : String) (A : Formula) (h_provable : is_provable (∀ x, A)) : is_provable A :=
  let h_ffs := is_free_for_self A x
  let h_inst := forall_elim x A (.var x) h_ffs h_provable
  Eq.mp (congrArg is_provable (substF_self A x)) h_inst

-- Theorems

theorem forall_vacuous (A : Formula) (x : String) : is_free_in x A = false -> is_provable ((∀ x, A) ↔ A) := by
  intro hfree
  have hfwd : is_provable ((∀ x, A) → A) := by
    apply deduction
    intro hall
    let h_is_free := is_free_for_var A x hfree
    let h_sub := substF_id A x (.var x) hfree
    let p := forall_elim x A (.var x) h_is_free hall
    rw [h_sub] at p
    exact p

  have hbwd : is_provable (A → (∀ x, A)) := by
    apply rule_gen
    apply deduction
    intro ha
    exact ha
    exact hfree

  exact mp (mp (iff_intro (∀ x, A) A) hfwd) hbwd

theorem exists_vacuous (A : Formula) (x : String) : is_free_in x A = false -> is_provable ((∃ x, A) ↔ A) := by
  intro hfree
  have hfwd: is_provable ((∃ x, A) → A) := by
    apply rule_exists_elim
    apply deduction
    intro ha
    exact ha
    exact hfree
  have hbwd: is_provable (A → (∃ x, A)) := by
    apply deduction
    intro ha
    let h_is_free := is_free_for_var A x hfree
    let h_sub := substF_id A x (.var x) hfree
    let p := exists_intro x A (.var x) h_is_free
    rw [h_sub] at p
    exact p ha
  exact mp (mp (iff_intro (∃ x, A) A) hfwd) hbwd

theorem forall_conj_dist (A B : Formula) (x : String) : is_provable ((∀ x, (A ∧ B)) ↔ ((∀ x, A) ∧ (∀ x, B))) := by
  have hfwd : is_provable ((∀ x, (A ∧ B)) → ((∀ x, A) ∧ (∀ x, B))) := by
    apply deduction
    intro hall
    let h_is_free := is_free_for_self (A ∧ B) x
    let p := forall_elim x (A ∧ B) (.var x) h_is_free hall
    rw [substF_self (A ∧ B) x] at p
    have ha : is_provable A := mp (conj_elim_left A B) p
    have hb : is_provable B := mp (conj_elim_right A B) p
    have ha_all : is_provable (∀ x, A) := by
      apply rule_gen_simple
      exact ha
    have hb_all : is_provable (∀ x, B) := by
      apply rule_gen_simple
      exact hb
    exact mp (mp (conj_intro (∀ x, A) (∀ x, B)) ha_all) hb_all

  have hbwd : is_provable (((∀ x, A) ∧ (∀ x, B)) → (∀ x, (A ∧ B))) := by
    apply deduction
    intro h_conj_all
    have ha_all := mp (conj_elim_left (∀ x, A) (∀ x, B)) h_conj_all
    have hb_all := mp (conj_elim_right (∀ x, A) (∀ x, B)) h_conj_all
    let pa := forall_elim x A (.var x) (is_free_for_self A x) ha_all
    rw [substF_self A x] at pa
    let pb := forall_elim x B (.var x) (is_free_for_self B x) hb_all
    rw [substF_self B x] at pb
    have hab : is_provable (A ∧ B) := mp (mp (conj_intro A B) pa) pb
    apply rule_gen_simple
    exact hab

  exact mp (mp (iff_intro (∀ x, (A ∧ B)) ((∀ x, A) ∧ (∀ x, B))) hfwd) hbwd

theorem exists_conj_dist_left (A B : Formula) (x : String) : is_free_in x B = false -> is_provable ((∃ x, (A ∧ B)) ↔ ((∃ x, A) ∧ B)) := by
  intro hfree
  have hfwd : is_provable ((∃ x, (A ∧ B)) → ((∃ x, A) ∧ B)) := by
    apply rule_exists_elim
    apply deduction
    intro hab
    have ha : is_provable A := mp (conj_elim_left A B) hab
    have hb : is_provable B := mp (conj_elim_right A B) hab
    have hex_a : is_provable (∃ x, A) := by
      let h_intro := exists_intro x A (.var x) (is_free_for_self A x)
      rw [substF_self] at h_intro
      exact h_intro ha
    exact mp (mp (conj_intro (∃ x, A) B) hex_a) hb
    rw [is_free_in_conj]
    rw [is_free_in_exi, hfree]
    simp only [BEq.rfl, ↓reduceIte, Bool.or_self]

  have hbwd : is_provable (((∃ x, A) ∧ B) → (∃ x, (A ∧ B))) := by
    apply deduction
    intro h_ex_a_b
    have hex_a := mp (conj_elim_left (∃ x, A) B) h_ex_a_b
    have hb := mp (conj_elim_right (∃ x, A) B) h_ex_a_b

    have h_target : is_provable ((∃ x, A) → (∃ x, (A ∧ B))) := by
      apply rule_exists_elim
      apply deduction
      intro ha
      have hab : is_provable (A ∧ B) := mp (mp (conj_intro A B) ha) hb
      let h_intro := exists_intro x (A ∧ B) (.var x) (is_free_for_self (A ∧ B) x)
      rw [substF_self] at h_intro
      exact h_intro hab
      rw [is_free_in_exi]
      simp only [BEq.rfl, ↓reduceIte]

    exact mp h_target hex_a

  exact mp (mp (iff_intro (∃ x, (A ∧ B)) ((∃ x, A) ∧ B)) hfwd) hbwd

theorem forall_disj_dist_left (A B : Formula) (x : String) : is_free_in x B = false -> is_provable ((∀ x, (A ∨ B)) ↔ ((∀ x, A) ∨ B)) := by
  intro hfree
  have hfwd : is_provable ((∀ x, (A ∨ B)) → ((∀ x, A) ∨ B)) := by
    apply deduction
    intro hall
    have h_inst : is_provable (A ∨ B) := by
      let step := forall_elim x (A ∨ B) (.var x) (is_free_for_self (A ∨ B) x) hall
      rw [substF_self] at step
      exact step
    apply mp (mp (mp (disj_elim A B ((∀ x, A) ∨ B)) ?caseA) ?caseB) h_inst
    apply deduction
    intro ha
    have hallA : is_provable (∀ x, A) := rule_gen_simple x ha
    exact mp (disj_intro_left (∀ x, A) B) hallA
    apply deduction
    intro hb
    exact mp (disj_intro_right (∀ x, A) B) hb

  have hbwd : is_provable (((∀ x, A) ∨ B) → (∀ x, (A ∨ B))) := by
    apply deduction
    intro hor
    have hA : is_provable ((∀ x, A) → (∀ x, (A ∨ B))) := by
      apply deduction
      intro haall
      let inst := forall_elim x A (.var x) (is_free_for_self A x) haall
      rw [substF_self] at inst
      exact rule_gen_simple x (mp (disj_intro_left A B) inst)
    have hB : is_provable (B → (∀ x, (A ∨ B))) := by
      apply deduction
      intro hb
      exact rule_gen_simple x (mp (disj_intro_right A B) hb)
    exact mp (mp (mp (disj_elim (∀ x, A) B (∀ x, (A ∨ B))) hA) hB) hor

  exact mp (mp (iff_intro (∀ x, (A ∨ B)) ((∀ x, A) ∨ B)) hfwd) hbwd

theorem exists_disj_dist (A B : Formula) (x : String) : is_provable ((∃ x, (A ∨ B)) ↔ ((∃ x, A) ∨ (∃ x, B))) := by
  have hfwd : is_provable ((∃ x, (A ∨ B)) → ((∃ x, A) ∨ (∃ x, B))) := by
    apply rule_exists_elim
    · apply deduction
      intro hab
      apply mp (mp (mp (disj_elim A B ((∃ x, A) ∨ (∃ x, B))) ?caseA) ?caseB) hab
      · apply deduction
        intro ha
        have hex_a : is_provable (∃ x, A) := by
          let h_rule := exists_intro x A (.var x) (is_free_for_self A x)
          rw [substF_self] at h_rule
          exact h_rule ha
        exact mp (disj_intro_left (∃ x, A) (∃ x, B)) hex_a
      · apply deduction
        intro hb
        have hex_b : is_provable (∃ x, B) := by
          let h_rule := exists_intro x B (.var x) (is_free_for_self B x)
          rw [substF_self] at h_rule
          exact h_rule hb
        exact mp (disj_intro_right (∃ x, A) (∃ x, B)) hex_b
    · rw [is_free_in_disj, is_free_in_exi, is_free_in_exi]
      simp

  have hbwd : is_provable (((∃ x, A) ∨ (∃ x, B)) → (∃ x, (A ∨ B))) := by
    apply deduction
    intro h_or_ex
    apply mp (mp (mp (disj_elim (∃ x, A) (∃ x, B) (∃ x, (A ∨ B))) ?to_exi_a) ?to_exi_b) h_or_ex
    · apply rule_exists_elim
      · apply deduction
        intro ha
        have h_intro := exists_intro x (A ∨ B) (.var x) (is_free_for_self (A ∨ B) x)
        rw [substF_self] at h_intro
        exact h_intro (mp (disj_intro_left A B) ha)
      · rw [is_free_in_exi]
        simp
    · apply rule_exists_elim
      · apply deduction
        intro hb
        have h_intro := exists_intro x (A ∨ B) (.var x) (is_free_for_self (A ∨ B) x)
        rw [substF_self] at h_intro
        exact h_intro (mp (disj_intro_right A B) hb)
      · rw [is_free_in_exi]
        simp

  exact mp (mp (iff_intro (∃ x, (A ∨ B)) ((∃ x, A) ∨ (∃ x, B))) hfwd) hbwd

theorem forall_imp_dist_left (A B : Formula) (x : String) :
  is_free_in x B = false -> is_provable ((∀ x, (A → B)) ↔ ((∃ x, A) → B)) := by
  intro hfree
  have hfwd : is_provable ((∀ x, (A → B)) → ((∃ x, A) → B)) := by
    apply deduction
    intro hall
    apply rule_exists_elim
    · apply deduction
      intro ha
      let hinst := forall_elim x (A → B) (.var x) (is_free_for_self (A → B) x) hall
      rw [substF_self] at hinst
      exact mp hinst ha
    · exact hfree
  have hbwd : is_provable (((∃ x, A) → B) → (∀ x, (A → B))) := by
    apply deduction
    intro hex_imp
    apply rule_gen_simple
    · apply deduction
      intro ha
      have hex_a : is_provable (∃ x, A) := by
        let h_rule := exists_intro x A (.var x) (is_free_for_self A x)
        rw [substF_self] at h_rule
        exact h_rule ha
      exact mp hex_imp hex_a
  exact mp (mp (iff_intro (∀ x, (A → B)) ((∃ x, A) → B)) hfwd) hbwd

theorem exists_imp_dist_left (A B : Formula) (x : String) :
  is_free_in x B = false -> is_provable ((∃ x, (A → B)) → ((∀ x, A) → B)) := by
  intro hfree
  apply deduction
  intro hex_imp
  apply deduction
  intro hall_a
  apply mp (rule_exists_elim ?step hfree) hex_imp
  apply deduction
  intro h_imp
  let ha := forall_elim x A (.var x) (is_free_for_self A x) hall_a
  rw [substF_self] at ha
  exact mp h_imp ha

theorem forall_imp_dist_right (A B : Formula) (x : String) :
  is_free_in x A = false -> is_provable ((∀ x, (A → B)) ↔ (A → (∀ x, B))) := by
  intro hfree
  have hfwd : is_provable ((∀ x, (A → B)) → (A → (∀ x, B))) := by
    apply deduction
    intro hall
    apply deduction
    intro ha
    apply rule_gen_simple
    let hinst := forall_elim x (A → B) (.var x) (is_free_for_self (A → B) x) hall
    rw [substF_self] at hinst
    exact mp hinst ha

  have hbwd : is_provable ((A → (∀ x, B)) → (∀ x, (A → B))) := by
    apply deduction
    intro ha_all_b
    apply rule_gen_simple
    apply deduction
    intro ha
    let hall_b := mp ha_all_b ha
    let hinst_b := forall_elim x B (.var x) (is_free_for_self B x) hall_b
    rw [substF_self] at hinst_b
    exact hinst_b

  exact mp (mp (iff_intro (∀ x, (A → B)) (A → (∀ x, B))) hfwd) hbwd

theorem exists_imp_dist_right (A B : Formula) (x : String) :
  is_free_in x A = false -> is_provable ((∃ x, (A → B)) → (A → (∃ x, B))) := by
  intro hfree
  apply deduction
  intro hex_imp
  apply deduction
  intro ha
  let target := ∃ x, B
  apply mp (rule_exists_elim ?step ?side) hex_imp
  · apply deduction
    intro h_imp
    have hb : is_provable B := mp h_imp ha
    let h_intro := exists_intro x B (.var x) (is_free_for_self B x)
    rw [substF_self] at h_intro
    exact h_intro hb
  · rw [is_free_in_exi]
    simp

theorem neg_exists_iff_forall_neg (A : Formula) (x : String) : is_provable ((¬(∃ x, A)) ↔ ((∀ x, ¬A))) := by
  have hfwd : is_provable ((¬(∃ x, A)) → (∀ x, ¬A)) := by
    apply deduction
    intro hnexi
    apply rule_gen_simple
    apply deduction
    intro ha
    have hex : is_provable (∃ x, A) := exists_intro_self x A ha
    have h_bot : is_provable bot := mp hnexi hex
    exact h_bot
  have hbwd : is_provable ((∀ x, ¬A) → ¬(∃ x, A)) := by
    apply deduction
    intro hallna
    have h_inner : is_provable (A → ((∀ x, ¬A) → bot)) := by
      apply deduction
      intro ha
      apply deduction
      intro h_all
      have h_na : is_provable (¬A) := forall_elim_self x (¬A) h_all
      have h_a_bot : is_provable (A → bot) := h_na
      exact mp h_a_bot ha
    have h_ex_elim : is_provable ((∃ x, A) → ((∀ x, ¬A) → bot)) := rule_exists_elim h_inner (by simp [is_free_in])
    have h_goal_imp : is_provable ((∃ x, A) → bot) := by
      apply deduction
      intro hexi
      exact mp (mp h_ex_elim hexi) hallna
    exact h_goal_imp
  exact mp (mp (iff_intro (¬(∃ x, A)) (∀ x, ¬A)) hfwd) hbwd

theorem neg_forall_from_exists_neg (A : Formula) (x : String) : is_provable ((∃ x, ¬A) → ¬(∀ x, A)) := by
  apply deduction
  intro hex_na
  have h_inner : is_provable ((A → bot) → (∀ x, A) → bot) := by
    apply deduction
    intro hna
    apply deduction
    intro hall
    let ha := forall_elim_self x A hall
    exact mp hna ha
  have h_free : is_free_in x ((∀ x, A) → bot) = false := by simp [is_free_in]
  have h7 : is_provable ((∃ x, ¬A) → ¬(∀ x, A)) := by
    apply deduction
    intro h_ex_na
    let h_elim := rule_exists_elim h_inner h_free
    let h_all_to_bot := mp h_elim h_ex_na
    exact mp (neg_intro (∀ x, A)) h_all_to_bot
  have h_forall_to_bot : is_provable ((∀ x, A) → bot) := mp h7 hex_na
  exact mp (neg_intro (∀ x, A)) h_forall_to_bot

end FOL.Minimal
