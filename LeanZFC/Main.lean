import Lean

namespace ZFC

-- Definitions

def id.{u} {α : Sort u} (x : α) : α := x

infixr:1 (priority := high) " # " => id

-- Definitions

def true : Prop := ∀ (P : Prop), P → P

def false : Prop := ∀ (P : Prop), P

def not (P : Prop) : Prop := P → false

prefix:40 (priority := high) "¬" => not

def or (P Q : Prop) : Prop := ¬P → Q

infixr:30 (priority := high) " ∨ " => or

def and (P Q : Prop) : Prop := ¬(¬P ∨ ¬Q)

infixr:35 (priority := high) " ∧ " => and

def iff (P Q : Prop) : Prop := (P → Q) ∧ (Q → P)

infixl:20 (priority := high) " ↔ " => iff

def eq {α : Type} (x y : α) : Prop := ∀ (P : α → Prop), P x → P y

infixl:50 (priority := high) " = " => eq

def ne {α : Type} (x y : α) : Prop := ¬(x = y)

infixl:50 (priority := high) " ≠ " => ne

def exi {α : Type} (P : α → Prop) : Prop := ¬(∀ (x : α), ¬P x)

def exiu {α : Type} (P : α → Prop) : Prop := exi P ∧ (∀ (x y : α), P x → P y → x = y)

-- Axioms

axiom prop_rec (F: Prop → Prop) {P: Prop} : F true → F false → F P
axiom fun_ext {A B: Type} (f g: A → B) : (∀ x, f x = g x) → f = g

-- Theorems

theorem trivial : true := λ _ => id

theorem not_false : not false := id

theorem not_not_intro {P : Prop} (h : P) : ¬¬P := λ h1 => h1 h

theorem not_not_elim {P : Prop} (h : ¬¬P) : P := prop_rec (λ x => ¬¬x → x) (λ _ => trivial) (λ h1 => h1 not_false) h

theorem exc_mid {P : Prop} : P ∨ ¬P := id

theorem false_elim {P : Prop} (h : false) : P := h P

theorem exfalso {P : Prop} (h : false) : P := false_elim h

theorem modus_ponens {P Q : Prop} (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem modus_tollens {P Q : Prop} (h1 : P → Q) (h2 : ¬Q) : ¬P := λ h3 => h2 (h1 h3)

theorem or_intro_left {P Q : Prop} (h : P) : P ∨ Q := λ h1 => false_elim (h1 h)

theorem or_intro_right {P Q : Prop} (h : Q) : P ∨ Q := λ _ => h

theorem or_elim {P Q R : Prop} (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := not_not_elim # λ h4 => h4 # h3 # h1 # modus_tollens h2 h4

theorem and_intro {P Q : Prop} (h1 : P) (h2 : Q) : P ∧ Q := λ h3 => or_elim h3 (λ h4 => h4 h1) (λ h4 => h4 h2)

theorem and_elim_left {P Q : Prop} (h : P ∧ Q) : P := sorry

theorem and_elim_right {P Q : Prop} (h : P ∧ Q) : Q := sorry

end ZFC
