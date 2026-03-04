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
  | .imp f1 f2 => is_free_in x f1 || is_free_in x f2
  | .conj f1 f2 => is_free_in x f1 || is_free_in x f2
  | .disj f1 f2 => is_free_in x f1 || is_free_in x f2
  | .all y body => if x == y then false else is_free_in x body

  | .exi y body => if x == y then false else is_free_in x body

def substF (A : Formula) (x : String) (s : Term) : Formula :=
  match A with
  | .atom p ts => .atom p (ts.map (substT · x s))
  | .bot => .bot

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

axiom lift_prop {A : Propositional.Minimal.Formula} :
  Propositional.Minimal.is_provable A -> is_provable (toFOL A)

-- Deduction and Inference
axiom mp {A B : Formula} : is_provable (A → B) -> is_provable A -> is_provable B
axiom deduction {A B : Formula} : (is_provable A -> is_provable B) -> is_provable (A → B)

-- Basic Hilbert Axioms (Re-declared for FOL.Formula)
axiom aff_cons (A B : Formula) : is_provable (A → (B → A))
axiom dist_imp (A B C : Formula) : is_provable ((A → (B → C)) → ((A → B) → (A → C)))
axiom conj_intro (A B : Formula) : is_provable (A → (B → (A ∧ B)))
axiom conj_elim_left (A B : Formula) : is_provable ((A ∧ B) → A)
axiom conj_elim_right (A B : Formula) : is_provable ((A ∧ B) → B)
axiom disj_intro_left (A B : Formula) : is_provable (A → (A ∨ B))
axiom disj_intro_right (A B : Formula) : is_provable (B → (A ∨ B))
axiom disj_elim (A B C : Formula) : is_provable ((A → C) → ((B → C) → ((A ∨ B) → C)))

-- Quantifier Axioms
axiom forall_elim (x : String) (A : Formula) (t : Term) :
  (is_free_for t x A = true) → is_provable (∀ x, A) -> is_provable (A⟦x := t⟧)

axiom exists_intro (x : String) (A : Formula) (t : Term) :
  (is_free_for t x A = true) → is_provable (A⟦x := t⟧) -> is_provable (∃ x, A)

-- Deduction Rules
axiom rule_gen {A B : Formula} {x : String} :
  is_provable (A → B) -> (is_free_in x A = false) -> is_provable (A → (∀ x, B))

axiom rule_exists_elim {A B : Formula} {x : String} :
  is_provable (A → B) -> (is_free_in x B = false) -> is_provable ((∃ x, A) → B)

end FOL.Minimal
