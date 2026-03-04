import LeanZFC.Minimal_Logic

namespace FirstOrder

inductive Term where

  | var : String → Term
  | func : String → List Term → Term

inductive Formula where

  | atom : String → List Term → Formula
  | imp  : Formula → Formula → Formula
  | all  : String → Formula → Formula
  | exi  : String → Formula → Formula

open Term Formula

def union (l1 l2 : List String) : List String :=
  match l1 with

  | [] => l2
  | x :: xs =>
      if l2.contains x then union xs l2
      else x :: union xs l2

def freeVars (t : Term) : List String :=
  match t with

  | .var y => [y]
  | .func _ ts => ts.foldl (fun acc ti => union acc (freeVars ti)) []

def substT (t : Term) (x : String) (s : Term) : Term :=
  match t with

  | .var y => if x == y then s else .var y
  | .func f ts => .func f (ts.map (substT · x s))

def substF (A : Formula) (x : String) (s : Term) : Formula :=
  match A with

  | .atom p ts => .atom p (ts.map (substT · x s))
  | .imp f1 f2 => .imp (substF f1 x s) (substF f2 x s)
  | .all y body =>
      if x == y then .all y body
      else .all y (substF body x s)
  | .exi y body =>
      if x == y then .exi y body
      else .exi y (substF body x s)

def is_free_in (x : String) (A : Formula) : Bool :=
  match A with

  | .atom _ ts => (ts.flatMap freeVars).contains x
  | .imp f1 f2 => is_free_in x f1 || is_free_in x f2
  | .all y body => if x == y then false else is_free_in x body
  | .exi y body => if x == y then false else is_free_in x body

def is_free_for (s : Term) (x : String) (A : Formula) : Bool :=
  match A with

  | .atom _ _ => true
  | .imp f1 f2 => is_free_for s x f1 && is_free_for s x f2
  | .all y body =>
      if x == y then true
      else if (freeVars s).contains y then false
      else is_free_for s x body
  | .exi y body =>
      if x == y then true
      else if (freeVars s).contains y then false
      else is_free_for s x body

axiom is_provable : Formula → Prop

-- Axioms

axiom forall_elim (x : String) (A : Formula) (t : Term) :
  (is_free_for t x A = true) → is_provable (.all x A) → is_provable (substF A x t)

axiom exists_intro (x : String) (A : Formula) (t: Term) :
  (is_free_for t x A = true) → is_provable (substF A x t) → is_provable (.exi x A)

-- Rules of Deduction

axiom forall_intro_imp {A B : Formula} {x} (h: is_provable (.imp A B)) (h': is_free_in x A = false):
  is_provable (.imp A (.all x B))

axiom exists_elim_imp {A B : Formula} {x} (h: is_provable (.imp A B)) (h': is_free_in x B = false):
  is_provable (.imp (.exi x A) B)

axiom modus_ponens {A B : Formula} (h: is_provable (.imp A B)) (h': is_provable A) : is_provable B

-- Theorems

end FirstOrder
