From Stdlib Require Import String Bool.
From Stdlib Require Export NArith Arith.
From Stdlib Require Import List.
Require Import Valuation.


Inductive BinopName :=
| LogAnd 
| Eq 
| ShiftLeft 
| ShiftRight 
| Times 
| Divide 
| Plus 
| Minus 
| Modulo.

Inductive expr :=
| nConst : nat -> expr
| bConst : bool -> expr
| Var : string -> expr
| Binop : BinopName -> expr -> expr -> expr.

Coercion nConst : nat >-> expr.
Coercion bConst : bool >-> expr.
Coercion Var : string >-> expr.

Inductive value := Nat (n : nat) | Bool (b : bool).


Definition interp_binop (b: BinopName) (v1 v2: value) : option value :=
  match b, v1, v2 with
    | LogAnd, Nat n1, Nat n2 => Some (Nat (Nat.land n1 n2))
    | Eq, Nat n1, Nat n2 => Some (Bool (if (n1 =? n2)%nat then true else false))
    | Eq, Bool b1, Bool b2 => Some (Bool (if Bool.eqb b1 b2 then true else false))
    | Plus, Nat n1, Nat n2 => Some (Nat (n1 + n2))
    | Minus, Nat n1, Nat n2 => Some (Nat (n1 - n2))
    | Times, Nat n1, Nat n2 => Some (Nat (n1 * n2))
    | Divide, Nat n1, Nat n2 => Some (Nat (n1 / n2))
    | ShiftLeft, Nat n1, Nat n2 => Some (Nat (Nat.shiftl n1 n2))
    | ShiftRight, Nat n1, Nat n2 => Some (Nat (Nat.shiftr n1 n2))
    | Modulo, Nat n1, Nat n2 => Some (Nat (Nat.modulo n1 n2))
    | _, _, _ => None
  end.

Inductive stmt :=
| pass : stmt
| varDecl : string -> expr -> stmt (*Var name, value*)
| assign : string -> expr -> stmt (*Var name, value*)
| ifThenElse : expr -> stmt -> stmt -> stmt (*Condition, then, else*)
| whileLoop : expr -> stmt -> stmt (*Condition, body*)
| await : string -> nat -> stmt (*Signal name, index of signal class*)
| callMethod : string -> list expr -> stmt (*Method name, arguments*)
| assignCallMethod : string -> string -> list expr -> stmt (*Return variable name, method name, arguments*)
| declCallMethod : string -> string -> list expr -> stmt (*Return variable name, method name, arguments*)
| bind : string -> string -> nat -> stmt (*Method name, signal name, index of signal class*)
| emitSignal : string -> list expr -> stmt (*Signal name, args*)
| sequence : stmt -> stmt -> stmt (*s1; s2*)
.

Declare Custom Entry gds.
Declare Scope gds_scope.
Delimit Scope gds_scope with gds.

Notation "<{ e }>" := e (e custom gds at level 99) : gds_scope.
Notation "( x )" := x (in custom gds, x at level 99) : gds_scope.
Notation "x" := x (in custom gds at level 0, x constr at level 0) : gds_scope.

Notation "x & y"   := (Binop LogAnd x y)     (in custom gds at level 80, right associativity) : gds_scope.
Notation "x == y"  := (Binop Eq x y)         (in custom gds at level 70, no associativity) : gds_scope.
Notation "x << y"  := (Binop ShiftLeft x y)  (in custom gds at level 60, left associativity) : gds_scope.
Notation "x >> y"  := (Binop ShiftRight x y) (in custom gds at level 60, left associativity) : gds_scope.
Notation "x + y"   := (Binop Plus x y)       (in custom gds at level 50, left associativity) : gds_scope.
Notation "x - y"   := (Binop Minus x y)      (in custom gds at level 50, left associativity) : gds_scope.
Notation "x * y"   := (Binop Times x y)      (in custom gds at level 40, left associativity) : gds_scope.
Notation "x / y"   := (Binop Divide x y)     (in custom gds at level 40, left associativity) : gds_scope.
Notation "x 'mod' y" := (Binop Modulo x y)   (in custom gds at level 40, left associativity) : gds_scope.

Notation "'pass'" := pass (in custom gds at level 0) : gds_scope.
Notation "'var' x ':=' e" := (varDecl x e)
  (in custom gds at level 0, x constr at level 0, e at level 85, no associativity) : gds_scope.
Notation "x ':=' e" := (assign x e)
  (in custom gds at level 0, x constr at level 0, e at level 85, no associativity) : gds_scope.
Notation "'if' c 'then' s1 'else' s2 'end'" := (ifThenElse c s1 s2)
  (in custom gds at level 89, c at level 99, s1 at level 99, s2 at level 99) : gds_scope.
Notation "'while' c 'do' s 'end'" := (whileLoop c s)
  (in custom gds at level 89, c at level 99, s at level 99) : gds_scope.
Notation "'await' sig 'on' n" := (await sig n)
  (in custom gds at level 0, sig constr at level 0, n constr at level 0) : gds_scope.
Notation "'bind' m 'to' sig 'on' n" := (bind m sig n)
  (in custom gds at level 0, m constr at level 0, sig constr at level 0, n constr at level 0) : gds_scope.

Notation "m ()" := (callMethod m (@nil expr))
  (in custom gds at level 0, m constr at level 0) : gds_scope.
Notation "m ( a , .. , b )" := (callMethod m (@cons expr a .. (@cons expr b nil) ..))
  (in custom gds at level 0, m constr at level 0, a at level 85, b at level 85) : gds_scope.
Notation "x '<-' m ()" := (assignCallMethod x m (@nil expr))
  (in custom gds at level 0, x constr at level 0, m constr at level 0) : gds_scope.
Notation "x '<-' m ( a , .. , b )" := (assignCallMethod x m (@cons expr a .. (@cons expr b nil) ..))
  (in custom gds at level 0, x constr at level 0, m constr at level 0, a at level 85, b at level 85) : gds_scope.
Notation "'var' x '<-' m ()" := (declCallMethod x m (@nil expr))
  (in custom gds at level 0, x constr at level 0, m constr at level 0) : gds_scope.
Notation "'var' x '<-' m ( a , .. , b )" := (declCallMethod x m (@cons expr a .. (@cons expr b nil) ..))
  (in custom gds at level 0, x constr at level 0, m constr at level 0, a at level 85, b at level 85) : gds_scope.
Notation "'emit' sig ()" := (emitSignal sig (@nil expr))
  (in custom gds at level 0, sig constr at level 0) : gds_scope.
Notation "'emit' sig ( a , .. , b )" := (emitSignal sig (@cons expr a .. (@cons expr b nil) ..))
  (in custom gds at level 0, sig constr at level 0, a at level 85, b at level 85) : gds_scope.

Notation "s1 ; s2" := (sequence s1 s2) (in custom gds at level 90, right associativity) : gds_scope.

Definition valuation := partial_map value.

(*
    What should a class state contain ? 
    the global store = valuation 
    The method store = map from string to (list string, option string, statement)
    The signal store = map from string to list string 
    The lists of waiting bodies per signal = map from string to list of (statement, valuation) 
    The lists of signal bindings  = map from string to list of string 

*)
Record class_state := {
    global_store: valuation; (*Store for variables*)
    method_store: partial_map ((list string) * option string * stmt); (*Store for methods, with parameter names, optional return variable name, and body*)
    signal_store: partial_map (list string); (*Store for signals, with parameter names *)
    waiting_bodies: partial_map (list (stmt * valuation)); (*Store for waiting bodies with their associated local valuations *)
    signal_bindings: partial_map (list string) (*Store for signal bindings from signal name to list of bound method names*)
    }.

Record total_state := {
    current_class: nat; (*Index of the current class*)
    class_states: list class_state (*List of all class states*)
    }.
