From Stdlib Require Import String Bool.
From Stdlib Require Export NArith Arith.
From Stdlib Require Import List.
Import ListNotations.
Require Import Valuation.
Open Scope list_scope. (* Valuation opens string_scope, whose ++ would shadow the list one *)

(* Types *)
Inductive typ := TNat | TBool.

(* rho in type PDF = return variable name and its type *)
Definition meth_ret := option (string * typ).

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

Definition value_to_option (v : value) : option value := Some v.
Coercion value_to_option : value >-> option.
(*NB: J'ai ajouté ça pour qu'on puisse update des valuations sans donner des options, pas sur que ce soit la meilleure idée, à voir*)


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

Definition valuation := partial_map value.

(* Where the result of a method call goes once the callee returns *)
Inductive ret_target :=
| ToAssign (x : string) (* x = f(...)     *)
| ToDecl (x : string).  (* var x = f(...) *)

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
(* Internal statements: never written in source programs, only produced by the semantics *)
| endScope : list string -> stmt (*End of an if/while block: removes the locals the block declared*)
| frame : nat -> valuation -> stmt -> stmt (*Class index, local store, code: runs in the context of that class (method body, woken body, ready, process)*)
| retFrame : ret_target -> string -> valuation -> stmt -> stmt (*Target, return variable name, local store, body*)
.

Inductive topLvl :=
| skip: topLvl
| classVarDecl: string -> expr -> topLvl (*Var name, value*)
| signalDecl : string -> list (string * typ) -> topLvl (*Signal name, typed argument names*)
| methodDecl : string -> list (string * typ) -> meth_ret -> stmt -> topLvl (*Method name, typed arg names, optional typed return var, body*)
| readyDecl : stmt -> topLvl (*Body*)
| processDecl : stmt -> topLvl (*Body*)
| sequenceTop : topLvl -> topLvl -> topLvl (*t1; t2*) 
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

(* Top-level declarations: separate entry, so that "var x := e" and ";"
   do not clash with their statement counterparts *)
Declare Custom Entry gds_top.


Notation "<[ t ]>" := t (t custom gds_top at level 99) : gds_scope.
Notation "( t )" := t (in custom gds_top, t at level 99) : gds_scope.
Notation "t" := t (in custom gds_top at level 0, t constr at level 0) : gds_scope.
 
Notation "'skip'" := skip (in custom gds_top at level 0) : gds_scope.
Notation "'var' x ':=' e" := (classVarDecl x e)
  (in custom gds_top at level 0, x constr at level 0, e custom gds at level 85, no associativity) : gds_scope.
 
Notation "'signal' sig ()" := (signalDecl sig (@nil (string * typ)))
  (in custom gds_top at level 0, sig constr at level 0) : gds_scope.
Notation "'signal' sig ( a , .. , b )" := (signalDecl sig (@cons (string * typ)a .. (@cons (string * typ)b nil) ..))
  (in custom gds_top at level 0, sig constr at level 0, a constr at level 0, b constr at level 0) : gds_scope.
 
Notation "'func' m () 'do' s 'end'" := (methodDecl m (@nil (string * typ)) None s)
  (in custom gds_top at level 0, m constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m ( a , .. , b ) 'do' s 'end'" := (methodDecl m (@cons (string * typ)a .. (@cons (string * typ)b nil) ..) None s)
  (in custom gds_top at level 0, m constr at level 0, a constr at level 0, b constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m () '->' r 'do' s 'end'" := (methodDecl m (@nil (string * typ)) (Some r) s)
  (in custom gds_top at level 0, m constr at level 0, r constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m ( a , .. , b ) '->' r 'do' s 'end'" := (methodDecl m (@cons (string * typ)a .. (@cons (string * typ)b nil) ..) (Some r) s)
  (in custom gds_top at level 0, m constr at level 0, a constr at level 0, b constr at level 0, r constr at level 0, s custom gds at level 99) : gds_scope.
 
Notation "'ready' 'do' s 'end'" := (readyDecl s)
  (in custom gds_top at level 0, s custom gds at level 99) : gds_scope.
Notation "'process' 'do' s 'end'" := (processDecl s)
  (in custom gds_top at level 0, s custom gds at level 99) : gds_scope.
 
Notation "t1 ; t2" := (sequenceTop t1 t2) (in custom gds_top at level 90, right associativity) : gds_scope.



(*
    What should a class state contain ? 
    the global store = valuation 
    The method store = map from string to (list string, option string, statement)
    The signal store = map from string to list string 
    The lists of waiting bodies per signal = map from string to list of (class index, statement, valuation) 
    The lists of signal bindings  = map from string to list of (class index, method name) 
    (the class index says in which class the body / method runs)

*)
Record class_state := {
    global_store: valuation; (*Store for variables*)
    method_store: partial_map ((list string) * option string * stmt); (*Store for methods, with parameter names, optional return variable name, and body*)
    signal_store: partial_map (list string); (*Store for signals, with parameter names *)
    waiting_bodies: partial_map (list (nat * stmt * valuation)); (*Store for waiting bodies, with the index of their class and their local valuation *)
    signal_bindings: partial_map (list (nat * string)) (*Store for signal bindings from signal name to list of bound methods (class index, method name)*)
    }.

Definition empty_cs: class_state := {|
    global_store := empty;
    method_store := empty;
    signal_store := empty;
    waiting_bodies := empty;
    signal_bindings := empty
|}.


(*Helper functions for updating class state*) 
(* -----------HELPER------------------*)

Definition update_gs (cs: class_state) (x: string) (v: value) : class_state :=
  {| global_store := (global_store cs)[x := v];
     method_store := method_store cs;
     signal_store := signal_store cs;
     waiting_bodies := waiting_bodies cs;
     signal_bindings := signal_bindings cs |}.

Definition update_method_store (cs: class_state) (name: string) (params: list string) (ret: option string) (body: stmt) : class_state :=
  {| global_store := global_store cs;
     method_store := (method_store cs)[name := Some (params, ret, body)];
     signal_store := signal_store cs;
     waiting_bodies := waiting_bodies cs;
     signal_bindings := signal_bindings cs |}.

Definition update_signal_store (cs: class_state) (name: string) (params: list string) : class_state :=
  {| global_store := global_store cs;
     method_store := method_store cs;
     signal_store := (signal_store cs)[name := Some params];
     waiting_bodies := waiting_bodies cs;
     signal_bindings := signal_bindings cs |}.


Definition update_waiting_bodies
    (cs: class_state) (name: string) (body: nat * stmt * valuation): class_state :=
  let bodies := match waiting_bodies cs name with Some l => l | None => [] end in
  {| global_store := global_store cs;
     method_store := method_store cs;
     signal_store := signal_store cs;
     waiting_bodies := (waiting_bodies cs)[name := Some (bodies ++ [body])];
     signal_bindings := signal_bindings cs |}.

Definition update_signal_bindings
    (cs: class_state) (name: string) (method_name: nat * string): class_state :=
  let methods := match signal_bindings cs name with Some l => l | None => [] end in
  {| global_store := global_store cs;
     method_store := method_store cs;
     signal_store := signal_store cs;
     waiting_bodies := waiting_bodies cs;
     signal_bindings := (signal_bindings cs)[name := Some (methods ++ [method_name])] |}.

(* Empties the list of bodies waiting for a signal (done at the start of an emission) *)
Definition clear_waiting_bodies (cs: class_state) (name: string) : class_state :=
  {| global_store := global_store cs;
     method_store := method_store cs;
     signal_store := signal_store cs;
     waiting_bodies := (waiting_bodies cs)[name := Some nil];
     signal_bindings := signal_bindings cs |}.



(* The states of all classes of the program; a class is identified by its
   index in this list *)
Definition world := list class_state.

(* Replaces the n-th element of a list (unchanged if n is out of range) *)
Fixpoint replace_nth {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: l', 0 => x :: l'
  | y :: l', S n' => y :: replace_nth l' n' x
  end.


(*Evaluate an expression to a value*)
Inductive eval_expr : class_state -> valuation -> expr -> value -> Prop :=
  | NatConst : forall cs val n, 
      eval_expr cs val (nConst n) (Nat n)
  | BoolConst : forall cs val b, 
      eval_expr cs val (bConst b) (Bool b)
  | VarLookupLocal : forall cs val x v,
      val x = Some v ->
      eval_expr cs val (Var x) v
  | VarLookupGlobal : forall cs val x v,
      val x = None -> 
      global_store cs x = Some v ->
      eval_expr cs val (Var x) v
  | BinopEval : forall cs val b e1 e2 v1 v2 v,
      eval_expr cs val e1 v1 ->
      eval_expr cs val e2 v2 ->
      interp_binop b v1 v2 = Some v ->
      eval_expr cs val (Binop b e1 e2) v.


(*  Auxiliary functions for the small-step semantics  *)
(*-----------------------------------------------------*)

Definition value_to_expr (v : value) : expr :=
  match v with
  | Nat n => nConst n
  | Bool b => bConst b
  end.

(* Locals declared directly in a block. Nested if/while blocks are not
   included: they remove their own locals when they end. *)
Fixpoint decls (s : stmt) : list string :=
  match s with
  | varDecl x _ => [x]
  | declCallMethod x _ _ => [x]
  | sequence s1 s2 => decls s1 ++ decls s2
  | _ => []
  end.

Definition remove_vars (xs : list string) (val : valuation) : valuation :=
  fun y => if existsb (String.eqb y) xs then None else val y.

(* If the code of a frame starts with an await: the signal, the class index,
   and the continuation (everything that follows the await in the frame) *)
Fixpoint head_await (s : stmt) : option (string * nat * stmt) :=
  match s with
  | await sig n => Some (sig, n, pass)
  | sequence s1 s2 =>
      match head_await s1 with
      | Some (sig, n, k) => Some (sig, n, sequence k s2)
      | None => None
      end
  | _ => None
  end.

(* Local store of a method call: parameters mapped to argument values.
   None if the number of arguments does not match. *)
Fixpoint bind_args (params : list string) (vs : list value) : option valuation :=
  match params, vs with
  | [], [] => Some empty
  | p :: ps, v :: vs' =>
      match bind_args ps vs' with
      | Some val => Some (val [p := v])
      | None => None
      end
  | _, _ => None
  end.

Definition list_or_nil {A} (o : option (list A)) : list A :=
  match o with Some l => l | None => [] end.

(* One frame per method bound to a signal, in binding order, each in the
   context of the class the method belongs to.
   None if a class or a method does not exist, or if the arity is wrong. *)
Fixpoint method_frames (w : world) (ms : list (nat * string)) (vs : list value) : option stmt :=
  match ms with
  | [] => Some pass
  | (cm, m) :: ms' =>
      match nth_error w cm with
      | None => None
      | Some csm =>
          match method_store csm m, method_frames w ms' vs with
          | Some (params, _, body), Some rest =>
              match bind_args params vs with
              | Some valf => Some (sequence (frame cm valf body) rest)
              | None => None
              end
          | _, _ => None
          end
      end
  end.

(* One frame per waiting body, in FIFO order, each in the context of its
   class and with its saved local store *)
Definition waiting_frames (ws : list (nat * stmt * valuation)) : stmt :=
  fold_right (fun '(ck, k, valk) acc => sequence (frame ck valk k) acc) pass ws.

(* What the caller executes once the callee has returned value v *)
Definition ret_stmt (t : ret_target) (v : value) : stmt :=
  match t with
  | ToAssign x => assign x (value_to_expr v)
  | ToDecl x => varDecl x (value_to_expr v)
  end.


(*  Small-step semantics of statements                                
    step w c val s w' val' s'  :  <w, c, val, s> --> <w', val', s'>   
    w is the state of all classes, c the index of the class whose      
    context the code runs in (globals, methods, signals), val the      
    local store of the enclosing frame.                               
    A statement is finished when it is pass (pass never steps).     *)
 (*-------------------------STEP RELATION-----------------------------------*)

Inductive step : world -> nat -> valuation -> stmt -> world -> valuation -> stmt -> Prop :=
(* Variables *)
| S_VarDecl : forall w c cs val x e v,
    nth_error w c = Some cs ->
    val x = None ->
    eval_expr cs val e v ->
    step w c val (varDecl x e) w (val [x := v]) pass
| S_AssignL : forall w c cs val x e v v',
    nth_error w c = Some cs ->
    val x = Some v' ->
    eval_expr cs val e v ->
    step w c val (assign x e) w (val [x := v]) pass
| S_AssignG : forall w c cs val x e v v',
    nth_error w c = Some cs ->
    val x = None ->
    global_store cs x = Some v' ->
    eval_expr cs val e v ->
    step w c val (assign x e) (replace_nth w c (update_gs cs x v)) val pass

(* Sequence *)
| S_SeqPass : forall w c val s2,
    step w c val (sequence pass s2) w val s2
| S_Seq : forall w c val s1 s1' s2 w' val',
    step w c val s1 w' val' s1' ->
    step w c val (sequence s1 s2) w' val' (sequence s1' s2)

(* Blocks: each branch / loop body is followed by an endScope that removes its locals *)
| S_IfT : forall w c cs val e s1 s2,
    nth_error w c = Some cs ->
    eval_expr cs val e (Bool true) ->
    step w c val (ifThenElse e s1 s2) w val (sequence s1 (endScope (decls s1)))
| S_IfF : forall w c cs val e s1 s2,
    nth_error w c = Some cs ->
    eval_expr cs val e (Bool false) ->
    step w c val (ifThenElse e s1 s2) w val (sequence s2 (endScope (decls s2)))
| S_WhileT : forall w c cs val e s,
    nth_error w c = Some cs ->
    eval_expr cs val e (Bool true) ->
    step w c val (whileLoop e s) w val
         (sequence (sequence s (endScope (decls s))) (whileLoop e s))
| S_WhileF : forall w c cs val e s,
    nth_error w c = Some cs ->
    eval_expr cs val e (Bool false) ->
    step w c val (whileLoop e s) w val pass
| S_EndScope : forall w c val xs,
    step w c val (endScope xs) w (remove_vars xs val) pass

(* Method calls (always to a method of the current class): the body runs in
   a frame of the current class with its own local store *)
| S_Call : forall w c cs val f args vs params ret body valf,
    nth_error w c = Some cs ->
    method_store cs f = Some (params, ret, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step w c val (callMethod f args) w val (frame c valf body)
| S_AssignCall : forall w c cs val x f args vs params r body valf,
    nth_error w c = Some cs ->
    method_store cs f = Some (params, Some r, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step w c val (assignCallMethod x f args) w val (retFrame (ToAssign x) r valf body)
| S_DeclCall : forall w c cs val x f args vs params r body valf,
    nth_error w c = Some cs ->
    method_store cs f = Some (params, Some r, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step w c val (declCallMethod x f args) w val (retFrame (ToDecl x) r valf body)

(* Frames: context switch. The inner code steps in the context of the frame's
   class cf, with the frame's local store; the outer context is untouched. *)
| S_Frame : forall w c val cf valf s w' valf' s',
    step w cf valf s w' valf' s' ->
    step w c val (frame cf valf s) w' val (frame cf valf' s')
| S_FrameDone : forall w c val cf valf,
    step w c val (frame cf valf pass) w val pass
(* await at the head of a frame of class cf, on a signal of class n: the rest
   of the frame is stored in the waiting list of class n, tagged with cf (it
   will run in the context of cf when woken), and the frame ends. *)
| S_FrameAwait : forall w c val cf valf s sig n k csn,
    head_await s = Some (sig, n, k) ->
    nth_error w n = Some csn ->
    step w c val (frame cf valf s)
         (replace_nth w n (update_waiting_bodies csn sig (cf, k, valf))) val pass

(* Frames of calls with a return value (same class as the caller). No await
   rule: a method with a return value that awaits is stuck (to be ruled out
   by the type system). *)
| S_RetFrame : forall w c val t r valf s w' valf' s',
    step w c valf s w' valf' s' ->
    step w c val (retFrame t r valf s) w' val (retFrame t r valf' s')
| S_RetDone : forall w c val t r valf v,
    valf r = Some v ->
    step w c val (retFrame t r valf pass) w val (ret_stmt t v)

(* Signals *)
(* bind f sig n: method f of the current class c is bound to signal sig of class n *)
| S_Bind : forall w c cs val f sig n csn m params,
    nth_error w c = Some cs ->
    nth_error w n = Some csn ->
    method_store cs f = Some m ->
    signal_store csn sig = Some params ->
    step w c val (bind f sig n)
         (replace_nth w n (update_signal_bindings csn sig (c, f))) val pass
(* emit: a class only emits its own signals. The waiting list is emptied
   first (bodies that await again during the emission wait for the next one),
   then the bound methods run, then the bodies that were waiting, each in a
   frame of its own class *)
| S_Emit : forall w c cs val sig args vs params calls,
    nth_error w c = Some cs ->
    signal_store cs sig = Some params ->
    Forall2 (eval_expr cs val) args vs ->
    length params = length vs ->
    method_frames w (list_or_nil (signal_bindings cs sig)) vs = Some calls ->
    step w c val (emitSignal sig args)
         (replace_nth w c (clear_waiting_bodies cs sig)) val
         (sequence calls (waiting_frames (list_or_nil (waiting_bodies cs sig)))).


(* Reflexive-transitive closure: <w, c, val, s> -->* <w', val', s'> *)
Inductive multi : world -> nat -> valuation -> stmt -> world -> valuation -> stmt -> Prop :=
| M_Refl : forall w c val s,
    multi w c val s w val s
| M_Step : forall w c val s w' val' s' w'' val'' s'',
    step w c val s w' val' s' ->
    multi w' c val' s' w'' val'' s'' ->
    multi w c val s w'' val'' s''.


(* Initialization of a class (big-step: declarations always end)   
  init cs t cs' ready process                                      
  Declares variables, signals and methods, and extracts the bodies
  of ready and process without running them. *)
  (*-----------------------------------------------------------*)

(* Combines what two parts of a class declare for ready (or process):
   None if both declare one *)
Definition merge_opt (o1 o2 : option stmt) : option (option stmt) :=
  match o1, o2 with
  | Some _, Some _ => None
  | Some s, None | None, Some s => Some (Some s)
  | None, None => Some None
  end.

Inductive init : class_state -> topLvl -> class_state -> option stmt -> option stmt -> Prop :=
| I_Skip : forall cs,
    init cs skip cs None None
| I_ClassVarDecl : forall cs x e v,
    global_store cs x = None ->
    eval_expr cs empty e v ->
    init cs (classVarDecl x e) (update_gs cs x v) None None
| I_SignalDecl : forall cs sig params,
    signal_store cs sig = None ->
    init cs (signalDecl sig params) (update_signal_store cs sig params) None None
| I_MethodDecl : forall cs f params ret body,
    method_store cs f = None ->
    init cs (methodDecl f params ret body) (update_method_store cs f params ret body) None None
| I_ReadyDecl : forall cs s,
    init cs (readyDecl s) cs (Some s) None
| I_ProcessDecl : forall cs s,
    init cs (processDecl s) cs None (Some s)
| I_Seq : forall cs t1 t2 cs1 cs2 r1 p1 r2 p2 r p,
    init cs t1 cs1 r1 p1 ->
    init cs1 t2 cs2 r2 p2 ->
    merge_opt r1 r2 = Some r ->
    merge_opt p1 p2 = Some p ->
    init cs (sequenceTop t1 t2) cs2 r p.


(* Initialization of all classes, in order. Each class is initialized
   independently, from an empty state. *)
Inductive init_all : list topLvl -> world -> list (option stmt) -> list (option stmt) -> Prop :=
| IA_Nil :
    init_all nil nil nil nil
| IA_Cons : forall t ts cs w r rs p ps,
    init empty_cs t cs r p ->
    init_all ts w rs ps ->
    init_all (t :: ts) (cs :: w) (r :: rs) (p :: ps).


(*  Execution of a program (small-step)
    A configuration is the state of all classes, the code currently running,
    and the number of process frames still to run. The process bodies never
    change, so they are a parameter of the relation. *)
  (*------------------------PROGRAM EVALUATION------------------------------------------------*)
Record config := {
    c_world : world;   (*State of all classes*)
    c_code : stmt;     (*Code currently running (pass when idle)*)
    c_frames : nat     (*Number of process frames still to run*)
    }.

Definition body_or_pass (o : option stmt) : stmt :=
  match o with Some s => s | None => pass end.

(* frame i empty b_i ; frame (i+1) empty b_(i+1) ; ... ; pass
   Used for all the readys, then for all the processes of one frame,
   in the order of the classes. A class without ready / process gets an
   empty frame. *)
Fixpoint class_frames (i : nat) (bodies : list (option stmt)) : stmt :=
  match bodies with
  | [] => pass
  | b :: bs => sequence (frame i empty (body_or_pass b)) (class_frames (S i) bs)
  end.

Inductive pstep (processes : list (option stmt)) : config -> config -> Prop :=
(* The running code takes one step. All top-level code runs inside frames,
   which set their own class, so the outer class index (0) and the outer
   local store (empty) are never used. *)
| P_Step : forall w s w' s' n,
    step w 0 empty s w' empty s' ->
    pstep processes {| c_world := w; c_code := s; c_frames := n |}
                    {| c_world := w'; c_code := s'; c_frames := n |}
(* The current code is finished: start the next frame, which runs the
   process of each class in order *)
| P_NextFrame : forall w n,
    pstep processes {| c_world := w; c_code := pass; c_frames := S n |}
                    {| c_world := w; c_code := class_frames 0 processes; c_frames := n |}.

Inductive pmulti (processes : list (option stmt)) : config -> config -> Prop :=
| PM_Refl : forall c, pmulti processes c c
| PM_Step : forall c c' c'',
    pstep processes c c' -> pmulti processes c' c'' -> pmulti processes c c''.

(* Whole program: all initializations, then all readys, then n frames, each
   running all the processes, always in the order of the classes.
   The program has finished when its code is pass and no frame is left. *)
Inductive eval_program : nat -> list topLvl -> world -> Prop :=
| Eval : forall n ts w w' readys processes,
    init_all ts w readys processes ->
    pmulti processes {| c_world := w; c_code := class_frames 0 readys; c_frames := n |}
                     {| c_world := w'; c_code := pass; c_frames := 0 |} ->
    eval_program n ts w'.
