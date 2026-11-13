From Stdlib Require Import String Bool.
From Stdlib Require Export NArith Arith.
From Stdlib Require Import List.
Import ListNotations.
Require Import Valuation.
Open Scope list_scope. (* Valuation opens string_scope, whose ++ would shadow the list one *)


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
| frame : valuation -> stmt -> stmt (*Code running with its own local store (method body, woken body)*)
| retFrame : ret_target -> string -> valuation -> stmt -> stmt (*Target, return variable name, local store, body*)
.

Inductive topLvl :=
| skip: topLvl
| classVarDecl: string -> expr -> topLvl (*Var name, value*)
| signalDecl : string -> list string -> topLvl (*Signal name, List of argument names*)
| methodDecl : string -> list string -> option string -> stmt -> topLvl (*Method name, arg names, optional return var name, body*)
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
 
Notation "'signal' sig ()" := (signalDecl sig (@nil string))
  (in custom gds_top at level 0, sig constr at level 0) : gds_scope.
Notation "'signal' sig ( a , .. , b )" := (signalDecl sig (@cons string a .. (@cons string b nil) ..))
  (in custom gds_top at level 0, sig constr at level 0, a constr at level 0, b constr at level 0) : gds_scope.
 
Notation "'func' m () 'do' s 'end'" := (methodDecl m (@nil string) None s)
  (in custom gds_top at level 0, m constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m ( a , .. , b ) 'do' s 'end'" := (methodDecl m (@cons string a .. (@cons string b nil) ..) None s)
  (in custom gds_top at level 0, m constr at level 0, a constr at level 0, b constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m () '->' r 'do' s 'end'" := (methodDecl m (@nil string) (Some r) s)
  (in custom gds_top at level 0, m constr at level 0, r constr at level 0, s custom gds at level 99) : gds_scope.
Notation "'func' m ( a , .. , b ) '->' r 'do' s 'end'" := (methodDecl m (@cons string a .. (@cons string b nil) ..) (Some r) s)
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

Definition empty_cs: class_state := {|
    global_store := empty;
    method_store := empty;
    signal_store := empty;
    waiting_bodies := empty;
    signal_bindings := empty
|}.


(*Helper functions for updating class state*)

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
    (cs: class_state) (name: string) (body: stmt * valuation): class_state :=
  let bodies := match waiting_bodies cs name with Some l => l | None => [] end in
  {| global_store := global_store cs;
     method_store := method_store cs;
     signal_store := signal_store cs;
     waiting_bodies := (waiting_bodies cs)[name := Some (bodies ++ [body])];
     signal_bindings := signal_bindings cs |}.

Definition update_signal_bindings
    (cs: class_state) (name: string) (method_name: string): class_state :=
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


Record total_state := {
    current_class: nat; (*Index of the current class*)
    class_states: list class_state (*List of all class states*)
    }.


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

(* One frame per method bound to a signal, in binding order.
   None if a method does not exist or has the wrong arity. *)
Fixpoint method_frames (cs : class_state) (ms : list string) (vs : list value) : option stmt :=
  match ms with
  | [] => Some pass
  | m :: ms' =>
      match method_store cs m, method_frames cs ms' vs with
      | Some (params, _, body), Some rest =>
          match bind_args params vs with
          | Some valf => Some (sequence (frame valf body) rest)
          | None => None
          end
      | _, _ => None
      end
  end.

(* One frame per waiting body, in FIFO order, each with its saved local store *)
Definition waiting_frames (ws : list (stmt * valuation)) : stmt :=
  fold_right (fun '(k, valk) acc => sequence (frame valk k) acc) pass ws.

(* What the caller executes once the callee has returned value v *)
Definition ret_stmt (t : ret_target) (v : value) : stmt :=
  match t with
  | ToAssign x => assign x (value_to_expr v)
  | ToDecl x => varDecl x (value_to_expr v)
  end.


(* ================================================================== *)
(*  Small-step semantics of statements                                *)
(*  step cs val s cs' val' s'  :  <cs, val, s> --> <cs', val', s'>    *)
(*  A statement is finished when it is pass (pass never steps).       *)
(* ================================================================== *)

Inductive step : class_state -> valuation -> stmt -> class_state -> valuation -> stmt -> Prop :=
(* Variables *)
| S_VarDecl : forall cs val x e v,
    val x = None ->
    eval_expr cs val e v ->
    step cs val (varDecl x e) cs (val [x := v]) pass
| S_AssignL : forall cs val x e v v',
    val x = Some v' ->
    eval_expr cs val e v ->
    step cs val (assign x e) cs (val [x := v]) pass
| S_AssignG : forall cs val x e v v',
    val x = None ->
    global_store cs x = Some v' ->
    eval_expr cs val e v ->
    step cs val (assign x e) (update_gs cs x v) val pass

(* Sequence *)
| S_SeqPass : forall cs val s2,
    step cs val (sequence pass s2) cs val s2
| S_Seq : forall cs val s1 s1' s2 cs' val',
    step cs val s1 cs' val' s1' ->
    step cs val (sequence s1 s2) cs' val' (sequence s1' s2)

(* Blocks: each branch / loop body is followed by an endScope that removes its locals *)
| S_IfT : forall cs val e s1 s2,
    eval_expr cs val e (Bool true) ->
    step cs val (ifThenElse e s1 s2) cs val (sequence s1 (endScope (decls s1)))
| S_IfF : forall cs val e s1 s2,
    eval_expr cs val e (Bool false) ->
    step cs val (ifThenElse e s1 s2) cs val (sequence s2 (endScope (decls s2)))
| S_WhileT : forall cs val e s,
    eval_expr cs val e (Bool true) ->
    step cs val (whileLoop e s) cs val
         (sequence (sequence s (endScope (decls s))) (whileLoop e s))
| S_WhileF : forall cs val e s,
    eval_expr cs val e (Bool false) ->
    step cs val (whileLoop e s) cs val pass
| S_EndScope : forall cs val xs,
    step cs val (endScope xs) cs (remove_vars xs val) pass

(* Method calls: the body runs in a frame with its own local store *)
| S_Call : forall cs val f args vs params ret body valf,
    method_store cs f = Some (params, ret, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step cs val (callMethod f args) cs val (frame valf body)
| S_AssignCall : forall cs val x f args vs params r body valf,
    method_store cs f = Some (params, Some r, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step cs val (assignCallMethod x f args) cs val (retFrame (ToAssign x) r valf body)
| S_DeclCall : forall cs val x f args vs params r body valf,
    method_store cs f = Some (params, Some r, body) ->
    Forall2 (eval_expr cs val) args vs ->
    bind_args params vs = Some valf ->
    step cs val (declCallMethod x f args) cs val (retFrame (ToDecl x) r valf body)

(* Frames: the inner code steps with the frame's local store; the outer one is untouched *)
| S_Frame : forall cs val valf s cs' valf' s',
    step cs valf s cs' valf' s' ->
    step cs val (frame valf s) cs' val (frame valf' s')
| S_FrameDone : forall cs val valf,
    step cs val (frame valf pass) cs val pass
(* await at the head of a frame: the rest of the frame and its local store are
   stored as a waiting body, and the frame ends (the caller continues).
   Only signals of the current class (index 0) for now. *)
| S_FrameAwait : forall cs val valf s sig k,
    head_await s = Some (sig, 0, k) ->
    step cs val (frame valf s) (update_waiting_bodies cs sig (k, valf)) val pass

(* Frames of calls with a return value. No await rule: a method with a return
   value that awaits is stuck (to be ruled out by the type system). *)
| S_RetFrame : forall cs val t r valf s cs' valf' s',
    step cs valf s cs' valf' s' ->
    step cs val (retFrame t r valf s) cs' val (retFrame t r valf' s')
| S_RetDone : forall cs val t r valf v,
    valf r = Some v ->
    step cs val (retFrame t r valf pass) cs val (ret_stmt t v)

(* Signals *)
| S_Bind : forall cs val f sig m params,
    method_store cs f = Some m ->
    signal_store cs sig = Some params ->
    step cs val (bind f sig 0) (update_signal_bindings cs sig f) val pass
(* emit: the waiting list is emptied first (bodies that await again during
   the emission wait for the next one), then the bound methods run, then the
   bodies that were waiting, each in its own frame *)
| S_Emit : forall cs val sig args vs params calls,
    signal_store cs sig = Some params ->
    Forall2 (eval_expr cs val) args vs ->
    length params = length vs ->
    method_frames cs (list_or_nil (signal_bindings cs sig)) vs = Some calls ->
    step cs val (emitSignal sig args)
         (clear_waiting_bodies cs sig) val
         (sequence calls (waiting_frames (list_or_nil (waiting_bodies cs sig)))).


(* Reflexive-transitive closure: <cs, val, s> -->* <cs', val', s'> *)
Inductive multi : class_state -> valuation -> stmt -> class_state -> valuation -> stmt -> Prop :=
| M_Refl : forall cs val s,
    multi cs val s cs val s
| M_Step : forall cs val s cs' val' s' cs'' val'' s'',
    step cs val s cs' val' s' ->
    multi cs' val' s' cs'' val'' s'' ->
    multi cs val s cs'' val'' s''.


(* Initialization of a class (big-step: declarations always end)   
  init cs t cs' ready process                                      
  Declares variables, signals and methods, and extracts the bodies
  of ready and process without running them. *)

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


(*  Execution of a class (small-step)                                 
    A configuration is the class state, the code currently running,   
    and the number of process frames still to run. The process body   
    never changes, so it is a parameter of the relation. *)
Record config := {
    c_state : class_state; (*State of the class*)
    c_code : stmt;         (*Code currently running (pass when idle)*)
    c_frames : nat         (*Number of process frames still to run*)
    }.

Definition body_or_pass (o : option stmt) : stmt :=
  match o with Some s => s | None => pass end.

Inductive pstep (process : option stmt) : config -> config -> Prop :=
(* The running code takes one step. All top-level code runs inside a frame,
   so the outer local store stays empty. *)
| P_Step : forall cs s cs' s' n,
    step cs empty s cs' empty s' ->
    pstep process {| c_state := cs; c_code := s; c_frames := n |}
                  {| c_state := cs'; c_code := s'; c_frames := n |}
(* The current code is finished: start the next process frame
   (an empty frame if the class has no process) *)
| P_NextFrame : forall cs n,
    pstep process {| c_state := cs; c_code := pass; c_frames := S n |}
                  {| c_state := cs; c_code := frame empty (body_or_pass process); c_frames := n |}.

Inductive pmulti (process : option stmt) : config -> config -> Prop :=
| PM_Refl : forall c, pmulti process c c
| PM_Step : forall c c' c'',
    pstep process c c' -> pmulti process c' c'' -> pmulti process c c''.

(* Whole class: initialization, then ready, then n process frames.
   The class has finished when its code is pass and no frame is left. *)
Inductive eval_class : nat -> topLvl -> class_state -> Prop :=
| Eval : forall n t cs cs' ready process,
    init empty_cs t cs ready process ->
    pmulti process {| c_state := cs; c_code := frame empty (body_or_pass ready); c_frames := n |}
                   {| c_state := cs'; c_code := pass; c_frames := 0 |} ->
    eval_class n t cs'.