Require Import GDS_Inductive Valuation.
From Stdlib Require Import String.
From Stdlib Require Import String List.

(*Def stores*)
(* Γ *)
Definition local_c := partial_map typ.

(* Λ *)
Record global_c := {
    varsc_store: partial_map typ; (*Variables type*)
    methc_store: partial_map (list typ * meth_ret); (*Method type and return (meth_ret)*)
    sigc_store: partial_map (list typ); (*Signals types *)
}.

Definition empty_global_c: global_c := {|
    varsc_store := empty;
    methc_store := empty;
    sigc_store := empty;
|}.

Definition update_varsc_store (gc: global_c) (x: string) (t: typ) : global_c :=
  {| varsc_store := (varsc_store gc)[x := Some t];
     methc_store := methc_store gc;
     sigc_store := sigc_store gc; 
  |}.

Definition update_methc_store (gc: global_c) (name: string) (params: list typ) (ret: meth_ret) : global_c :=
  {| varsc_store := varsc_store gc;
     methc_store := (methc_store gc)[name := Some (params, ret)];
     sigc_store := sigc_store gc;
  |}.

Definition update_sigc_store (gc: global_c) (name: string) (params: list typ) : global_c :=
  {| varsc_store := varsc_store gc;
     methc_store := methc_store gc;
     sigc_store := (sigc_store gc)[name := Some params];
  |}.

(* Value typing *)
Inductive value_typing : value -> typ -> Prop:=
  |VNat: forall n, value_typing (Nat n) TNat
  |VBool: forall b, value_typing (Bool b) TBool.

Inductive optype: BinopName -> typ -> typ -> typ -> Prop :=
  | Op_LogAnd : optype LogAnd TNat TNat TNat
  | Op_EqNat: optype Eq TNat TNat TBool
  | Op_EqBool: optype Eq TBool TBool TBool
  | Op_ShiftLeft: optype ShiftLeft TNat TNat TNat
  | Op_ShiftRight: optype ShiftRight TNat TNat TNat 
  | Op_Times: optype Times TNat TNat TNat 
  | Op_Divide: optype Divide TNat TNat TNat 
  | Op_Plus: optype Plus TNat TNat TNat  
  | Op_Minus: optype Minus TNat TNat TNat  
  | Op_Modulo: optype Modulo TNat TNat TNat 
  .

(* Link optype and interp_binop *)
Lemma op_requirement :
  forall (op: BinopName) (t1 t2 t: typ) v1 v2,
  optype op t1 t2 t -> value_typing v1 t1 -> value_typing v2 t2 
  -> exists v, interp_binop op v1 v2 = Some v /\ value_typing v t
.
Proof.
  intros.
  inversion H; subst; inversion H0; inversion H1; subst.
  all: eexists; split; try reflexivity; try constructor.
Qed.

  
Inductive expr_typ: global_c -> local_c -> expr -> typ -> Prop :=
  |TNatRule: forall gc lc n, expr_typ gc lc (nConst n) TNat
  |TBoolRule: forall gc lc b, expr_typ gc lc (bConst b) TBool
  |TVarLRule: forall gc lc x t, lc x = Some t -> expr_typ gc lc (Var x) t
  |TVarGRule: forall gc lc x t, lc x = None -> varsc_store gc x = Some t
      -> expr_typ gc lc (Var x) t
  |TBinopRule: forall gc lc b e1 e2 t1 t2 t,
      expr_typ gc lc e1 t1 ->
      expr_typ gc lc e2 t2 ->
      optype b t1 t2 t ->
      expr_typ gc lc (Binop b e1 e2) t
.

(* Remove the variables x from a local context *)
Definition remove_varl (x : list string) (lc : local_c) : local_c :=
  fun y => if existsb (String.eqb y) x then None else lc y.

(* na(s): no await outside a nested frame / retFrame *)
Fixpoint na (s : stmt) : bool :=
  match s with
  | await _ _ => false
  | sequence s1 s2 => na s1 && na s2
  | ifThenElse _ s1 s2 => na s1 && na s2
  | whileLoop _ s1 => na s1
  | _ => true
  end.

(* Same domain, and every stored value has its declared type *)
Definition local_store_typ (val : valuation) (lc : local_c) : Prop :=
  (forall x, val x = None <-> lc x = None) /\
  (forall x v t, val x = Some v -> lc x = Some t -> value_typing v t).

(* Return target t can receive a value of type τ *)
Inductive ret_target_typ : global_c -> local_c -> ret_target -> typ -> local_c -> Prop :=
  | TG_ASSIGN_L : forall gc lc x t,
      lc x = Some t ->
      ret_target_typ gc lc (ToAssign x) t lc
  | TG_ASSIGN_G : forall gc lc x t,
      lc x = None ->
      varsc_store gc x = Some t ->
      ret_target_typ gc lc (ToAssign x) t lc
  | TG_DECL : forall gc lc x t,
      lc x = None ->
      ret_target_typ gc lc (ToDecl x) t (lc [x := Some t])
.

Inductive stmt_typ: global_c -> local_c -> stmt -> local_c -> Prop :=
  | T_PASS: forall gc lc,
      stmt_typ gc lc pass lc
  | T_VARDECL: forall gc lc x e t,
      lc x = None ->
      expr_typ gc lc e t ->
      stmt_typ gc lc (varDecl x e) (lc [x := Some t])
  | T_ASSIGN_L: forall gc lc x e t,
      lc x = Some t ->
      expr_typ gc lc e t ->
      stmt_typ gc lc (assign x e) lc
  | T_ASSIGN_G: forall gc lc x e t,
      lc x = None ->
      varsc_store gc x = Some t ->
      expr_typ gc lc e t ->
      stmt_typ gc lc (assign x e) lc
  | T_IF: forall gc lc e s1 s2 lc1 lc2,
      expr_typ gc lc e TBool ->
      stmt_typ gc lc s1 lc1 ->
      stmt_typ gc lc s2 lc2 ->
      stmt_typ gc lc (ifThenElse e s1 s2) lc
  | T_WHILE: forall gc lc e s lc',
      expr_typ gc lc e TBool ->
      stmt_typ gc lc s lc' ->
      stmt_typ gc lc (whileLoop e s) lc
  | T_SEQ: forall gc lc s1 s2 lc1 lc2,
      stmt_typ gc lc s1 lc1 ->
      stmt_typ gc lc1 s2 lc2 ->
      stmt_typ gc lc (sequence s1 s2) lc2
  | T_AWAIT: forall gc lc sig tys,
      sigc_store gc sig = Some tys ->
      stmt_typ gc lc (await sig 0) lc
  | T_CALL: forall gc lc f args tys rho,
      methc_store gc f = Some (tys, rho) ->
      Forall2 (expr_typ gc lc) args tys ->
      stmt_typ gc lc (callMethod f args) lc
  | T_ASSIGNCALL_L: forall gc lc x f args tys r t,
      methc_store gc f = Some (tys, Some (r, t)) ->
      Forall2 (expr_typ gc lc) args tys ->
      lc x = Some t ->
      stmt_typ gc lc (assignCallMethod x f args) lc
  | T_ASSIGNCALL_G: forall gc lc x f args tys r t,
      methc_store gc f = Some (tys, Some (r, t)) ->
      Forall2 (expr_typ gc lc) args tys ->
      lc x = None ->
      varsc_store gc x = Some t ->
      stmt_typ gc lc (assignCallMethod x f args) lc
  | T_DECLCALL: forall gc lc x f args tys r t,
      methc_store gc f = Some (tys, Some (r, t)) ->
      Forall2 (expr_typ gc lc) args tys ->
      lc x = None ->
      stmt_typ gc lc (declCallMethod x f args) (lc [x := Some t])
  | T_BIND: forall gc lc f sig tys rho,
      methc_store gc f = Some (tys, rho) ->
      sigc_store gc sig = Some tys ->
      stmt_typ gc lc (bind f sig 0) lc
  | T_EMIT: forall gc lc sig args tys,
      sigc_store gc sig = Some tys ->
      Forall2 (expr_typ gc lc) args tys ->
      stmt_typ gc lc (emitSignal sig args) lc
  | T_ENDSCOPE: forall gc lc xs,
      stmt_typ gc lc (endScope xs) (remove_varl xs lc)
  | T_FRAME: forall gc lc valf lcf s lcf',
      local_store_typ valf lcf ->
      stmt_typ gc lcf s lcf' ->
      stmt_typ gc lc (frame valf s) lc
  | T_RETFRAME: forall gc lc lc' tg r valf lcf s lcf' t,
      local_store_typ valf lcf ->
      stmt_typ gc lcf s lcf' ->
      lcf' r = Some t ->
      na s = true ->
      ret_target_typ gc lc tg t lc' ->
      stmt_typ gc lc (retFrame tg r valf s) lc'
.

(* retok(rho, Γ', s) *)
Definition retok (p : meth_ret) (lc' : local_c) (s : stmt) : Prop :=
  match p with
  | None => True
  | Some (r, t) => lc' r = Some t /\ na s = true
  end.

(* Build initial local context of a method body [x1 |-> t1, ..., xn |-> tn] *)
Fixpoint params_ctx (ps : list (string * typ)) : local_c :=
  match ps with
  | nil => empty
  | (x, t) :: ps' => (params_ctx ps') [x := Some t]
  end.

Inductive toplvl_typ : global_c -> topLvl -> global_c -> Prop :=
  | T_SKIP : forall gc,
      toplvl_typ gc skip gc
  | T_CLASSVAR : forall gc x e t,
      varsc_store gc x = None ->
      expr_typ gc empty e t ->
      toplvl_typ gc (classVarDecl x e) (update_varsc_store gc x t)
  | T_SIGNALDECL : forall gc sig ps,
      sigc_store gc sig = None ->
      toplvl_typ gc (signalDecl sig ps) (update_sigc_store gc sig (map snd ps))
  | T_METHODDECL : forall gc f ps rho s lc',
      methc_store gc f = None ->
      NoDup (map fst ps) ->
      stmt_typ (update_methc_store gc f (map snd ps) rho) (params_ctx ps) s lc' ->
      retok rho lc' s ->
      toplvl_typ gc (methodDecl f ps rho s) (update_methc_store gc f (map snd ps) rho)
  | T_READY : forall gc s lc',
      stmt_typ gc empty s lc' ->
      toplvl_typ gc (readyDecl s) gc
  | T_PROCESS : forall gc s lc',
      stmt_typ gc empty s lc' ->
      toplvl_typ gc (processDecl s) gc
  | T_TOPSEQ : forall gc gc1 gc2 t1 t2,
      toplvl_typ gc t1 gc1 ->
      toplvl_typ gc1 t2 gc2 ->
      toplvl_typ gc (sequenceTop t1 t2) gc2
.

Fixpoint nb_prog (prog: topLvl) : nat :=
    match prog with
    |processDecl _ => 1
    |sequenceTop e1 e2 => nb_prog e1 + nb_prog e2
    | _ => 0
    end.

Definition prog_ok (prog: topLvl) : Prop := 
    exists gc, toplvl_typ empty_global_c prog gc /\ nb_prog prog <= 1.