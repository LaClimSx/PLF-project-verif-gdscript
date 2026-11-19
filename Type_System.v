Require Import GDS_Inductive Valuation.
From Stdlib Require Import String.

(*Types and contexts*)
Inductive typ := TNat | TBool.

(* rho in PDF = return variable name and its type *)
Definition meth_ret := option (string * typ).

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
  |VBool: forall b, value_typing (Bool b) TBool
.

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
  
  
  