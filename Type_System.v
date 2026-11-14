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


(* Value typing
Inductive value_typing : value -> typ -> Prop:=
    |VNat: n -> TNat
    |VBool: b -> TBool
. *)