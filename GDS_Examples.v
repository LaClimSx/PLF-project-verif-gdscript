From Stdlib Require Import String List.
Import ListNotations.
Require Import Valuation GDS_Inductive GDS_Solving.
Open Scope list_scope.

(* ================================================================== *)
(*  Examples                                                          *)
(* ================================================================== *)

Open Scope string_scope.
Open Scope gds_scope.

(* A class with a global count, two methods and a signal *)
Definition cs0 : class_state :=
  let cs := update_gs empty_cs "count" (Nat 0) in
  let cs := update_method_store cs "incr" nil None <{ "count" := "count" + 1 }> in
  let cs := update_method_store cs "get" nil (Some "r") <{ var "r" := "count" }> in
  update_signal_store cs "tick" nil.

(* Calls, return values, bind/emit, and block scoping *)
Definition prog1 : stmt := <{
  bind "incr" to "tick" on 0 ;
  emit "tick" () ;
  var "c" <- "get" () ;
  "incr" () ;
  "c" <- "get" () ;
  if true then var "z" := 1 else pass end ;
  var "z" := true
}>.

Example prog1_runs : exists cs val,
  multi cs0 empty prog1 cs val pass
  /\ global_store cs "count" = Some (Nat 2)
  /\ val "c" = Some (Nat 2)
  /\ val "z" = Some (Bool true).
Proof. do 2 eexists. split; [unfold prog1; run | repeat split; reflexivity]. Qed.

(* Loop whose body declares a local: the local dies at the end of each iteration *)
Definition prog2 : stmt := <{
  var "i" := 0 ;
  while ("i" == 3) == false do var "y" := "i" ; "i" := "i" + 1 end
}>.

Example prog2_runs : exists cs val,
  multi cs0 empty prog2 cs val pass /\ val "i" = Some (Nat 3) /\ val "y" = None.
Proof. do 2 eexists. split; [unfold prog2; run | split; reflexivity]. Qed.

(* await inside a while loop: each emission runs one more iteration *)
Definition waiter : stmt :=
  <{ while true do await "tick" on 0 ; "count" := "count" + 10 end }>.

Definition prog3 : stmt :=
  sequence (frame empty waiter) <{ emit "tick" () ; emit "tick" () }>.

Example prog3_runs : exists cs val,
  multi cs0 empty prog3 cs val pass
  /\ global_store cs "count" = Some (Nat 20)
  /\ length (list_or_nil (waiting_bodies cs "tick")) = 1.
Proof. do 2 eexists. split; [unfold prog3; run | split; reflexivity]. Qed.


(* ================================================================== *)
(*  Whole classes                                                     *)
(* ================================================================== *)

(* ready is declared before the methods it calls *)
Definition cls : topLvl := <[
  var "count" := 0 ;
  signal "tick" () ;
  ready do
    bind "incr" to "tick" on 0 ;
    "setup" () ;
    while true do await "tick" on 0 ; "count" := "count" + 10 end
  end ;
  func "setup" () do "count" := 100 end ;
  func "incr" () do "count" := "count" + 1 end ;
  process do emit "tick" () end
]>.

(* 3 frames: each emission runs incr (+1) then the waiting loop (+10) *)
Example cls_runs : exists cs, eval_class 3 cls cs /\ global_store cs "count" = Some (Nat 133).
Proof. eexists. split; [unfold cls; class_run | reflexivity]. Qed.

(* No process: frames do nothing *)
Definition cls2 : topLvl := <[ var "x" := 1 ; ready do "x" := "x" + 1 end ]>.
Example cls2_runs : exists cs, eval_class 5 cls2 cs /\ global_store cs "x" = Some (Nat 2).
Proof. eexists. split; [unfold cls2; class_run | reflexivity]. Qed.

(* Two ready: initialization is stuck *)
Example two_ready : forall cs r p,
  ~ init empty_cs <[ ready do pass end ; ready do pass end ]> cs r p.
Proof.
  intros cs r p H. inversion H; subst.
  repeat match goal with Hi : init _ (readyDecl _) _ _ _ |- _ => inversion Hi; subst; clear Hi end.
  simpl in *. discriminate.
Qed.


Definition cls3: topLvl := <[
  var "a" := 0 ;
  var "ret1" := 3 ;
  var "ret2" := 1 ;
  signal "sig" () ;
  ready do
    await "sig" on 0 ;
    "ret1" := 10 ;
    await "sig" on 0 ;
    "ret2" := 5
    end ;
  process do 
  "a" := "a" + 1 ;
  if ("a" == 2) then 
    emit "sig" () 
  else 
    (if ("a" == 5) then 
      emit "sig" () 
    else 
      pass end)
    end
  end
]>.

Example cls3_runs : exists cs, eval_class 5 cls3 cs /\ global_store cs "ret1" = Some (Nat 10) /\ global_store cs "ret2" = Some (Nat 5).
Proof. eexists. split; [unfold cls3; class_run | repeat split; reflexivity]. Qed.
