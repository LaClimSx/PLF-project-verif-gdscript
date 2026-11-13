From Stdlib Require Import String List.
Import ListNotations.
Require Import Valuation GDS_Inductive GDS_Solving.
Open Scope list_scope.

(*  Examples
    Statements run in a world with a single class (index 0) *)
    (*--------------------------------------------------------*)

Open Scope string_scope.
Open Scope gds_scope.

(* A class with a global count, two methods and a signal *)
Definition cs0 : class_state :=
  let cs := update_gs empty_cs "count" (Nat 0) in
  let cs := update_method_store cs "incr" nil None <{ "count" := "count" + 1 }> in
  let cs := update_method_store cs "get" nil (Some "r") <{ var "r" := "count" }> in
  update_signal_store cs "tick" nil.

Definition w0 : world := [cs0].

(* global variable x of class c in world w *)
Definition global_of (w : world) (c : nat) (x : string) : option value :=
  match nth_error w c with Some cs => global_store cs x | None => None end.

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

Example prog1_runs : exists w val,
  multi w0 0 empty prog1 w val pass
  /\ global_of w 0 "count" = Some (Nat 2)
  /\ val "c" = Some (Nat 2)
  /\ val "z" = Some (Bool true).
Proof. do 2 eexists. split; [unfold prog1; run | repeat split; reflexivity]. Qed.

(* Loop whose body declares a local: the local dies at the end of each iteration *)
Definition prog2 : stmt := <{
  var "i" := 0 ;
  while ("i" == 3) == false do var "y" := "i" ; "i" := "i" + 1 end
}>.

Example prog2_runs : exists w val,
  multi w0 0 empty prog2 w val pass /\ val "i" = Some (Nat 3) /\ val "y" = None.
Proof. do 2 eexists. split; [unfold prog2; run | split; reflexivity]. Qed.

(* await inside a while loop: each emission runs one more iteration *)
Definition waiter : stmt :=
  <{ while true do await "tick" on 0 ; "count" := "count" + 10 end }>.

Definition prog3 : stmt :=
  sequence (frame 0 empty waiter) <{ emit "tick" () ; emit "tick" () }>.

Example prog3_runs : exists w val,
  multi w0 0 empty prog3 w val pass
  /\ global_of w 0 "count" = Some (Nat 20)
  /\ (match nth_error w 0 with
      | Some cs => length (list_or_nil (waiting_bodies cs "tick"))
      | None => 0 end) = 1.
Proof. do 2 eexists. split; [unfold prog3; run | split; reflexivity]. Qed.


(*  Whole programs with one class *)
(*--------------------------------*)

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
Example cls_runs : exists w, eval_program 3 [cls] w /\ global_of w 0 "count" = Some (Nat 133).
Proof. eexists. split; [unfold cls; program_run | reflexivity]. Qed.

(* No process: frames do nothing *)
Definition cls2 : topLvl := <[ var "x" := 1 ; ready do "x" := "x" + 1 end ]>.
Example cls2_runs : exists w, eval_program 5 [cls2] w /\ global_of w 0 "x" = Some (Nat 2).
Proof. eexists. split; [unfold cls2; program_run | reflexivity]. Qed.

(* Two ready: initialization is stuck *)
Example two_ready : forall cs r p,
  ~ init empty_cs <[ ready do pass end ; ready do pass end ]> cs r p.
Proof.
  intros cs r p H. inversion H; subst.
  repeat match goal with Hi : init _ (readyDecl _) _ _ _ |- _ => inversion Hi; subst; clear Hi end.
  simpl in *. discriminate.
Qed.


(* Awaits in series*)
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

Example cls3_runs : exists w, eval_program 5 [cls3] w /\ global_of w 0 "ret1" = Some (Nat 10) /\ global_of w 0 "ret2" = Some (Nat 5).
Proof. eexists. split; [unfold cls3; program_run | repeat split; reflexivity]. Qed.


(* Multiple Classes *)
(*------------------------------------------------------*)

(* Class 0: counts frames and emits "hit" every frame *)
Definition emitter : topLvl := <[
  var "frames" := 0 ;
  signal "hit" () ;
  process do "frames" := "frames" + 1 ; emit "hit" () end
]>.

(* Class 1: binds one of its methods to "hit" of class 0, and waits for it in
   a loop. Both run in the context of class 1 (they update its own count).
   Its process copies its count into "seen" after class 0 has emitted. *)
Definition listener : topLvl := <[
  var "count" := 0 ;
  var "seen" := 0 ;
  ready do
    bind "onHit" to "hit" on 0 ;
    while true do await "hit" on 0 ; "count" := "count" + 10 end
  end ;
  func "onHit" () do "count" := "count" + 1 end ;
  process do "seen" := "count" end
]>.

(* 3 frames: each frame, class 0 emits (onHit +1, waiting loop +10 in class 1),
   then the process of class 1 runs *)
Example two_classes : exists w,
  eval_program 3 [emitter; listener] w
  /\ global_of w 0 "frames" = Some (Nat 3)
  /\ global_of w 1 "count" = Some (Nat 33)
  /\ global_of w 1 "seen" = Some (Nat 33)
  /\ global_of w 0 "count" = None.
Proof. eexists. split; [program_run | repeat split; reflexivity]. Qed.

(* Same classes in the other order: the listener's process now runs before the
   emission of each frame, so "seen" lags one frame behind.
   The listener is class 0 and the emitter class 1, so the indices change. *)
Definition listener' : topLvl := <[
  var "count" := 0 ;
  var "seen" := 0 ;
  ready do
    bind "onHit" to "hit" on 1 ;
    while true do await "hit" on 1 ; "count" := "count" + 10 end
  end ;
  func "onHit" () do "count" := "count" + 1 end ;
  process do "seen" := "count" end
]>.

Example two_classes_order : exists w,
  eval_program 3 [listener'; emitter] w
  /\ global_of w 0 "count" = Some (Nat 33)
  /\ global_of w 0 "seen" = Some (Nat 22).
Proof. eexists. split; [program_run | repeat split; reflexivity]. Qed.