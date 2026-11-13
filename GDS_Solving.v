From Stdlib Require Import String List.
Import ListNotations.
Require Import Valuation GDS_Inductive.
Open Scope list_scope.

(* ================================================================== *)
(*  Executable evaluation of expressions (used to run examples)       *)
(* ================================================================== *)

Fixpoint eval_e (cs : class_state) (val : valuation) (e : expr) : option value :=
  match e with
  | nConst n => Some (Nat n)
  | bConst b => Some (Bool b)
  | Var x => match val x with
             | Some v => Some v
             | None => global_store cs x
             end
  | Binop b e1 e2 =>
      match eval_e cs val e1, eval_e cs val e2 with
      | Some v1, Some v2 => interp_binop b v1 v2
      | _, _ => None
      end
  end.

Lemma eval_e_sound : forall cs val e v,
  eval_e cs val e = Some v -> eval_expr cs val e v.
Proof.
  intros cs val e. induction e; intros v H; simpl in H.
  - inversion H; constructor.
  - inversion H; constructor.
  - destruct (val s) eqn:Hs.
    + inversion H; subst. now apply VarLookupLocal.
    + now apply VarLookupGlobal.
  - destruct (eval_e cs val e1) eqn:H1; [|discriminate].
    destruct (eval_e cs val e2) eqn:H2; [|discriminate].
    eapply BinopEval; eauto.
Qed.

Fixpoint eval_args (cs : class_state) (val : valuation) (args : list expr) : option (list value) :=
  match args with
  | [] => Some nil
  | a :: args' =>
      match eval_e cs val a, eval_args cs val args' with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Lemma eval_args_sound : forall cs val args vs,
  eval_args cs val args = Some vs -> Forall2 (eval_expr cs val) args vs.
Proof.
  intros cs val args. induction args as [|a args' IH]; intros vs H; simpl in H.
  - inversion H. constructor.
  - destruct (eval_e cs val a) eqn:Ha; [|discriminate].
    destruct (eval_args cs val args') eqn:Hargs; [|discriminate].
    inversion H; subst. constructor; auto using eval_e_sound.
Qed.





(* ================================================================== *)
(*  Tactics to run examples                                           *)
(* ================================================================== *)

Ltac solve_premise :=
  match goal with
  | |- eval_expr _ _ _ _ => apply eval_e_sound; reflexivity
  | |- Forall2 (eval_expr _ _) _ _ => apply eval_args_sound; reflexivity
  | |- _ => reflexivity
  end.

(* One step, choosing the rule from the shape of the statement *)
Ltac sstep :=
  match goal with
  (* statement built by a function (e.g. waiting_frames): compute its head first *)
  | |- step ?c ?v ?s ?c' ?v' ?s' =>
      let h := eval hnf in s in
      tryif constr_eq h s then fail else (change (step c v h c' v' s'); sstep)
  | |- step _ _ (sequence pass _) _ _ _ => apply S_SeqPass
  | |- step _ _ (sequence _ _) _ _ _ => eapply S_Seq; sstep
  | |- step _ _ (frame _ pass) _ _ _ => apply S_FrameDone
  | |- step _ _ (frame _ _) _ _ _ =>
      first [ eapply S_FrameAwait; reflexivity | eapply S_Frame; sstep ]
  | |- step _ _ (retFrame _ _ _ pass) _ _ _ => eapply S_RetDone; reflexivity
  | |- step _ _ (retFrame _ _ _ _) _ _ _ => eapply S_RetFrame; sstep
  | |- step _ _ (assign _ _) _ _ _ =>
      first [ eapply S_AssignL; solve_premise | eapply S_AssignG; solve_premise ]
  | |- step _ _ (ifThenElse _ _ _) _ _ _ =>
      first [ eapply S_IfT; solve_premise | eapply S_IfF; solve_premise ]
  | |- step _ _ (whileLoop _ _) _ _ _ =>
      first [ eapply S_WhileF; solve_premise | eapply S_WhileT; solve_premise ]
  | |- step _ _ _ _ _ _ => econstructor; solve_premise
  end.

(* Steps until no rule applies (loops forever on a diverging program) *)
Ltac run := repeat (eapply M_Step; [sstep |]); apply M_Refl.





(* ================================================================== *)
(*  Tactics to run whole classes                                      *)
(* ================================================================== *)

Ltac init_run :=
  match goal with
  | |- init _ (sequenceTop _ _) _ _ _ =>
      eapply I_Seq; [init_run | init_run | reflexivity | reflexivity]
  | |- init _ _ _ _ _ => econstructor; solve_premise
  end.

Ltac pstep_run :=
  first [ eapply P_Step; sstep | apply P_NextFrame ].

Ltac class_run :=
  eapply Eval; [ init_run | repeat (eapply PM_Step; [pstep_run |]); apply PM_Refl ].