From Stdlib Require Import String ZArith Bool.
Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A} (d : A) : total_map A := fun _ => d.

Definition t_update {A} (m : total_map A) (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "m [ x := v ]" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(* partial version: unbound variables give None *)
Definition partial_map (A : Type) := total_map (option A).
Definition empty {A} : partial_map A := t_empty None.