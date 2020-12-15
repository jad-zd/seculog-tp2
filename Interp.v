Require Import Coq.Program.Equality.
Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Omega.
Import ListNotations.
Open Scope nat_scope.
Close Scope Z_scope.
Require Import String.
Open Scope string_scope.
Require Import While Tactics.
Require Import WhileBigStep.
Require Import Lia.

Fixpoint exec_prog (fuel: nat) (env: state) (i: stmt) : option state :=
None.

Definition p1 :=
  Seq (Assign "x" (Const 10%Z))
      (Seq (Assign "sum" (Const 0%Z))
           (While (Not (Eq (Var "x") (Const 0%Z)))
                  (fun _ => True)
                  (Seq
                     (Assign "sum" (Add (Var "sum") (Var "x")))
                     (Assign "x" (Sub (Var "x") (Const 1%Z)))
                  )
           )
      ).

(* Le calcul suivant devrait retourner [Some 55]. *)
Compute
  option_map (fun env => env "sum")
  (exec_prog 30 (fun _ => 0%Z) p1).


Theorem exec_prog_bigstep:
  forall fuel s i s',
    exec_prog fuel s i = Some s' ->
    bigstep s i s'.
Proof.
Admitted.

Lemma exec_prog_more_fuel:
  forall f s i s',
    exec_prog f s i = Some s' ->
    forall f',
      f' >= f ->
      exec_prog f' s i = Some s'.
Proof.
Admitted.

Theorem bigstep_exec_prog:
  forall s i s',
    bigstep s i s' ->
    exists fuel,
      exec_prog fuel s i = Some s'.
Proof.
Admitted.

