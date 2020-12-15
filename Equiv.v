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
Require Import WhileSmallStep WhileBigStep.


Lemma star_seq:
  forall s1 env1 env2,
    star s1 env1 Skip env2 ->
    forall s2 s3 env3,
      star s2 env2 s3 env3 ->
      star (Seq s1 s2) env1 s3 env3.
Proof.
  intros s1 env1 env2 Hstar.
  dependent induction Hstar; simpl; intros.
Admitted.


Theorem bigstep_star:
  forall i env env',
    bigstep env i env' ->
    star i env Skip env'.
Proof.
Admitted.

Lemma step_bigstep:
  forall i env i' env',
    step i env i' env' ->
    forall env'',
      bigstep env' i' env'' ->
      bigstep env i env''.
Proof.
Admitted.

Theorem star_bigstep:
  forall i env env',
    star i env Skip env' ->
    bigstep env i env'.
Proof.
Admitted.


