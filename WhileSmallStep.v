Require Import Coq.Program.Equality.
Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.
Close Scope Z_scope.
Require Import String.
Open Scope string_scope.
Require Import While Tactics.

Inductive step : stmt -> state -> stmt -> state -> Prop :=
| step_assign: forall env x e,
  step (Assign x e) env Skip (update_state env x (eval_expr env e))
| step_if_true:
  forall env c s1 s2, eval_condP env c -> step (If c s1 s2) env s1 env
| step_if_false:
  forall env c s1 s2, ~ eval_condP env c -> step (If c s1 s2) env s2 env
| step_while_true:
  forall env c I s,
  eval_condP env c -> step (While c I s) env (Seq s (While c I s)) env
| step_while_false:
  forall env c I s, ~ eval_condP env c -> step (While c I s) env Skip env
| step_seq:
  forall env s1 s1' env' s2,
  step s1 env s1' env' -> step (Seq s1 s2) env (Seq s1' s2) env'
| step_seq_skip: forall env s2, step (Seq Skip s2) env s2 env.

Inductive star : stmt -> state -> stmt -> state -> Prop :=
| star_refl: forall env i, star i env i env
| star_step: forall env1 i1 env2 i2 env3 i3,
  step i1 env1 i2 env2 -> star i2 env2 i3 env3 -> star i1 env1 i3 env3.

