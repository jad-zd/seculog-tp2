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
Require Import WhileBigStep.
Require Import Lia.

Fixpoint exec_prog (fuel: nat) (env: state) (i: stmt) : option state :=
  match fuel with
  | O => None
  | S fuel_1 =>
    match i with
    | Skip => Some env
    | Assign v e => Some (update_state env v (eval_expr env e))
    | Seq s1 s2 =>
      match exec_prog fuel_1 env s1 with
      | None => None
      | Some env' => exec_prog fuel_1 env' s2
      end
    | If c s1 s2 => 
      if eval_cond env c
      then exec_prog fuel_1 env s1
      else exec_prog fuel_1 env s2
    | While c Inv s =>
      if eval_cond env c
      then match exec_prog fuel_1 env s with
      | None => None
      | Some env' => exec_prog fuel_1 env' (While c Inv s)
      end
      else Some env
    end
  end.

Definition p1 :=
  Seq
    (Assign "x" (Const 10%Z))
    (Seq
      (Assign "sum" (Const 0%Z))
      (While
        (Not (Eq (Var "x") (Const 0%Z)))
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
  forall fuel s i s', exec_prog fuel s i = Some s' -> bigstep s i s'.
Proof.
  intro.
  induction fuel.
  - intros. simpl in H. discriminate H.
  - intros. destruct i.
    * injection H as H. rewrite H. apply bigstep_skip.
    * injection H as H. rewrite <- H. apply bigstep_assign.
    * destruct (exec_prog fuel s i1) eqn:Eqn.
      -- eapply bigstep_seq.
        ** eapply IHfuel. apply Eqn.
        ** eapply IHfuel. simpl in H. rewrite Eqn in H. apply H.
      -- eapply bigstep_seq.
        ** eapply IHfuel. simpl in H. rewrite Eqn in H. rewrite <- H. apply Eqn.
        ** eapply IHfuel. simpl in H. rewrite Eqn in H. rewrite <- H. discriminate.
    * simpl in H. destruct (eval_cond s c) eqn:E2.
      -- eapply bigstep_if_true.
        ** apply eval_cond_true. apply E2.
        ** apply IHfuel. apply H.
      -- eapply bigstep_if_false.
        ** apply eval_cond_false. apply E2.
        ** apply IHfuel. apply H.
    * simpl in H. destruct (eval_cond s c) eqn:E3. destruct (exec_prog fuel s i) eqn:E4.
      -- eapply bigstep_while_true.
        ** apply eval_cond_true. apply E3.
        ** apply IHfuel. eapply E4.
        ** apply IHfuel. apply H.
      -- discriminate.
      -- injection H as H. rewrite <- H. eapply bigstep_while_false. apply eval_cond_false. apply E3.
Qed.


Lemma exec_prog_more_fuel:
  forall f s i s',
  exec_prog f s i = Some s'
  -> forall f', f' >= f
  -> exec_prog f' s i = Some s'.
Proof.
  intros fuel.
  induction fuel.
  - intros. inversion H.
  - intros. simpl in H.  destruct f'.
  * lia.
  * simpl. destruct i.
    -- apply H.
    -- apply H.
    -- destruct (exec_prog fuel s i1) eqn:E.
      ** eapply IHfuel in E. 
        --- rewrite E. eapply IHfuel in H.
          *** eapply H.
          *** lia.
        --- lia.
      ** discriminate.
    -- destruct (eval_cond s c) eqn:E2.
      ** eapply IHfuel.
        --- apply H.
        --- lia.
      ** eapply IHfuel.
        --- apply H.
        --- lia.
    -- destruct (eval_cond s c) eqn:E3.
      ** destruct (exec_prog fuel s i) eqn:E4.
        --- eapply IHfuel in E4.
          *** rewrite E4. eapply IHfuel.
            ---- apply H.
            ---- lia.
          *** lia.
        --- discriminate.
      ** congruence.
Qed.

Theorem bigstep_exec_prog:
  forall s i s',
  bigstep s i s'
  -> exists fuel, exec_prog fuel s i = Some s'.
Proof.
  intros s i s' H.
  induction H.
  - exists 1. simpl. reflexivity.
  - exists 1. simpl. reflexivity.
  - destruct IHbigstep1. destruct IHbigstep2. exists (S (max x x0)). simpl.
  rewrite (exec_prog_more_fuel x env s1 env').
    * rewrite (exec_prog_more_fuel x0 env' s2 env'').
      + reflexivity.
      + apply H2.
      + lia.
    * apply H1.
    * lia.
  - destruct IHbigstep as [fuel]. exists (S fuel). simpl.
  destruct (eval_cond env c) eqn:E2.
    * apply H1.
    * apply eval_cond_true in H. congruence.
  - destruct IHbigstep as [fuel]. exists (S fuel). simpl.
  destruct (eval_cond env c) eqn:E3.
    * apply eval_cond_false in H. congruence.
    * apply H1.
  - apply eval_cond_false in H. exists 1. simpl.
  destruct (eval_cond env c) eqn:E4.
    * discriminate.
    * reflexivity.
  - destruct IHbigstep1 as [fuel1]. destruct IHbigstep2 as [fuel2].
  exists (S (max fuel1 fuel2)). simpl. destruct (eval_cond env c) eqn:E5.
    * apply eval_cond_true in H. rewrite (exec_prog_more_fuel fuel1 env s env').
      + rewrite (exec_prog_more_fuel fuel2 env' (While c I s) env'').
        -- reflexivity.
        -- apply H3.
        -- lia.
      + apply H2.
      + lia.
    * apply eval_cond_true in H. congruence.
Qed.
