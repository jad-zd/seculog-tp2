Ltac inv H := inversion H; try subst; clear H.

Ltac trim H :=
  match type of H with
  | ?A -> ?B =>
    let x := fresh in
    assert (x: A); [clear H| specialize (H x); clear x]
  end.

Require Import Arith ZArith Lia.

Definition Zfact n := Z.of_nat (fact (Z.to_nat n)).

Lemma fact_S: (forall n : nat, n <> 0 -> fact n = n * fact (n - 1))%nat.
Proof.
  destruct n; simpl; auto. congruence.
  rewrite ! Nat.sub_0_r.  auto.
Qed.

Open Scope Z_scope.

Lemma Zfact_pos: forall z, 0 < z -> Zfact z = z * Zfact (z - 1).
Proof.
  unfold Zfact. intros.
  rewrite (fact_S (Z.to_nat z)). 2: lia.
  rewrite Z2Nat.inj_sub. simpl. 2: lia.
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat.id. 2: lia. reflexivity.
Qed.

Lemma Zfact_neg: forall z, z <= 0 -> Zfact z = 1.
Proof.
  unfold Zfact; intros.
  unfold Z.to_nat.
  destruct z; simpl; auto. lia.
Qed.

Fixpoint fib n :=
  (match n with
  | O => 1%nat
  | S n' =>
    match n' with
    | O => 1
    | S n'' => fib n' + fib n''
    end
  end)%nat.

Lemma fib_eqn (n: nat) : (n > 0 -> fib n + fib (Nat.pred n) = fib (1 + n))%nat.
Proof. induction n; simpl; intros; eauto. lia. Qed.

Definition Zfib n := Z.of_nat (fib (Z.to_nat n)).

Lemma Zfib_eqn (n: Z) : n > 0 -> Zfib n + Zfib (n - 1) = Zfib (1 + n).
Proof.
  unfold Zfib. intros.
  rewrite Z2Nat.inj_add by lia.
  rewrite Z2Nat.inj_sub by lia.
  rewrite <- fib_eqn by lia. f_equal.
  rewrite <- Nat2Z.inj_add. f_equal. f_equal. f_equal. lia.
Qed.

