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
Require Import While Tactics WhileBigStep.
Require Import Hoare.

Definition swap :=
  Seq
    (Seq (Assign "tmp" (Var "x")) (Assign "x" (Var "y")))
    (Assign "y" (Var "tmp")).

Lemma swap_correct:
  forall A B,
  valid_hoare_triple
    (fun env => env "x" = A /\ env "y" = B)
    swap
    (fun env => env "x" = B /\ env "y" = A).
Proof.
  intros A B.
  apply auto_hoare'; simpl.
  unfold update_state; simpl.
  intros. destruct H. split.
  - apply H0.
  - apply H.
Qed.

Definition slow_assign : stmt :=
  While
    (Lt (Var "x") (Var "b"))
    (fun env => eval_expr env (Var "x") <= eval_expr env (Var "b"))
    (Assign "x" (Add (Var "x") (Const 1))).

Lemma slow_assign_correct:
  valid_hoare_triple
    (fun env => env "x" <= env "b")
    slow_assign
    (fun env => env "x" = env "b").
Proof.
  intros.
  apply auto_hoare'; simpl.
  unfold update_state; simpl.
  intros. split.
  - lia.
  - intros. lia.
Qed.


Definition dummy_sum (x y: Z) :=
  Seq
    (Assign "x" (Const x))
    (Seq
      (Assign "y" (Const y))
      (While
        (Lt (Const 0) (Var "y"))
         (fun env => eval_expr env (Var "y") >= 0 /\ (eval_expr env (Var "x")) + (eval_expr env (Var "y")) = x + y)
        (Seq
          (Assign "x" (Add (Var "x") (Const 1)))
          (Assign "y" (Sub (Var "y") (Const 1)))
        )
      )
    ).

Theorem dummy_sum_correct x y:
  0 <= y
  -> valid_hoare_triple
       (fun _ => True)
       (dummy_sum x y)
       (fun env => env "x" = x + y).
Proof.
  intros.
  apply auto_hoare'.
  simpl; unfold update_state; simpl; intros.
  split.
  - lia.
  - intros. split.
    * lia.
    * intros. lia.
Qed.

Definition gcd (x y : Z) :=
  While
    (Not (Eq (Var "x") (Var "y")))
       (fun env => Z.gcd (env "x") (env "y") = Z.gcd x y)
    (If
      (Lt (Var "x") (Var "y"))
      (Assign "y" (Sub (Var "y") (Var "x")))
      (Assign "x" (Sub (Var "x") (Var "y")))
    ).

Check Z.gcd_sub_diag_r.
Check Z.gcd_comm.
Check Z.gcd_diag.

Theorem gcd_correct:
  forall x y,
  valid_hoare_triple
    (fun env => env "x" = x /\ env "y" = y)
    (gcd x y)
    (fun env => env "x" = env "y" /\ Z.gcd x y = Z.abs (env "x")).
Proof.
  intros. apply auto_hoare'.
  simpl. unfold update_state; simpl.
  intros. split.
    - destruct H. rewrite H. rewrite H0. reflexivity.
    - intros. split.
      * intros. split.
        + intro. rewrite <- H2. apply Z.gcd_sub_diag_r.
        + intros. rewrite Z.gcd_comm. rewrite <- H2.
          rewrite (Z.gcd_comm (env' "x") (env' "y")).
          apply Z.gcd_sub_diag_r.
      * intros. split.
        + lia.
        + rewrite <- H2. assert (env' "x" = env' "y").
          -- lia.
          -- rewrite <- H3. apply Z.gcd_diag.
Qed.  

Definition factorielle n :=
  Seq
    (Assign "res" (Const 1))
    (While
      (Lt (Const 0) (Var "n"))
      (fun env => env "res" * Zfact (env "n") = Zfact n)
      (Seq
        (Assign "res" (Mul (Var "res") (Var "n")))
        (Assign "n" (Sub (Var "n") (Const 1)))
      )
    ).

(* La commande suivante empêche que [Z.mul] soit déplié dans les preuves. Cela
évitera certains buts "bizarres". *)
Opaque Z.mul.

Check Zfact_pos.
Check Zfact_neg.
Check Z.mul_assoc.
Check Z.mul_1_l.

Theorem factorielle_correct:
  forall n, n >= 0
  -> valid_hoare_triple
       (fun env => env "n" = n)
       (factorielle n)
       (fun env => env "res" = Zfact n).
Proof.
  intros.
  apply auto_hoare'; simpl.
  unfold update_state; simpl; intros.
  split.
  - rewrite H0. lia.
  - intros. split.
    * intros. rewrite <- Z.mul_assoc. rewrite <- Zfact_pos.
      + apply H3.
      + apply H2.
    * intros. rewrite (Zfact_neg (env' "n")) in H3.
      + lia.
      + lia.
Qed.

(* On définit la condition [a <= b] comme étant [a = b || a < b] *)
Definition Le a b := Or (Eq a b) (Lt a b).

Example div_mod a b :=
  Seq
    (Assign "x" (Const a))
    (Seq
      (Assign "y" (Const 0))
      (While
        (Le (Const b) (Var "x"))
           (fun env => True)
        (Seq
          (Assign "x" (Sub (Var "x") (Const b)))
          (Assign "y" (Add (Var "y") (Const 1)))
        )
      )
    ).

Theorem div_mod_correct a b:
  valid_hoare_triple
    (fun env => True)
    (div_mod a b)
    (fun env => b * env "y" + env "x" = a /\ env "x" < b).
Proof.
Admitted.

Definition parity x :=
  Seq
    (Assign "x" (Const x))
    (Seq
      (If (Lt (Const 0) (Var "x")) Skip (Assign "x" (Sub (Const 0) (Var "x"))))
      (While
        (Le (Const 2) (Var "x"))
           (fun env => True)
        (Assign "x" (Sub (Var "x") (Const 2)))
      )
    ).

Check Z.even_sub.
Check Z.even_opp.

Theorem parity_correct x:
  valid_hoare_triple
    (fun env => True)
    (parity x)
    (fun env =>
       match env "x" with
       | 0 => Z.even x = true
       | 1 => Z.even x = false
       | _ => False
       end
    ).
Proof.
Admitted.

Definition sqrt x :=
  Seq
    (Assign "x" (Const x))
    (Seq
      (Assign "z" (Const 0))
      (While
        (Le (Mul (Add (Var "z") (Const 1)) (Add (Var "z") (Const 1))) (Var "x"))
           (fun env => True)
        (Assign "z" ((Add (Var "z") (Const 1))))
      )
    ).

Theorem sqrt_correct x:
  0 <= x
  -> valid_hoare_triple
      (fun env => env "x" = x)
      (sqrt x)
      (fun env =>
        env "z" * env "z" <= x
        /\ x < (env "z" + 1) * (env "z" + 1)
      ).
Proof.
Admitted.

Definition square1 x :=
  Seq
    (Assign "x" (Const x))
    (Seq
      (Assign "y" (Var "x"))
      (Seq
        (Assign "z" (Const 0))
        (While
          (Not (Eq (Var "y") (Const 0)))
             (fun env => True)
          (Seq
            (Assign "z" (Add (Var "z") (Var "x")))
            (Assign "y" (Sub (Var "y") (Const 1)))
          )
        )
      )
    ).

Theorem square1_correct x:
  valid_hoare_triple
    (fun env => True)
    (square1 x)
    (fun env => env "z" = x * x).
Proof.
Admitted.

Definition square2 x :=
  Seq
    (Assign "x" (Const x))
    (Seq
      (Assign "y" (Const 0))
      (Seq
        (Assign "z" (Const 0))
        (While
          (Not (Eq (Var "y") (Var "x")))
             (fun env => True)
          (Seq
            (Assign "z" (Add (Var "z") (Var "x")))
            (Assign "y" (Add (Var "y") (Const 1)))
          )
        )
      )
    ).

Theorem square2_correct x:
  valid_hoare_triple
    (fun env => True)
    (square2 x)
    (fun env => env "z" = x * x).
Proof.
Admitted.

Check Zfib.

Definition Fib n :=
  Seq
    (Assign "x" (Const 1))
    (Seq
      (Assign "y" (Const 1))
      (Seq
        (Assign "z" (Const 1))
        (While
          (Not (Eq (Var "x") (Const (1 + n))))
          (fun env => True)
          (Seq
            (Assign "t" (Var "z"))
            (Seq
              (Assign "z" (Add (Var "z") (Var "y")))
              (Seq
                (Assign "y" (Var "t"))
                (Assign "x" (Add (Var "x") (Const 1)))
              )
            )
          )
        )
      )
    ).

Opaque Z.sub Z.add.

Check Z.add_comm.
Check Zfib_eqn.

Theorem fib_correct n:
  0 <= n
  -> valid_hoare_triple (fun env => True) (Fib n) (fun env => env "y" = Zfib n).
Proof.
Admitted.

