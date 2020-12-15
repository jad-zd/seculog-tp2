Require Import Coq.Program.Equality.
Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Omega.
Import ListNotations.
Close Scope nat_scope.
Open Scope Z_scope.
Require Import String.
Open Scope string_scope.

Definition var := string.
Definition val := Z.
Definition var_eq := string_dec.

(** * 1 - Le langage While *)

(** Le langage While est un langage impératif minimaliste. Les valeurs
manipulées dans ce langage sont des entiers naturels [val := nat] et les
variables sont représentées par un identifiant (de type [string]). *)

(** ** Les expressions, conditions et instructions *)
(** Les expressions [expr] peuvent être des constantes [Const n], des variables
[Var n], ou bien des opérations binaires ([Add], [Mul], [Sub] sur d'autres
expressions). *)

Inductive expr : Set :=
| Const (n: val)
| Var (v: var)
| Add (e1 e2: expr)
| Mul (e1 e2: expr)
| Sub (e1 e2: expr).

(** On a aussi des conditions [cond] qui seront utilisées pour les branchements
conditionnels ([if then else] et [while]). Ces conditions peuvent être l'égalité
entre deux expressions [Eq], une infériorité stricte [Lt], la conjonction ou la
disjonction de deux conditions [And] et [Or] ou bien la négation d'une condition
[Not]. *)

Inductive cond : Set :=
| Eq (e1 e2: expr)
| Lt (e1 e2: expr)
| And (c1 c2: cond)
| Or (c1 c2: cond)
| Not (c: cond).

(** Les instructions [stmt] sont les suivantes :
 - [Skip] : ne rien faire
 - [Assign v e] : stocke le résultat de l'évaluation de [e] dans la variable [v]
 - [Seq s1 s2] : faire [s1], puis [s2]
 - [If c s1 s2] : si [c] est vrai, faire [s1], sinon faire [s2]
 - [While c s] : tant que [c] est vrai, faire [s]
 *)

(** ** Évaluation des expressions et conditions  *)

(** Pour évaluer les expressions, nous avons besoin d'un *environnement* qui
associe à chaque variable sa valeur. On utilisera pour cela le type [state]
définit ci-dessous. Les fonctions d'évaluation des expressions [eval_expr] et
des conditions [eval_cond] sont standard. *)

Definition state := var -> val.

(** [update_env e x z] crée un nouvel environnement à partir de [e] en associant
la valeur [z] à la variable [x]. *)

Definition update_state (e: state) (x: var) (z: val) :=
  fun y => if var_eq y x then z else e y.

Fixpoint eval_expr (env: state) (e: expr) : val :=
  match e with
  | Const n => n
  | Var v => env v
  | _ => 0
  end.

Compute
  let s := fun _ => 0 in
  let s := update_state s "x" 12 in
  let s := update_state s "y" 5 in
  let e := Mul (Const 3) (Add (Var "x") (Mul (Const 12) (Sub (Var "x") (Var "y")))) in
  eval_expr s e.

Fixpoint eval_cond (env: state) (c: cond) : bool :=
  match c with
  | Eq e1 e2 => Z.eqb (eval_expr env e1) (eval_expr env e2)
  | Lt e1 e2 => Z.ltb (eval_expr env e1) (eval_expr env e2)
  | _ => false
  end.

Fixpoint eval_condP (env: state) (c: cond) : Prop :=
  match c with
  | Eq e1 e2 => (eval_expr env e1) = (eval_expr env e2)
  | Lt e1 e2 => (eval_expr env e1) < (eval_expr env e2)
  | _ => False
  end.

Lemma eval_cond_true:
  forall env c,
    eval_condP env c <->
    eval_cond env c = true.
Proof.
Admitted.

Lemma eval_cond_false:
  forall env c,
    ~ eval_condP env c <->
    eval_cond env c = false.
Proof.
Admitted.

Lemma eval_cond_dec:
  forall env c, {eval_condP env c} + {~ eval_condP env c}.
Proof.
Admitted.                       (* à remplacer par Defined. quand vous aurez fini. *)
(* Defined permet de rendre les définitions *transparentes*, et pourront donc
être évaluées par la commande Compute. *)

Compute
  let s := fun _ => 0 in
  let s := update_state s "x" 12 in
  let s := update_state s "y" 5 in
  let e := Mul (Const 3) (Add (Var "x") (Mul (Const 12) (Sub (Var "x") (Var "y")))) in
  eval_cond_dec s (Eq e (Const 288)).



Inductive stmt  :=
| Skip
| Assign (v: var) (e: expr)
| Seq (s1 s2: stmt)
| If (c: cond) (s1 s2: stmt)
| While (c: cond) (I: state -> Prop) (s: stmt)
.

