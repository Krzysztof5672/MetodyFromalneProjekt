(*Laby 2*)

(*Zad 1*)

Definition ownOr (x : bool) (y : bool) : bool :=
  match x , y with 
  |  false , false => false
  |  _, _=> true
  end .


Search (bool -> bool -> bool).
Theorem equalOr: forall (x:bool) (y:bool), ownOr x y = orb x y.

Proof.
intros.
destruct x.
destruct y.
unfold ownOr.
unfold orb.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
destruct y.
simpl.
reflexivity.
reflexivity.
Qed.

(*Zad2*)
Definition neg (x: bool) : bool :=
  match x with 
  | false => true
  | true => false
  end .
  
Search (bool -> bool).

Theorem dwuident: forall (x:bool) , negb(negb x)=x.

Proof.
intro x.
destruct x.
unfold negb.
trivial.
trivial.
Qed.

(*Zad3*)

Theorem consExt: forall (t : Type), forall (f : t -> t) , (forall (x : t), f x = x) -> (forall (x : t), f (f(x))=x).

Proof.
intros.
rewrite -> H.
rewrite -> H.
trivial.
Qed.

(*Zad 4*)
(*
Theorem cosExtBool: forall(f : bool -> bool),forall (t : bool) ,f(t)=t ->(forall (t:bool) ,f(f(t))=t).

Proof.
intro f.
intro zalozenie.
apply (consExt bool (f zalozenie)).
trivial.
Qed.
*)

(*Zad 5*)

Inductive ints : Type := plus (n : nat) | minus (n : nat).
(* konstruktor plus modeluje, że każda liczba naturalna jest liczba calkowta, a minus, ze kazda liczba przeciwna *)
(* do liczby naturalnej jest liczba calkowita *)

Definition absHelp (x : ints) : nat :=
  match x with
  | plus n => n
  | minus n => n
  end.


Theorem Spr: forall x: ints , Nat.leb 0 (absHelp x)=true.

Print Nat.leb.

Proof.
intros.
unfold Nat.leb.
reflexivity.
Qed.

(*Zad 6*)
Search (bool -> bool).
Theorem eqalKonAlt : forall (x:bool) (y:bool) , orb x y = andb x y -> x=y.

Proof.
intros.
destruct x.
destruct y.
trivial.
discriminate.
destruct y.
discriminate.
trivial.
Qed.

(*Zad 7*)
 Require Import Stdlib.Arith.PeanoNat.


Theorem zad7: forall (x y z m : nat), x+y=z -> m*z=m*x + m*y.
Proof.
  intros.
  rewrite <- H.
  apply Nat.mul_add_distr_l.
 Qed.
 



