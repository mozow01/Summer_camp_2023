Require Import Arith.

(*Szintaxis*)

Inductive Var : Set :=
  | X : nat -> Var.

Inductive Exp : Set := 
  | eqZ : Var -> Exp
  | pl1 : Var -> Exp
  | cat : Exp -> Exp -> Exp
  | lop : Var -> Exp -> Exp.

(* A kifejezések denotációs szemantikája, azaz mit *)

Definition Val := Var -> nat.

Print sumbool.

Print Nat.eq_dec.

Definition Upd (V : Val) (n : nat) (x : Var)  : Val  :=
  match x with 
    | X k =>  fun (y : Var) =>  match y with
                                | X m => match (Nat.eq_dec m k) with
                                          | left _  => n
                                          | right _ => V (X m) 
                                           end
                                end
  end.

Fixpoint For (n : nat) (V : Val)  (T : Val -> Val) : Val :=
  match n with
    | 0          => V
    | S m => T (For m V T)
  end.

Fixpoint ExpDenote (V : Val) (E : Exp) : Val :=
  match E with
    | eqZ x          => Upd V 0 x
    | pl1 x          => Upd V (S (V x)) x
    | cat E1 E2         => ExpDenote (ExpDenote V E1) E2      
    | lop x E => For (V x) V (fun U => ExpDenote U E)
  end.



Lemma eqZDenote : forall (V : Val) (x : Var), ExpDenote V (eqZ x) = Upd V 0 x.
Proof.
intros.
unfold ExpDenote.
auto.
Defined.

Lemma pl1Denote : forall (x : Var) (V : Val), ExpDenote V (pl1 x) = Upd V (S (V x)) x.
Proof.
intros.
unfold ExpDenote.
auto.
Defined.

Lemma catDenote : forall (V : Val) (E1 E2 : Exp), ExpDenote V (cat E1 E2) = ExpDenote (ExpDenote V E1) E2.
Proof.
intros.
induction E1, E2.
all: unfold ExpDenote; auto.
Defined.

Lemma lopDenote : forall (V : Val) (E : Exp) (x : Var), ExpDenote V (lop x E) = For (V x) V (fun U => ExpDenote U E).
Proof.
intros.
induction E.
all: unfold ExpDenote; auto.
Defined.

Lemma pl1Denote_2 : forall (x : Var), (fun U => ExpDenote U (pl1 x)) =  (fun U => Upd U (S (U x)) x).
Proof.
intros.
unfold ExpDenote.
auto.
Defined.

(*
LOOP x1 DO
  x0 := x0 + 1
END;
LOOP x2 DO
  x0 := x0 + 1
END
*)


Definition ADD_LOOP := cat (lop (X 1) (pl1 (X 0)) ) (lop (X 2) (pl1 (X 0))). 

Theorem LOOP_add_correctness : forall V : Val, (ExpDenote V ADD_LOOP) = fun (y : Var) => match y with
                   | X 0 => V (X 1) + V (X 2)
                   | X (S m) => V (X (S m))
                 end.
Proof.
intros.
unfold ADD_LOOP.
rewrite catDenote.
rewrite lopDenote.
rewrite lopDenote.
rewrite pl1Denote_2.
Abort.












