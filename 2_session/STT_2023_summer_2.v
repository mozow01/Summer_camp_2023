(*
******************
Természetes számok
******************
*)

Print nat_ind.

(*Taktika a nat-ban való számolásra. Azon alapul, hogy a Presburget-aritmetika (N,+) _eldönthető_ axiómarendszer.*)

Require Import Lia.

(*Egyszerű példa, az első n természetes szám összege...*)

Fixpoint összeg (n:nat) :=
match n with 
  | 0 => 0
  | S n => (összeg n) + S n
end.

(*... és a rá vonatkozó nevezetes tétel.*)

Theorem első_n_szám_összege : forall n, 2*(összeg n) = n*(n+1).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
simpl in IHn.
lia.
Show Proof.
Qed.

(* 
********************
Egyszerű bináris fák
********************

rögzítet típusból jönnek a levelek értékei (nem függő típus)

*)

Inductive Tree_nat : Set :=
  | leaf : nat -> Tree_nat
  | node : Tree_nat -> Tree_nat -> Tree_nat.

Print Tree_nat_ind.

Fixpoint Tree_nat_sum (t:Tree_nat) :=
match t with 
  | leaf m => m
  | node t1 t2 => (Tree_nat_sum t1) + (Tree_nat_sum t2)
end.

Theorem összegtétel : forall t1 t2 : Tree_nat, Tree_nat_sum (node t1 t2) = (Tree_nat_sum t1) + (Tree_nat_sum t2).
Proof.
intros.
induction t1, t2.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(*
****************
Polimorf fatípus
****************

(a típus típusfüggő)

*)

Inductive Tree_Type : Type :=
  | tleaf : forall A: Set, A -> Tree_Type
  | tnode : Tree_Type -> Tree_Type -> Tree_Type.

Print nat_ind.

(*A típuselméletben értelmeteln állítás:

Theorem forall t : Tree_nat, t : Tree_Type nat.*)

(*Csak úgy lehet, ha ágyazzuk az egyiket a másikba:*)

Fixpoint beagy (t:Tree_nat) : Tree_Type := 
match t with
  | leaf m => tleaf nat m
  | node t1 t2 => tnode (beagy t1) (beagy t2)
end.

(*Komputálja legyen szíves a beagy függvényt*)

Eval compute in beagy (node (leaf 1) (leaf 2)).


(*
***********************************
Függő (dependens/dependent) fatípus
***********************************

(a típus termfüggő)

*)

Inductive hTree : nat -> Set :=
  | hleaf : hTree 0
  | hnode : forall n:nat, hTree n -> hTree n -> hTree (S n).

Print Nat.max.

Fixpoint hTree_height (n:nat) (t:hTree n) :=
match t with 
  | hleaf => 0
  | hnode n t1 t2 => Nat.max (hTree_height n t1) (hTree_height n t2) + 1
end.

Theorem magasságtétel : forall (n : nat) (t : hTree n), hTree_height n t = n.
Proof.
intros.
induction t.
simpl.
reflexivity.
simpl.
lia.
Qed.

(*
*****************
Bizonyítástípusok
*****************
*)

Print and.
Print and_ind.

Print prod.
Print prod_ind.

