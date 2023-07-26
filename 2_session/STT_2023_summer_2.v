(*
******************
Természetes számok
******************
*)

Print nat_ind.


(*Taktika a nat-ban való számolásra. Azon alapul, hogy a Presburger-aritmetika (N,+) _eldönthető_ axiómarendszer.*)

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
compute.
reflexivity.
simpl.
simpl in IHn.
Time lia.
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
all: auto.

Qed.

(*
****************
Polimorf fatípus
****************

(a típus típusfüggő)

*)

Inductive Tree_Type (A: Set) : Type :=
  | tleaf : A -> Tree_Type A
  | tnode : Tree_Type A -> Tree_Type A -> Tree_Type A.

Print nat_ind.

(*A típuselméletben értelmetlen állítás: 

Theorem forall t : Tree_nat, t : Tree_Type nat.*)

(*Csak úgy lehet, ha ágyazzuk az egyiket a másikba... *)

Fixpoint beagy (t:Tree_nat) : Tree_Type nat := 
match t with
  | leaf m => tleaf nat m
  | node t1 t2 => tnode nat (beagy t1) (beagy t2)
end.

(*... vagy a másikat az egyikbe: *)

Fixpoint kiagy (t:Tree_Type nat) : Tree_nat := 
match t with
  | tleaf _ m => leaf m
  | tnode _ t1 t2 => node (kiagy t1) (kiagy t2)
end.

(*Komputálja legyen szíves a beagy függvényt*)

Eval compute in beagy (node (leaf 1) (leaf 2)).



(*Mivel ez kölcsönösen megtehető, ezért felvetődik a kérdés, hogy ez a két típus "izomorf". Izomorfnak nevezzük az A típust a B-vel, ha vannak u:A -> B és v:B -> A, hogy (u(v(x))=x és v(u(y))=y. Ezt tételbenis kimondjuk:*)

Theorem izomorfia : (forall t : Tree_nat,  kiagy(beagy t) = t) /\ (forall t : Tree_Type nat,  beagy(kiagy t) = t).
Proof.
intuition.
induction t.
all: auto.
simpl.
rewrite IHt1.
rewrite IHt2.
reflexivity.
induction t.
all: auto.
simpl.
rewrite IHt1.
rewrite IHt2.
reflexivity.
Qed.


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


