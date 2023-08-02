Theorem Chain_rule : forall A B C : Prop, ((A -> B) /\ (B -> C)) -> A -> C.
Admitted.

Search bool.

Print orb.

Parameter x : bool.

Eval compute in (orb true x).

Theorem classical_impl : forall x y : bool,
orb (negb x) y = implb x y.
Proof.
intros x y.
induction x.
induction y.
all: simpl; reflexivity. 
Defined.



