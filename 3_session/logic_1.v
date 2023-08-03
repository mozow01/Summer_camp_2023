Theorem Chain_rule : forall A B C : Prop, ((A -> B) /\ (B -> C)) -> A -> C.
Proof.
intros A B C x y.
destruct x as [H1 H2].

Admitted.

Search bool.

Print orb.

Parameter x : bool.

Eval compute in (orb x true).

Theorem classical_impl_or : forall x y : bool,
orb (negb x) y = implb x y.
Proof.
intros x y.
Print bool_ind.
induction x.
induction y.
all: compute; auto. 
Defined.

Theorem imp_disj : forall A B, (~ A) \/ B -> (A -> B). 
Proof. 
intros.
destruct H as [H1|H2].
contradiction.
auto.
Qed.

Theorem LEM : forall A : Prop, (A \/ ~ A).
Admitted.

Inductive Fals : Type := .

Print Fals_sind.

Print True_rect.

Print False.
Print False_rect.
Print bool_ind.

Theorem disj_imp : forall A B : Prop, (A \/ ~ A) -> (A -> B) -> ((~ A) \/ B). 
Proof. 
intros.
destruct H as [H1|H2].
right; auto.
left; auto.
Qed.





