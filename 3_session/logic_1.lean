-- Chain rule for →  

-- (A → B) ∧ (B → C)
-- ------------------
--       A → C

-- The idea of the proof:

-- A ⊢  (A → B) ∧ (B → C)            
-- -----------------                   
--    A ⊢   A → B           A ⊢ A        A ⊢  (A → B) ∧ (B → C)
--  -------------------------------       -----------------
--                 A  ⊢ B                      A ⊢   B → C
--          ------------------------------------------------
--                              A ⊢ C
--                           -----------
--                              A → C

-- https://leanprover.github.io/theorem_proving_in_lean/tactics.html#basic-tactics




theorem Chain_rule : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C :=
begin
intros A B C x,
have H1 : A → B :=
begin
from and.left x,
end,
have H2 : B → C := and.right x,
intros y,
apply H2,
apply H1,
exact y,
end

#print Chain_rule

-- above from the term of conjunction type two new hypotheses were infered and added to the premisses

-- a different strategy: decompose the term of conjunction type into two hypotheses directly

theorem Chain_rule_2 : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C :=
begin
intros A B C x,
cases x, -- "cases" is an awkward name, bc there is no proof by cases here
intros y,
apply x_right,
apply x_left,
exact y,
end

#print Chain_rule_2

theorem impl_and_disj : ∀ (A B : Prop), ( (¬ A) ∨ B ) → A → B :=
begin
intros A B x,
cases x with y z, -- igazi esetszétválasztás
intros w,
contradiction,
intros w,
from z,
end

open classical

theorem disj_and_impl : ∀ (A B : Prop), (A → B) → ( (¬ A) ∨ B ) :=
begin
intros A B x,
have y : A ∨ ¬ A := em A, -- em A a "bizonyítása" A ∨ ¬ A -nak
cases y with H1 H2,
right,
apply x, exact H1,
left,
exact H2,
end

