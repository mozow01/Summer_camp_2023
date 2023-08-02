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

--  egy másik stratégiával szétszedjük a feltételt

theorem Chain_rule_2 : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C :=
begin
intros A B C x,
cases x,
intros y,
apply x_right,
apply x_left,
exact y,
end

#print Chain_rule_2


