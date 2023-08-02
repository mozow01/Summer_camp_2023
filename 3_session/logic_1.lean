 -- Chain rule for →  

theorem Chain_rule : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C :=
begin
intros A B C x,
have H1 : A → B :=
begin
from and.left x,
end,
have H2 : B → C := 
begin
from and.right x,
end,
intros y,
apply H2,
apply H1,
exact y,
end