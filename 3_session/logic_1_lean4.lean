-- Lean4 codes


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
--                            ⊢ A → C

-- https://leanprover.github.io/theorem_proving_in_lean/tactics.html#basic-tactics

theorem Chain_rule : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C := by
  intros A B C x y
  have H1 : A → B := by
    exact And.left x
  have H2 : B → C := And.right x 
  apply H2
  apply H1
  exact y

#print Chain_rule


theorem impl_and_disj : ∀ (A B : Prop), ( (¬ A) ∨ B ) → A → B := by
  intros A B x
  induction x 
  case inl H1 => intro K1; contradiction;
  case inr H2 => intro; trivial

#print impl_and_disj

open Classical

theorem disj_and_impl : ∀ (A B : Prop), (A → B) → ( (¬ A) ∨ B ) := by
  intros A B x 
  have y := em A  -- "em A" is the inhabitant of a the proposition A ∨ ¬ A  (alternative solution: "have y := begin from em A end")
  cases y 
  case inl H1 => have z : B := (x H1); exact Or.inr z;
  case inr H2 => exact Or.inl H2;

#print disj_and_impl

