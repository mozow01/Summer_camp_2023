-------------------------------------------------------------------------------
-- SYNTAX ---------------------------------------------------------------------
-------------------------------------------------------------------------------

---Definition of variables.
-- The variables are indexed by Nat, so we have countably infinite of
-- them, called x[i]
inductive Var : Type where
  | X : Nat → Var

notation:70 "x[" lhs:70 "]" => Var.X lhs

---Definition of expressions.
-- It encodes the main "syntax" of the language.
inductive Exp : Type where
  | eqZ : Var → Exp
  | pl1 : Var → Exp
  | cat : Exp → Exp → Exp
  | lop : Var → Exp → Exp

notation:40 lhs:40 "= 0"                        => Exp.eqZ lhs
notation:40 lhs:40 "+= 1"                       => Exp.pl1 lhs
notation:50 lhs:40 " ; " rhs:40                 => Exp.cat lhs rhs
notation:60 "LOOP " lhs:30 " DO " rhs:30 " END" => Exp.lop lhs rhs


-------------------------------------------------------------------------------
-- SEMANTICS ------------------------------------------------------------------
-------------------------------------------------------------------------------

---Evaluation function which gives the value of a given variable.
-- This function represents the state of the variables during program execution.
def Val : Type := Var → Nat

---Creates a new evaluation without the first variable.
def Tail (V : Val) : Val :=
  fun U => match U with
    | x[i] => V (x[Nat.succ i])

---Helper function to update the value of a given variable to an
---arbitrary value.
-- It transforms an evaluation function into a new one.
def Upd (U : Var) (n : Nat) (V : Val) : Val :=
  match U with
    | x[0]          => fun T => match T with
      | x[0]          => n
      | x[Nat.succ j] => V (x[Nat.succ j])

    | x[Nat.succ i] => fun T => match T with
      | x[0]          => V (x[0])
      | x[Nat.succ j] => Upd (x[i]) n (Tail V) (x[j])

---Helper function for looping.
-- It transforms the evaluation function with T precisely n times.
def Rec (n : Nat) (T : Val → Val) (V : Val) : Val :=
  match n with
    | 0          => V
    | Nat.succ m => T (Rec m T V)

---Function to evaluate an expression with given initial values.
-- It encodes the "semantics" of the language.
def Eval (V : Val) (E : Exp) : Val :=
  match E with
    | x = 0           => Upd x 0 V
    | x += 1          => Upd x (Nat.succ (V x)) V
    | P₁ ; P₂         => Eval (Eval V P₁) P₂         --⟦⟦V ⊢ P₁⟧ ⊢ P₂⟧
    | LOOP x DO P END => Rec (V x) (fun U => Eval U P) V

notation:30 "⟦" lhs:30 "⊢" rhs:30 "⟧" => Eval lhs rhs

---Function to evaluate an expression with zero initial values.
-- Normally it is expected to have variables initialized to zero.
def EvalZero (P : Exp) : Val := ⟦fun _ => 0 ⊢ P⟧
notation:30 "⟦" lhs:30 "⟧" => EvalZero lhs

-------------------------------------------------------------------------------
-- TESTS ----------------------------------------------------------------------
-------------------------------------------------------------------------------

---An example program written in LOOP.
-- It sets the value of X 1 to 2, and X 3 to 0, then copies X 1 to X 3
-- and simultaneously doubles X 1. At the end X 1 = 4 and X 3 = 2.
def test : Exp := 
  x[1] = 0;
  x[1] += 1;
  x[1] += 1;
  x[3] = 0;
  LOOP x[1] DO
    x[3] += 1;
    x[1] += 1
  END

---Test evaluation.
def testval : Val := ⟦test⟧

---Test function to ease checking the output.
def f (i : Nat) : Nat := testval (x[i])

-------------------------------------------------------------------------------
-- PROOFS ---------------------------------------------------------------------
-------------------------------------------------------------------------------

---Check output
theorem thm1 : f 1 = 4 := rfl

theorem thm2 : f 3 = 2 := rfl

#check (V : Val) → (x : Var) →  ⟦V ⊢ (x = 0)⟧

--theorem thm3 (V : Val) (x : Var) : ⟦V ⊢ x = 0⟧ 