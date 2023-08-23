Require Import List.

(*Shunting yard eljárás prefix és absztrakt szintaxis legyártására (nem fát eredményez,
 mert az redundánsan felesleges bonyolítás a Coq-ban) *)

(*a nyelv karakterei, zárójelek is*)

Inductive char : Set :=
  | letter : nat -> char
  | lp : char
  | rp : char
  | binop : nat -> char
  | unop : nat -> char.

(*prefix csináló, ebből a traziciós függvény, ami a SYA egy lépését végzi el*)

Definition machine (x y z : list char) : list char * list char * list char :=
  match (rev x) with 
    | nil => (nil, nil, nil)
    | a::l => match a with
                 | letter n => (rev l, y, (letter n)::z)
                 | rp => (rev l, rp::y, z)
                 | binop n => (rev l, (binop n)::y, z)
                 | unop n => (rev l, (unop n)::y, z)
                 | lp => match y with
                           | (binop n)::rp::k => (rev l, k, (binop n)::z)
                           | (unop n)::rp::k => (rev l, k, (unop n)::z)
                           | _ => (nil, nil, nil)
                         end
              end
  end. 

(*Példákok*)

(*     (((3+4)+(-5))*6)            *)

Eval compute in (machine (lp::(letter 1)::(binop 1)::(letter 2)::rp::nil) nil nil).

Eval compute in (machine (lp :: letter 1 :: binop 1 :: letter 2 :: nil) (rp::nil) nil).

(* Eval simpl in (machine (binop 1 :: letter 1 :: lp :: nil) (rp::nil) (letter 2 :: nil) ).

Eval simpl in (machine (letter 1 :: lp :: nil) (binop 1 :: rp :: nil) (letter 2 :: nil) ).

Eval simpl in (machine (lp :: nil) (binop 1 :: rp :: nil) (letter 1 :: letter 2 :: nil) ).

Print option. *)

(*prefix csináló, traziciós függvény opció típussal, 
ha nem jól zárójelezett, vagy üres a bemebnet, akkor None *)

Definition machine' (x y z : list char) : option (list char * list char * list char) :=
  match (rev x) with 
    | nil => None
    | a::l => match a with
                 | letter n =>  Some (l, y, (letter n)::z)
                 | rp => Some (l, rp::y, z)
                 | binop n => Some (l, (binop n)::y, z)
                 | unop n => Some (l, (unop n)::y, z)
                 | lp => match y with
                           | (binop n)::rp::k => Some (l, k, (binop n)::z)
                           | (unop n)::rp::k => Some (l, k, (unop n)::z)
                           | _ => None
                         end
              end
  end.

Definition machine'' (x y z : list char) (w : option char) : option (list char * list char * list char * char) :=
  match (rev x) with 
    | nil => None
    | a::l => match a with
                 | rp => match w with 
                            | None | Some (binop _) | Some rp => Some (l, rp::y, z, rp )
                            | _ => None
                         end
                 | letter n => match w with 
                            | None | Some (binop _) | Some rp => Some (l, y, (letter n)::z, letter n )
                            | _ => None
                         end 
                        
                 | binop n => match w with 
                            | Some (letter _) | Some lp => Some (l, (binop n)::y, z, binop n )
                            | _ => None
                         end 

                 | unop n => match w with 
                            | Some (letter _) | Some lp => Some (l, (unop n)::y, z, unop n )
                            | _ => None
                         end 


                 | lp => match w with 
                            | Some (letter _) | Some lp | Some (unop _) => match y with
                                                                   | (binop n)::rp::k => Some (l, k, (binop n)::z, lp )
                                                                   | (unop n)::rp::k => Some (l, k, (unop n)::z, lp )
                                                                   | _ => None
                                                                           end
                            | _ => None
                         end
              end
  end.

(*A motor működteti a tranzíciós folyamatot, t az imput méretének felső korlátja, 
ami majd a feldolgozandó hossza lesz*)

Fixpoint engine'' (t : nat) (i : option (list char * list char * list char * option char)) {struct t} :=
  match t with
    | 0 => i
    | S t' => match i with
                | None => None
                | Some (x, y, z, w) => match (machine'' x y z w ) with
                                      | Some (a,b,c,d) => engine'' t' (Some (rev a, b, c, Some d))
                                      | None => None
                                    end
              end
  end.

Definition Engine (expr : list char) := 
match engine'' (length expr) (Some (expr, nil, nil, None)) with
  | Some ( _ , _ , out, _) => Some out
  | None => None
end.


Eval compute in (Engine (lp::(letter 1)::(unop 1)::rp::nil)).

Eval compute in (Engine (lp::(binop 1)::(letter 1)::(letter 2)::rp::nil)).

Eval compute in 
(Engine (lp::(unop 1)::lp::lp::(letter 1)::(binop 1)::(letter 2)::rp::binop 2::(letter 3)::rp::rp::nil)).




Fixpoint engine' (t : nat) (i : option (list char * list char * list char)) {struct t} 
: option (list char * list char * list char) :=
  match t with
    | 0 => i
    | S t' => match i with
                | None => None
                | Some (x, y, z) => match (machine' x y z) with
                                      | Some (a,b,c) => engine' t' (Some (rev a, b, c))
                                      | None => None
                                    end
              end
  end.


(*szép engine*)

Definition engine (expr : list char) := 
match engine' (length expr) (Some (expr, nil, nil)) with
  | Some ( _ , _ , out) => Some out
  | None => None
end.

(*Példákok*)

Eval compute in 
(engine (lp::(unop 1)::lp::lp::(letter 1)::(binop 1)::(letter 2)::rp::binop 2::(letter 3)::rp::rp::nil)).

Eval compute in (engine (lp::(unop 1::nil))).

(*AST-k típusa*)

Inductive AST : Set :=
  | Letter : nat -> AST
  | Binop : nat -> AST -> AST -> AST
  | Unop : nat -> AST -> AST.

(*AST-ből könnyen lehet, amúgy infixet csinálni*)

Fixpoint AST_to_infix (t : AST) : list char := 
match t with 
  | Letter n => (letter n::nil)
  | Binop n t1 t2 => lp::nil ++ (AST_to_infix t1) ++ (binop n)::nil ++ (AST_to_infix t2) ++ rp::nil
  | Unop n t => lp::nil ++ (unop n)::nil ++ (AST_to_infix t) ++ rp::nil
end.

(*AST-t már nehezebb, ezt is két lépésben*)

Definition machine_infix_AST (x y : list char) (z : list AST) : 
option (list char * list char * list AST) :=
  match (rev x) with 
    | nil => None
    | a::l => match a with
                 | letter n =>  Some (l, y, (Letter n)::z)
                 | rp => Some (l, rp::y, z)
                 | binop n => Some (l, (binop n)::y, z)
                 | unop n => Some (l, (unop n)::y, z)
                 | lp => match y with
                           | (unop n)::rp::k => match z with 
                                                  | b::w => Some (l, k, ((Unop n) b)::w)
                                                  | _ => None
                                                end
                           | (binop n)::rp::k => match z with 
                                                  | b::c::w => Some (l, k, ((Binop n) b c)::w)
                                                  | _ => None
                                                end 
                           | _ => None
                         end
              end
  end.

Fixpoint engine_infix_AST' (t : nat) (i : option (list char * list char * list AST)) {struct t} 
: option (list char * list char * list AST) :=
  match t with
    | 0 => i
    | S t' => match i with
                | None => None
                | Some (x, y, z) => match (machine_infix_AST x y z) with
                                      | Some (a,b,c) => engine_infix_AST' t' (Some (rev a, b, c))
                                      | None => None
                                    end
              end
  end.

Definition engine_infix_AST (expr : list char) := 
match engine_infix_AST' (length expr) (Some (expr, nil, nil)) with
  | Some ( _ , _ , out) => Some out
  | None => None
end.

(*Példák*)

Eval compute in 
(engine_infix_AST 
(lp::(unop 1)::lp::lp::(letter 1)::(binop 1)::(letter 2)::rp::binop 2::(letter 3)::rp::rp::nil)).

Eval compute in (engine_infix_AST (lp::(letter 1)::(unop 1)::rp::nil)).

(* Próbálkozás, hogy máshogy lehet-e...
Fixpoint Prenfix_AST (expr : list car) : option AST := 
match expr with 
  | nil => None
  | a::exp => match a with
                | letter n => Letter n
                | unop n => (Unop n) (Prenfix_AST exp)
                | 
  | Unop n t => lp::nil ++ (unop n)::nil ++ (AST_infix t) ++ rp::nil
end.
*)





