Require Import List.
Require Import Bool.

(*Ezek a programok definiálnak egy tárgynyelvet, ami a Boole-algebra negációt és konjunkciót tartalmazó fragmentuma. Majd megadják a szemantikáját. Ezek után egy gépet (veremautómatát) veszünk, amelyik iperatív stílusban programok futtatásával számolja ki a Boole-értéket. A képzeletbeli stack-machine-t a tárnyelv kifejezéseinek programokká való leforsításával lehet etetni és az eredmény, amit a stack-machine kiköp.*)

(*Tárgynyelv: negáció, konjunkció, kifejezések*)

Inductive unop : Set :=
  | NEG : unop.

Inductive binop : Set :=
  | AND : binop.

Inductive Exp : Set :=
  | Const : bool -> Exp
  | Neg : unop -> Exp -> Exp
  | And : binop -> Exp -> Exp -> Exp.

(*Szemantika: maga az ExpDenote nevű definíció az úgy nevezett "jelentése" (russelliánus értelemben: denotáló komplexusa) a nyelv kifejezéseinek, a kifejezések denotációját (értékét) a jelentések jelölik ki. Maga az ExpDenote(E) értékek a denotációk. Az értékek a Coq natív nyelvének szavai, ezért itt most akát metanyelvi fordításról is beszélhetünk.*)

Fixpoint ExpDenote (E : Exp) : bool :=
  match E with
    | Const b => b
    | Neg x E1 => negb (ExpDenote E1)
    | And y E1 E2 => andb (ExpDenote E1) (ExpDenote E2)
  end.

(*Ez a program bizonyítja (nem teljes a bizonyítás, de végigvihető), hogy az "AND (Neg NEG e) e" kifejezés denotációja mindig a "false".*)

(*Figyeljünk fel a "SearchRewrite (negb (negb _))." keresőkifejezésre, ami az rewrite taktikához keres olyan, már létező lemmát, az adott helyzetben alkalmazhatnábk.*)

Theorem ContradictionDenote : forall e, ExpDenote(And AND (Neg NEG e) e) = false.
Proof.
intros.
induction e.
induction b; unfold ExpDenote; simpl; auto.
simpl.
simpl in IHe.
SearchRewrite (negb (negb _)).
rewrite negb_involutive.
SearchRewrite (andb _ _ ).
rewrite andb_comm.
auto.
simpl.
simpl in IHe1,IHe2.
SearchRewrite (negb (andb _ _)).
rewrite negb_andb.
Abort.

(*Nem kötelező, hogy a tárgynyelv szándékolt jelentése legyen a metanyelvi jelentés. Lehetnénak a bool helyett Prop-ok is a denotációk, és így sokkal egyszerűbbé válnának a bizonyítások, mert a Coq a Prop-okkal való számolásban van igazán elemében.*)

Fixpoint ExpDenote2 (E : Exp) : Prop :=
  match E with
    | Const b => if true then True else False
    | Neg x E1 => ~ (ExpDenote2 E1)
    | And y E1 E2 => (ExpDenote2 E1) /\ (ExpDenote2 E2)
  end.

Theorem FalseDenote2 : forall e, ~ (ExpDenote2(And AND (Neg NEG e) e)).
Proof.
induction e.
induction b.
simpl.
firstorder.
simpl.
firstorder.
simpl.
simpl in IHe.
firstorder.
simpl.
simpl in IHe1, IHe2.
firstorder.
Qed.

(*A képzeletbeli stack machine-t vezértő utasítások nyelve, programjai és a stack tartalma*)

Inductive instr : Set :=
  | iConst : bool -> instr
  | iNeg : unop -> instr
  | iAnd : binop -> instr.

Definition prog := list instr.
Definition stack := list bool.

(*Kifejezések fordítása a stack machine számára*)

Fixpoint compile (E : Exp) : prog :=
  match E with
    | Const b => iConst b :: nil
    | Neg x e  => compile e ++ iNeg x :: nil
    | And y e1 e2 => compile e2 ++ compile e1 ++ iAnd y :: nil
  end.

(*A gép elemi működése*)

Definition machine (i : instr) (s : stack) : option stack :=
  match i with
    | iConst b => Some (b :: s)
    | iNeg x =>
      match s with
        | b :: s' => Some ((negb b) :: s')
        | _ => None
      end
    | iAnd y =>
      match s with
        | b1 :: b2 :: s' => Some (((andb b1 b2)) :: s')
        | _ => None
      end
  end.

(*Program futtatása a gépen*)


Fixpoint engine_aux (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match machine i s with
        | None => None
        | Some s' => engine_aux p' s'
      end
  end.

Definition engine (p : prog) : option stack := engine_aux p nil.



