(*
FOL [T, ->, /\, exists] (mert nekem még csak ennyi kell), Bruijn-számozással kezelt individumtermekkel, bizonyítástermek nélkül, a kétváltozós Γ ⊢ A levezetésrelációval. Később bővítendő Bruijn-számozással kezelt levezetéstermekkel és a háromváltozós Γ ⊢ p : A levezetésrelációval.

TODO néhány kvantoros levezetéses példa és a helyettesítés lemmái

*)

Require Import List.
Require Import Arith.
Require Import Vector.

Structure Sig := mkSig {
c_sym : Set;
f_sym : Set;
r_sym : Set;
f_dim : f_sym -> nat;
r_dim : r_sym -> nat;
}.

Context {σ : Sig}.


Inductive Trm : Set  :=
  | ind : nat -> Trm   
  | mk_c : (@c_sym σ) -> Trm
  | mk_f : forall (f : (@f_sym σ)) (v : t Trm ((@f_dim σ) f)), Trm 
with Frm : Set :=
  | top : Frm
  | conj : Frm -> Frm -> Frm 
  | arr : Frm -> Frm -> Frm 
  | ex : Frm -> Frm 
  | mk_r : forall (r : (@r_sym σ)) (v : t Trm ((@r_dim σ) r)), Frm.

Definition Cntx_F := list Frm.


(*Individuumtermek k. szabad változóját és ettől fölfelé minden szabad változót liftel n-nel*)

Fixpoint lift_aux_tr (n : nat) (t : Trm) (k : nat) : Trm :=
   match t with
     | ind i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) ind (i + n)
                  | right _ => (* k > i *) ind i
                end
     | mk_c x => mk_c x
     | mk_f f v => mk_f f (@map Trm Trm (fun t => lift_aux_tr n t k) ((@f_dim σ) f) v)
   end.

(*Individuumtermek minden szabad változójának liftelése n-nel*)

Definition lift_tr t1 n := lift_aux_tr n t1 0.

(* Az alábbi függvény egy termsorozat minden elemét lifteli (azaz a benne szereplő szabad bizonyításváltozók indexét emeli eggyel.) *)

Definition lift_seq_tr (s : nat -> Trm) (k : nat) : Trm :=
  match k with 
     | 0 => lift_tr (s 0) 1
     | S m => lift_tr (s (S m)) 1
  end.
  
(* Eltol egy termsorozatot 1-gyel és az első helyre berakja a ind 0-t. *)

Definition shift_seq_tr (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => ind 0
     | S m => (s m)
  end.

(* A t term n-edik szabad változója helyére az s termsorozat n. elemét helyettesíti *)

Fixpoint subst_aux_tr (t : Trm) (n : nat) (s : nat -> Trm) {struct t} : Trm :=
match t with
     | ind i => match (Nat.eq_dec n i)  with 
                 | left _ => s n
                 | right _ => ind i
                end
     | mk_c x => mk_c x
     | mk_f f v => mk_f f (@map Trm Trm (fun t => subst_aux_tr t n s) ((@f_dim σ) f) v)
   end.

(* Ugyenez 0-val. *)
  
Definition subst_tr t s := subst_aux_tr t 0 s.

(* Ugyanez, azzal a sorozattal, amikor a 0. elem t, a többi irreleváns *)

Definition subs_tr t r := subst_aux_tr t 0 (fun k : nat => 
match k with | 0 => r | S _ => ind 0 end).

Fixpoint subst_aux_fr (A : Frm) (n : nat) (s : nat -> Trm) {struct A} : Frm :=
match A with
      | top => top
      | conj B C => conj (subst_aux_fr B n s) (subst_aux_fr C n s) 
      | arr B C => arr (subst_aux_fr B n s) (subst_aux_fr C n s) 
      | ex B => ex (subst_aux_fr B (S n) (shift_seq_tr ( lift_seq_tr s)))
      | mk_r r v => mk_r r (@map Trm Trm (fun t => subst_aux_tr t n s) ((@r_dim σ) r) v)
end.

Definition subst_fr A s := subst_aux_fr A 0 s.



(* Ugyanez, azzal a sorozattal, amikor a 0. elem t, a többi irreleváns *)

Definition subs_form A r := subst_aux_fr A 0 (fun k : nat => 
match k with | 0 => r | S _ => ind 0 end).

(*Formulák k. szabad változóját és ettől fölfelé minden szabad változót liftel n-nel*)

Fixpoint lift_aux_fr (n : nat) (A : Frm) (k : nat) : Frm :=
   match A with
      | top => top
      | conj B C => conj (lift_aux_fr n B k) (lift_aux_fr n C k) 
      | arr B C => arr (lift_aux_fr n B k) (lift_aux_fr n C k) 
      | ex B => ex (lift_aux_fr n B (S k))
      | mk_r r v => mk_r r (@map Trm Trm (fun t => lift_aux_tr n t k) ((@r_dim σ) r) v)
   end.

Definition lift_fr n (A : Frm) := lift_aux_fr n A 0.

Definition lift_form (A : Frm) := lift_aux_fr 1 A 0.

Print list.


Fixpoint lift_cntx (Γ : Cntx_F) {struct Γ} : Cntx_F := 
  match Γ with
    | List.nil => List.nil
    | A :: l => (lift_form A) :: lift_cntx l
  end.

Eval compute in lift_cntx (top :: top :: List.nil).


Inductive Prov : Cntx_F -> Frm -> Prop :=
  | ND_hypO : forall Γ A, Prov (A :: Γ) A
  | ND_hypS :
      forall Γ A B,
      Prov Γ A -> Prov (B :: Γ) A
  | ND_top : forall Γ, Prov Γ top
  | ND_imp_intro : forall Γ A B,
      Prov (A :: Γ) B -> Prov Γ (arr A B)
  | ND_imp_elim :
      forall Γ A B,
      Prov Γ (arr A B) -> Prov Γ A -> Prov Γ B 
  | ND_conj_intro :
      forall Γ A B,
      Prov Γ A -> Prov Γ B -> Prov Γ (conj A B) 
  | ND_conj_left :
      forall Γ A B,
      Prov Γ (conj A B) -> Prov Γ A 
  | ND_conj_right :
       forall Γ A B,
      Prov Γ (conj A B) -> Prov Γ B
  | ND_ex_intro :
      forall Γ A t, Prov Γ (subs_form A t) -> Prov Γ (ex A)   
  | ND_ex_elim : 
      forall Γ A B,  Prov Γ (ex A) -> Prov (A :: lift_cntx Γ) (lift_form B) -> Prov Γ B.






