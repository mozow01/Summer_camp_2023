-- Simple type theory wit Nameless Dummies

-- Típusok nyelve
inductive Typ : Type where
  | Iota : Typ
  | Arrow : Typ → Typ → Typ

notation:70 "ι" => Typ.Iota
notation:70 lhs:70 " ⇒ " rhs:70 => Typ.Arrow lhs rhs

#check ι ⇒ ι

/- Változók: nameless dummies :)

Nincsenek explicit változók, csak indexek, amik azt mondják meg, hogy a
kontextus hanyadik eleme az illető implicit 'változó'.
-/

-- A kontextusok típusok listái, a művelet a kontextuskibővítés
--(balról hozzáfűzünk a listához egy új elemet, ez a ::)
def Cntxt := List Typ


-- Külön vannak kifejezések (terminusok, termek)
inductive Trm : Type where
  | ind : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Typ → Trm → Trm

open Trm
notation:30 lhs:30 " $ " rhs:30 => Trm.app lhs rhs

/- Mivel itt bizonyításokról, levezetsekről van szó (és ez szemléletesebb is),
ezért an n-edik változót 

ind n 

jelöli. Ez viszont nem egy abszolút sorszám, hanem egy relatív. A Γ =
A_0::A_1::A_2::...::nil kontextusban ind 0 pl. az lista első elemére, az A_0
típusúváltozóra mutat. Ha Γ bővül egy elemmel, a sorrendek eltolódnak 1-gyel. 

lam-nál meg kell jelölni, hogy milyen típusú termet absztrahál, azaz lam egy Typ
-> Trm -> Trm típusú lesz.

app problémamentes
-/

inductive Tyty : Cntxt → Trm → Typ → Prop where
  | Ty_ind0 (Γ : Cntxt) (A : Typ) :
      Tyty (A :: Γ) (ind 0) A
  | Ty_indS (Γ : Cntxt) (A B : Typ) (i : Nat) : 
      Tyty Γ (ind i) A → Tyty (B :: Γ) (ind (Nat.succ i)) A
  | Ty_app (Γ : Cntxt) (A B : Typ) (t s : Trm) : 
      Tyty Γ t (A ⇒ B) → Tyty Γ s A → Tyty Γ (t $ s) B
  | Ty_lam (Γ : Cntxt) (A B : Typ) (t : Trm) : 
      Tyty (A :: Γ) t B → Tyty Γ (lam A t) (A ⇒ B)
open Tyty
notation:20 Γ:20 " ⊢ " t:20 " [:] " A:20 => Tyty Γ t A
notation:20 " ⊢ " t:20 " [:] " A:20 => Tyty [] t A


-- Ezzel azt mondjuk, hogy a simp taktika próbálkozzon ezekkel a levezetési lépésekkel is,
-- név szerint a De Bruijn-indexekkel kapcsolatos komputációkat is elvégzi.
attribute [simp] Ty_ind0
attribute [simp] Ty_indS

theorem First_typeability_rule_for_snd_term (Γ : Cntxt) (A B : Typ) : 
  A :: B :: Γ ⊢ (ind 1) [:] B := by
--   apply Ty_indS
--   apply Ty_ind0
-- vagy rövidebben
--   simp [Ty_ind0, Ty_indS]
-- vagy még rövidebben
  simp

theorem Chain_rule : ∀ (A B C : Typ), ∃ (P : Trm),
  A ⇒ B :: B ⇒ C :: [] ⊢ P [:] A ⇒ C := by
    intros A B C
    exists (lam A (ind 2 $ ind 1 $ ind 0))
    apply Ty_lam
    apply Ty_app _ B C
    simp
    apply Ty_app _ A B
    all_goals simp