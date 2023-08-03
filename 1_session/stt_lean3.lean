

-- Simple type theory wit Nameless Dummies

-- Típusok nyelve
inductive Typ : Type
  | Iota : Typ
  | Arrow : Typ → Typ → Typ


/- Változók: nameless dummies :)

Nincsenek explicit változók, csak indexek, amik azt mondják meg, hogy a
kontextus hanyadik eleme az illető implicit 'változó'.
-/

-- A kontextusok típusok listái, a művelet a kontextuskibővítés
--(balról hozzáfűzünk a listához egy új elemet, ez a ::)
def Cntxt := list Typ


-- Külön vannak kifejezések (terminusok, termek)
inductive Trm : Type 
  | ind : nat → Trm
  | app : Trm → Trm → Trm
  | lam : Typ → Trm → Trm

open Trm

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


inductive Tyty : Cntxt → Trm → Typ → Prop 
  | Ty_ind0 (Γ : Cntxt) (A : Typ) :
      Tyty (A :: Γ) (ind 0) A
  | Ty_indS (Γ : Cntxt) (A B : Typ) (i : nat) : 
      Tyty Γ (ind i) A → Tyty (B :: Γ) (ind (nat.succ i)) A
  | Ty_app (Γ : Cntxt) (A B : Typ) (t s : Trm) : 
      Tyty Γ t (Typ.Arrow A B) → Tyty Γ s A → Tyty Γ (Trm.app t s) B
  | Ty_lam (Γ : Cntxt) (A B : Typ) (t : Trm) : 
      Tyty (A :: Γ) t B → Tyty Γ (lam A t) (Typ.Arrow A B)


open Tyty

theorem First_typeability_rule_for_snd_term : 
∀ Γ : Cntxt, ∀ A B : Typ, Tyty (A :: (B :: Γ)) (ind 1) B := 
begin
intros,
have H1 : Tyty (B :: Γ) (ind 0) B := 
  begin 
    exact Ty_ind0 Γ B, 
  end,
  
end