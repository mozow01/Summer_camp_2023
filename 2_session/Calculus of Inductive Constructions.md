# Calculus of Inductive Constructions

Thierry Coquand, Christine Paulin-Mohring implementálták számítógépesen az _Induktív Konstrukciók Kalkulusát_ (CIC, CoC, Coq), ami Peer Martin-Löf típuselméletének átdolgozása. 

## Természetes számok (nat)

Alappélda

_Konstruktorok:_

<img src="https://i.upmath.me/svg/0%3A%5Ctext%7Bnat%7D" alt="0:\text{nat}" />

<img src="https://i.upmath.me/svg/S%3A%20%5Ctext%7Bnat%7D%5Cto%20%5Ctext%7Bnat%7D" alt="S: \text{nat}\to \text{nat}" />

"Szemléletesen, egy induktívan definiált típus konstruktorok egy teljes listája által adott. A nekik megfelelő indukciós elvvel érvelünk a típus elemeivel kapcsolatban és a konstruktorokon függvényeket adunk meg, amik alkamasak az egész típus felett értelmezett primitív rekurzív függvények definiálására." (Christine Paulin-Mohring, 1990)

_Indukciós szabály:_

<img src="https://i.upmath.me/svg/%5Cdfrac%7B%5Cforall%20P%20%3A%20%5Ctext%7Bnat%7D%20%5Cto%20%5Ctext%7BProp%7D%2C%5Cquad%20%0A%20%20%20%20%20%20%20P%200%2C%20%5Cquad%20(%5Cforall%20n%20%3A%20%5Ctext%7Bnat%7D%2C%20P%20n%20%5Cto%20P%20(S%20n))%7D%7B%5Cforall%20n%20%3A%20%5Ctext%7Bnat%7D%2C%20P%20n%7D%0A" alt="\dfrac{\forall P : \text{nat} \to \text{Prop},\quad 
       P 0, \quad (\forall n : \text{nat}, P n \to P (S n))}{\forall n : \text{nat}, P n}
" />


## Egyszerű bináris fák, a leveleken természetes számok

_Konstruktorok:_

<img src="https://i.upmath.me/svg/%5Cfrac%7B%20n%3A%5Ctext%7Bnat%7D%7D%7B%5Ctext%7Bleaf%20%7D%20n%3A%20%5Ctext%7BTree%5C_nat%7D%7D" alt="\frac{ n:\text{nat}}{\text{leaf } n: \text{Tree\_nat}}" />

<img src="https://i.upmath.me/svg/%5Cfrac%7B%20t1%3A%5Ctext%7BTree%5C_nat%7D%2C%5Cqquad%20t2%3A%5Ctext%7BTree%5C_nat%7D%7D%7B%5Ctext%7Bnode%20%7Dt1%5C%2C%20t2%20%3A%20%5Ctext%7BTree%5C_nat%7D%7D" alt="\frac{ t1:\text{Tree\_nat},\qquad t2:\text{Tree\_nat}}{\text{node }t1\, t2 : \text{Tree\_nat}}" />

_Indukciós szabály:_

<img src="https://i.upmath.me/svg/%5Cfrac%7BP%20%3A%5Ctext%7BTree%5C_nat%7D%5Cto%5Ctext%7BProp%7D%2C%5Cqquad%20%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(%5Ctext%7Bleaf%20%7Dn)%2C%5Cquad%20%5Cforall%20t%2Ct_0%3A%20%5Ctext%7BTree%5C_nat%7D%2C%20P%20t%20%5Cto%20P%20t_0%20%5Cto%20P%20(%5Ctext%7Bnode%20%7Dt%5C%2Ct_0))%20%7D%7B%5Cforall%20t%20%3A%20%5Ctext%7BTree%5C_nat%7D%2C%20P%20t%7D" alt="\frac{P :\text{Tree\_nat}\to\text{Prop},\qquad \forall n:\text{nat}, P(\text{leaf }n),\quad \forall t,t_0: \text{Tree\_nat}, P t \to P t_0 \to P (\text{node }t\,t_0)) }{\forall t : \text{Tree\_nat}, P t}" />








