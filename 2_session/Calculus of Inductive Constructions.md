# Calculus of Inductive Constructions

Thierry Coquand, Christine Paulin-Mohring implementálták számítógépesen az _Induktív Konstrukciók Kalkulusát_ (CIC, CoC, Coq), ami Peer Martin-Löf típuselméletének átdolgozása. 

## Természetes számok (nat)

Alappélda

_Konstruktorok:_

<img src="https://i.upmath.me/svg/0%3A%5Ctext%7Bnat%7D" alt="0:\text{nat}" />

<img src="https://i.upmath.me/svg/S%3A%20%5Ctext%7Bnat%7D%5Cto%20%5Ctext%7Bnat%7D" alt="S: \text{nat}\to \text{nat}" />

_Indukciós szabály:_

<img src="https://i.upmath.me/svg/%5Cdfrac%7B%5Cforall%20P%20%3A%20%5Ctext%7Bnat%7D%20%5Cto%20%5Ctext%7BProp%7D%2C%5Cquad%20%0A%20%20%20%20%20%20%20P%200%2C%20%5Cquad%20(%5Cforall%20n%20%3A%20%5Ctext%7Bnat%7D%2C%20P%20n%20%5Cto%20P%20(S%20n))%7D%7B%5Cforall%20n%20%3A%20%5Ctext%7Bnat%7D%2C%20P%20n%7D%0A" alt="\dfrac{\forall P : \text{nat} \to \text{Prop},\quad 
       P 0, \quad (\forall n : \text{nat}, P n \to P (S n))}{\forall n : \text{nat}, P n}
" />


"Szemléletesen, egy induktívan definiált típus konstruktorok egy teljes listája által adott. A nekik megfelelő indukciós elvvel érvelünk a típus elemeivel kapcsolatban és a konstruktorokon függvényeket adunk meg, amik alkamasak az egész típus felett értelmezett primitív rekurzív függvények definiálására." (Christine Paulin-Mohring, 1990)

