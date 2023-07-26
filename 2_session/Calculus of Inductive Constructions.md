# Calculus of Inductive Constructions (CIC)

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

<img src="https://i.upmath.me/svg/%5Cfrac%7BP%20%3A%5Ctext%7BTree%5C_nat%7D%5Cto%5Ctext%7BProp%7D%2C%5Cqquad%20%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(%5Ctext%7Bleaf%20%7Dn)%2C%5Cquad%20%5Cforall%20t%2Ct_0%3A%20%5Ctext%7BTree%5C_nat%7D%2C%20P%20t%20%5Cto%20P%20t_0%20%5Cto%20P%20(%5Ctext%7Bnode%20%7Dt%5C%2Ct_0)%20%7D%7B%5Cforall%20t%20%3A%20%5Ctext%7BTree%5C_nat%7D%2C%20P%20t%7D" alt="\frac{P :\text{Tree\_nat}\to\text{Prop},\qquad \forall n:\text{nat}, P(\text{leaf }n),\quad \forall t,t_0: \text{Tree\_nat}, P t \to P t_0 \to P (\text{node }t\,t_0) }{\forall t : \text{Tree\_nat}, P t}" />

## Bizonyítások típusai

### Kondicionális

Bevezetési és kiküszöbölési szabályok:

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%5CGamma%20%5Cvdash%20P%3AA%5Cto%20B%5Cqquad%20%5CGamma%20%5Cvdash%20Q%3AA%7D%7B%5CGamma%20%5Cvdash%20P%20Q%3AB%7D%2C%5Cqquad%20%5Cfrac%7B%5CGamma%5Ccup%5C%7B(x%2CA)%5C%7D%20%5Cvdash%20P%3AB%7D%7B%5CGamma%20%5Cvdash%20%5Clambda%20x%5Ccolon%20%5C!%5C!A.%20P%3AA%5Cto%20B%7D" alt="\frac{\Gamma \vdash P:A\to B\qquad \Gamma \vdash Q:A}{\Gamma \vdash P Q:B},\qquad \frac{\Gamma\cup\{(x,A)\} \vdash P:B}{\Gamma \vdash \lambda x\colon \!\!A. P:A\to B}" />

### Univerzális kvantifikáció

Bevezetési és kiküszöbölési szabályok:

<img src="https://i.upmath.me/svg/%5Cboxed%7B%5Cfrac%7B%5CGamma%20%5Cvdash%20f%3A%5Cforall%20x%3AA%2CB%5Cqquad%20%5CGamma%20%5Cvdash%20a%3AA%7D%7B%5CGamma%20%5Cvdash%20fa%3AB%5Bx%2Fa%5D%7D%5Cqquad%20%5Ctext%7B(apply)%7D%7D" alt="\boxed{\frac{\Gamma \vdash f:\forall x:A,B\qquad \Gamma \vdash a:A}{\Gamma \vdash fa:B[x/a]}\qquad \text{(apply)}}" />

<img src="https://i.upmath.me/svg/%5Cboxed%7B%5Cfrac%7B%5CGamma%5Ccup%5C%7B(x%3AA)%5C%7D%20%5Cvdash%20P%3AB%7D%7B%5CGamma%20%5Cvdash%20%5Clambda%20x%5Ccolon%20%5C!%5C!A.%20P%3A%5Cforall%20x%3AA%2CB%7D%5Cqquad%20%5Ctext%7B(intro)%7D%7D" alt="\boxed{\frac{\Gamma\cup\{(x:A)\} \vdash P:B}{\Gamma \vdash \lambda x\colon \!\!A. P:\forall x:A,B}\qquad \text{(intro)}}" />

Az univerzális kvantifikáció konstans B esetén azonos az kondicionálissal.

Ez utóbbi szabályok a Coq természetes nyelvén (_native language_ of Coq) alapszabály, bele van égetve a nyelvbe, itt lehet megtekinteni: [https://coq.inria.fr/distrib/current/refman/language/cic.html]

### Konjunkció

<img src="https://i.upmath.me/svg/%5Cfrac%7Bp%3AA%2C%5Cquad%20q%3AB%7D%7B(p%2Cq)%3AA%5C%26%20B%7D" alt="\frac{p:A,\quad q:B}{(p,q):A\&amp; B}" />

<img src="https://i.upmath.me/svg/%5Cfrac%7Bp%3AA%5C%26%20B%7D%7B%5Ctext%7Bpr%7D_1%20p%3AA%7D%2C%5Cquad%20%5Cfrac%7Bp%3AA%5C%26%20B%7D%7B%5Ctext%7Bpr%7D_2%20p%3AB%7D" alt="\frac{p:A\&amp; B}{\text{pr}_1 p:A},\quad \frac{p:A\&amp; B}{\text{pr}_2 p:B}" />

<img src="https://i.upmath.me/svg/%5Cfrac%7Bp%3AA%5Cto%20P%2C%5Cquad%20q%3AB%5Cto%20P%20%7D%7B(p%2Cq)%3AA%5C%26%20B%5Cto%20P%7D" alt="\frac{p:A\to P,\quad q:B\to P }{(p,q):A\&amp; B\to P}" />

<img src="https://i.upmath.me/svg/%5Cfrac%7BP%3AA%5C%26%20B%5Cto%20P%2C%5Cquad%20%5Cforall%20p%3AA%2C%5Cforall%20q%3AB%2C%20P(p%2Cq)%7D%7B%5Cforall%20r%3AA%5C%26%20B%2CPr%7D%20" alt="\frac{P:A\&amp; B\to P,\quad \forall p:A,\forall q:B, P(p,q)}{\forall r:A\&amp; B,Pr} " />







