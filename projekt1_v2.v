(*
Projekt 1
Krzysztof Boleń

W ramach tego tematu należy w Rocq zaimplementować i szczegółowo omówić 
podstawowe zagadnienia analizy matematycznej, konkretnie skupiając się na
 ciągach liczbowych i ich weryfikacji formalnej. Konkretnie, należy 
 zdefiniować odpowiednie typy i relacje modelujące pojęcia granic
  liczbowych i udowodnić formalnie granice wybranych ciągów.
 
  Konkretnie, należy:

  Definicja zbieżności właściwej ciągu liczbowego i zbieżności ciągu
     liczbowego do granicy właściwej;
  Wykazanie jednoznaczności granicy właściwej;
  Zdefiniowanie kilku, przykładowych ciągów zbieżnych (w tym ciągu stałego)
   i udowodnienie ich granic.
*)

(*Import bibloteki Lia na przyszłość*)
Require Import Lia.
(*Import bibloteki odpoweidzialnej za liczby rzeczywiste*)
Require Import Reals.
Require Import Lra.

(*Definicja ciągu geometrycznego jako wyraz początkowy a oraz iloraz q*)
Inductive seriesGeo := geo (a : R) (q : R).

(*by nie musieć pisać %R*)
Open Scope R_scope.
(*sprawdzam jak działa funkcja pow*)
Print pow.

(*definiuję jak obliczyć wartość n-tego wyrazu ciągu*)


Definition eval_seriesGeo (an : seriesGeo) (n:nat) :=
  match an, n with
  | geo a q , n => a * pow q n
  end.
  
Eval simpl in  eval_seriesGeo (geo 0 5) 5.

Eval simpl in  eval_seriesGeo (geo 2 0.25) 3.

(*uogólniona definicja ciągu liczbowego*)

Definition sequence := nat -> R.

Definition const_seq_1  : sequence := fun n => 1.

Compute const_seq_1 5%nat.

Print Rabs. (* sprawdzam jak wyglada funkcja Rabs - wartość bezwzględna dla R*)
(*definiuje granice ciągu*)  

Definition lim (an : sequence) (g : R) := 
  forall (e : R), 
      e>0 -> (*dla każdego e z R większego od 0 zachodzi *)
      exists (n0 : nat), (*istnieje jakieś n0 naturalne*)
      forall (n : nat), 
      (n>=n0)%nat -> (* że dla każdego n większego od tego n0 zachodzi*)
        Rabs (an n -g)<e. 

(*definicja istnienia granicy*)
Definition limExists (an : sequence) (g : R) := lim an g. 



(*twierdzenie pomocnicze że 1 do dowolnej natrualnej potęgi to 1*)
Lemma powCons :forall n:nat, pow 1 n=1.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  simpl.
  ring. (*służy do automatycznego upraszczania i udowadniania równości 
    algebraicznych w strukturach typu pierścień
    tutaj się przydaje bo mamy liczbę rzeczywistą do potęgi naturalnej*)
Qed.
(*definicja funkcji ciagu ktory dla kazdego n ma wartosc c *)
Definition const_seq (c : R) : sequence := fun n => c.

(*dowód tego że granicą ciągu stałego złożonego z samych 1 jest 1*)
Theorem easyLim : lim (const_seq 1) 1.
Proof.
  unfold lim. (*rozpakowanie definicji granicy*)
  intros e He. (*dodanie do założeń że e>0*)
  exists 1%nat. (*wzięcie 1 jako dowolne n0 *)
  intros n Hn. (*dodanie do założenia że n> 1*)
  unfold const_seq. (*rozpakowanie definicji funkcji ciągu*)
  replace (1-1) with 0 by ring. (* robie podstawienie za 1-1 0 dzięki ring*)
  rewrite Rabs_R0. (*lemat ze wartosc bezwgledna z 0 to 0*)
  exact He. (* wskazuje ze rozwiazniem dowodu jest zalozenie*)
 Qed.

Print Rabs_pos_lt.

(*lemat dot. tego że wartość bezwglena jest wieksza od zera jesli a i b są różne*)
Lemma diffNotZero : forall (a b : R), a<>b -> Rabs (a - b) >0.
Proof.
   intros. (*wprowadzam zmienne*)
   unfold Rabs. (*rozpakowuje definicje wartości bezwgldenej*)
   destruct (Rcase_abs (a - b)) as [Hlt | Hge]. (*rozbijam na przypadki że różnica
       albo jest wieksza od zera albo mniejsza*)
   lra.
   lra.
 Qed.
 (*twierdzenie dot. nierownosci trojka*)
Theorem absTriang : forall (a b : R), Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros. (*wporwadzamy zmienne*)
  unfold Rabs. (*rozpakowanie definicji Rabs*)
  destruct (Rcase_abs (a + b)) as [Hab | Hab]. (*rozbicie sumy na przypadki*)
  destruct (Rcase_abs a) as [Ha | Ha]. (*rozbicie a na przypadki a>0 lub a<0*)
  destruct (Rcase_abs b) as [Hb | Hb]. (*rozbicie a na przypadki b>0 lub b<0*)
  (*dalsza część dowodu to rozbijanie na przypadki i upraszczanie*)
  lra.
  lra.
  destruct (Rcase_abs b) as [Hb | Hb].
  lra.
  lra.
  destruct (Rcase_abs a) as [Ha | Ha].
  destruct (Rcase_abs b) as [Hb | Hb].
  lra.
  lra.
  destruct (Rcase_abs b) as [Hb | Hb].
  lra.
  lra.
Qed.

(*Lemat dot. symetrii wartości bezwględenej*)
Lemma symRabs : forall (a b : R), Rabs (a - b)=Rabs(b - a).
(*dowod polega na rozpakowaniu definicji Rabs i rozbiciu na przypadki 
a nastepnie konczenie za pomoca metody lra jak w poprzednim lemacie*)
Proof.
  intros.
  unfold Rabs.
  destruct (Rcase_abs (a-b)) as [Hab | Hab].
  destruct (Rcase_abs (b-a)) as [Hba | Hba].
  lra.
  lra.
  destruct (Rcase_abs (b-a)) as [Hba | Hba].
  lra.
  lra.
Qed.
(*Twierdzenie dot. jednoznaczności granicy ciągu*)

Theorem oneLim : forall (an : sequence) (g1 g2 : R),
   lim an g1 /\ lim an g2 -> g1=g2.
Proof. (*plan dowodu, tezę rozbijamy na dwa czyli albo g1=g2 albo są różne
  pierwszy przypadek trywialny, w drugim trzeba pokazać sprzeczność*)
  intros. (* wprowadzamy zmienne i założenie*)
  destruct H. (*rozbijam założenie dot. granic na 2*)
  destruct (Req_dec g1 g2) as [Heq | Hneq].  
  (*Req_dec mówi że 2 liczby albo są sobie równe albo są różne teraz 
  mamy dwa takie same cele ale w jednym mamy założenie że g1=g2 a w drugim 
  g1<>g2
  *)
  trivial. (*jest to oczywiste bo wynika bezpośrednio z założenia*)
  exfalso. (*zamieniam cel na fałsz bo dążymy do sprzeczności*)
  set (e := Rabs (g1-g2)/2). (*ustalam e na |g1-g2|/2 by wyszło dobrze ;)*)
  assert (He : e>0). (*udowadaniam że e jest większe od 0*)
  {  
    unfold e.
    apply Rdiv_lt_0_compat. (*twierdzenie że jeśli coś w nawiasie jest niezerowe
       to podzielone przez dowolna liczbę nadal jest niezerowe*)
    apply diffNotZero. (*używam wcześniej udowodnionegog twierdzenia*)
    trivial. (*wynika juz z obecnego załozenia ze g1<>g2*)
    lra.
  }
  specialize (H e He). (* podstawie założenia o  e oraz He do założenia H*)
  destruct H as [N HN]. (*rozbijam teraz H na to n0 oraz pozsotałą część założenia*)
  specialize (H0 e He). (*teraz podstawiam do H0  e oraz He*)
  destruct H0 as [N0 HN0]. (*i analogicznie rozbijam na N0 i HN0*)
  set (N_max := max N N0). (*tworze nowe N jako maksimum z N i N0*)
  assert (HNg1 :  Rabs (an N_max - g1) < e). 
  (*udowadniam że dla N_max wartość ciągu minus g1 jest mniejsza od e*)
  {
    apply HN. (*używam założenia z HN*)
    unfold N_max. (* i rozpakowuję N_max*)
    lia.
  }
  assert (HNg2 :  Rabs (an N_max - g2) < e).
  (*udowadniam że dla N_max wartość ciągu minus g2 jest mniejsza od e*)
  { (*analogicznie jak w poprzednim assercie*)
    apply HN0.
    unfold N_max.
    lia.
  }
  assert (Htriangle : Rabs (g1 - g2) <= 
            Rabs (g1 - an N_max)
            + Rabs (an N_max - g2)).
  (*udowadniam nierownosc trojkata z wartosicami bezglednymi*)
  {
    replace (g1 - g2)
      with
        ((g1 - an N_max)
        +
        (an N_max - g2))
        by ring.
        (*do g1-g2 wrzucam sztuczne 0 w postaci -an N_max + an N_max 
        by móc potem użyć lematu który udowodniłem wcześniej*)
    apply absTriang .
  }
  assert (Hsum : Rabs (g1 - an N_max ) + 
              Rabs (an N_max - g2)
              < e + e).
       (*teraz udowadanim że suma |g1 -an n_max| i |an N_max - g2| 
       jest mniejsza od dwóch e*)
  {
    rewrite symRabs. (*używam twierdzenie o symetryczności wartości bezwglednej*)
    lra.
  }
  
  assert (Hfinal : Rabs (g1-g2) <e+e).
  (*udowadniam że |g1-g2| jest mniejsze od 2e
  wszystko już mamy gotowe dzięki Htriangle oraz Hsum dlatego wystarczy lra
  *)
  {
    lra.
  }
  unfold e in Hfinal. (*rozpakowuje e w Hfinal by dostać sprzeczność*)
  lra.
Qed.

(*definicja dowolnego ciągu w postaci a*q^N *)
Definition geo_seq (a q : R) : sequence := fun n => a * pow q n.

(*dowod ze szereg 1/2^n zbiega do 0*)
Theorem easyGeoToZero : lim (geo_seq 1 0.5) 0.
Proof.
  (*rozpakowuje definicje granicy oraz obliczenie wartosci ciągu*)
  unfold lim, geo_seq. 
  (*wprwoadzam e i założenie że e>0*)
  intros e He.
  
  (* Szukamy n0 : (1/2)^n0 < e *)
  (* Używamy: (1/2)^n -> 0, więc istnieje takie n0 *)
  (*pokazuje ze 0.5 jest mniejsze niż 1 by użyć twierdzenia pow_lt_1_zero*)
    assert (Hq : Rabs 0.5 < 1).
    { rewrite Rabs_pos_eq. (*zamienia |0.5| na 0.5*)
     lra. 
     lra.
    }
    (*wprowadzam do zalozen twierdzenie o zbieganiu do 0 ciagu typu q^n czy |q|<1*)
    assert (H := pow_lt_1_zero 0.5 Hq e He).
  (* pow_lt_1_zero : 0 <= q < 1 -> e > 0 -> exists n0, q^n0 < e *)
  (*rozbijam moje nowe zalozenie na n0 i nowa zalozenie Hn0*)
  destruct H as [n0 Hn0].
  exists n0. (*wskazuje ze n0 istnieje*)
  (*wprowadzamy n:nat i zalozenie ze n>=n0*)
  intros n Hn.
  (*usuwam 0 z wartości bezwgledenj*)
  replace (1 * 0.5 ^ n  - 0) with (0.5 ^ n) by ring.
  apply Hn0. (*uzywam zalozenia ktore pochodzi z twierdzenia ze to
  |0.5^n|  jest mniejsze od e gdy n>n0
*)
  (*rozpakowuje założenie że n>=n0*)
  exact Hn.

Qed.



