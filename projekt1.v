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
Print Rabs. (* sprawdzam jak wyglada funkcja Rabs - wartość bezwzględna dla R*)
(*definiuje granice ciągu*)  
Definition lim (an : seriesGeo) (g : R) := 
  forall (e : R), 
      e>0 -> (*dla każdego e z R większego od 0 zachodzi *)
      exists (n0 : nat), (*istnieje jakieś n0 naturalne*)
      forall (n : nat), 
      (n>=n0)%nat -> (* że dla każdego n większego od tego n0 zachodzi*)
        Rabs (eval_seriesGeo an n -g)<e. 

Definition log2 (x : R) : R :=
  ln x / ln 2.


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
(*dowód tego że granicą ciągu stałego złożonego z samych 1 jest 1*)
Theorem easyLim : lim (geo 1 1) 1.
Proof.
  unfold lim. (*rozpakowanie definicji granicy*)
  intros e He. (*dodanie do założeń że e>0*)
  exists 1%nat. (*wzięcie 1 jako dowolne n0 *)
  intros n Hn. (*dodanie do założenia że n> 1*)
  unfold eval_seriesGeo. (*rozpakowanie definicji liczenia wartości ciągu*)
  simpl. 
  rewrite powCons. (*użycie twierdzenia do potęg liczby 1*)
  simpl.
  rewrite Rminus_diag_eq. (*używam twierdzenia że x-x=0 i rozbiło mi to na
        2 warunki, że Rabs 0 < e i 1*1=1 by wewnątrz Rabs`a było 0*)
  rewrite Rabs_R0. (*użycie twierdzenia że moduł z 0 to 0*)
  trivial.
  ring. (*analogicznie jak w lemacie użycie taktyki ring by pokazać że 1*1=1 *)
Qed.

Print Rabs_pos_lt.
Require Import Lra.
(*lemat dot. tego że wartość bezwglena jest wieksza od zera jesli a i b są różne*)
Lemma diffNotZero : forall (a b : R), a<>b -> Rabs (a - b) >0.
Proof.
   intros.
   unfold Rabs.
   destruct (Rcase_abs (a - b)) as [Hlt | Hge].
   lra.
   lra.
 Qed.
 (*twierdzenie dot. nierownosci trojka*)
Theorem absTriang : forall (a b : R), Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros.
  unfold Rabs.
  destruct (Rcase_abs (a + b)) as [Hab | Hab].
  destruct (Rcase_abs a) as [Ha | Ha].
  destruct (Rcase_abs b) as [Hb | Hb].
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

Theorem oneLim : forall (an : seriesGeo) (g1 g2 : R),
   lim an g1 /\ lim an g2 -> g1=g2.
Proof. (*plan dowodu, tezę rozbijamy na dwa czyli albo g1=g2 albo są różne
  pierwszy przypadek trywialny, w drugim trzeba pokazać sprzeczność*)
  intros.
  destruct H.
  destruct (Req_dec g1 g2) as [Heq | Hneq].  (*wytlumaczyć co to robi*)
  rewrite Heq.
  trivial.
  exfalso.
  set (e := Rabs (g1-g2)/2).
  assert (He : e>0).
  {  
    unfold e.
    apply Rdiv_lt_0_compat. (*twierdzenie że jeśli coś w nawiasie jest niezerowe
       to podzielone przez dowolna liczbę nadal jest niezerowe*)
    apply diffNotZero.
    apply Hneq.
    lra.
  }
  specialize (H e He).
  destruct H as [N HN].
  specialize (H0 e He).
  destruct H0 as [N0 HN0]. 
  set (N_max := max N N0).
  assert (HNg1 :  Rabs (eval_seriesGeo an N_max - g1) < e).
  {
    apply HN.
    unfold N_max.
    lia.
  }
  assert (HNg2 :  Rabs (eval_seriesGeo an N_max - g2) < e).
  {
    apply HN0.
    unfold N_max.
    lia.
  }
  assert (Htriangle : Rabs (g1 - g2) <= 
            Rabs (g1 - eval_seriesGeo an N_max)
            + Rabs (eval_seriesGeo an N_max - g2)).
  {
    replace (g1 - g2)
      with
        ((g1 - eval_seriesGeo an N_max)
        +
        (eval_seriesGeo an N_max - g2))
        by ring.
    apply absTriang .
  }
  assert (Hsum : Rabs (g1 - eval_seriesGeo an N_max ) + 
              Rabs (eval_seriesGeo an N_max - g2)
              < e + e).
  {
    rewrite symRabs.
    lra.
  }
  
  assert (Hfinal : Rabs (g1-g2) <e+e).
  {
    lra.
  }
  unfold e in Hfinal.
  lra.
Qed.
  