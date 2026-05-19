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




