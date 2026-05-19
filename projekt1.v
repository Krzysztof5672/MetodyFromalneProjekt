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



