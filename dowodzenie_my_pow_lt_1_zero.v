Require Import Reals.
Require Import Lra.
Require Import Lia.

Open Scope R_scope.

Lemma my_pow_lt_1_zero : forall q e : R,
  Rabs q < 1 ->
  e > 0 ->
  exists n0 : nat, forall n : nat, (n >= n0)%nat -> Rabs (q ^ n) < e.
Proof.
  intros q e Hq He.
  set (r := Rabs q).
  assert (Hr0 : 0 <= r) by (unfold r; apply Rabs_pos).
  assert (Hr1 : r < 1) by (unfold r; exact Hq).
  assert (Hpow : forall n : nat, Rabs (q ^ n) = r ^ n).
  { intro n. unfold r. rewrite <- RPow_abs. reflexivity. }

  (* Używamy archimed żeby znaleźć n0 takie że e * (1-r)^(-1) < n0 *)
  (* Prostsze: indukcja po n, pokazujemy że r^n < e dla dużych n *)
  
  (* Kluczowy lemat: r^n -> 0, czyli forall e>0 exists n0, r^n0 < e *)
  (* Dowodzimy przez: 1/r > 1, więc (1/r)^n -> inf, więc r^n -> 0 *)
  
  destruct (Req_dec r 0) as [Hr_zero | Hr_nonzero].
  
  - (* r = 0 *)
    exists 1%nat.
    intros n Hn.
    rewrite Hpow, Hr_zero.
    rewrite pow_ne_zero.
    lra.
    lia.


  - (* 0 < r < 1 *)
    assert (Hr_pos : 0 < r) by lra.
    
    (* 1/r > 1 *)
    assert (Hinvr : 1 < / r).
    { apply Rmult_lt_reg_l with r; [lra |].
 
      rewrite Rinv_r. 
      lra.
      lra.
     }
    
    (* niech h = 1/r - 1 > 0, czyli 1/r = 1 + h *)
    set (h := / r - 1).
    assert (Hh : 0 < h) by (unfold h; lra).
    
    (* Bernoulli: (1+h)^n >= 1 + n*h *)
    (* czyli (1/r)^n >= 1 + n*h > n*h *)
    (* czyli 1/r^n > n*h *)
    (* czyli r^n < 1/(n*h) *)
    
    (* Archimedes: exists n0, 1/(e*h) < n0 *)
    destruct (archimed (1 / (e * h))) as [Harch _].
    exists (Z.to_nat (up (1 / (e * h)))).
    intros n Hn.
    rewrite Hpow.
    
    (* r^n < e bo (1/r)^n > 1/(e) przez Bernoulliego *)
    apply Rlt_le_trans with (1/ (INR n * h)).
    
    + (* 1/(n*h) < e, bo n > 1/(e*h) *)
      apply Rmult_lt_reg_r with (INR n * h).
       apply Rmult_lt_0_compat. 
       apply lt_0_INR. 
       admit.
       lra.
       rewrite Rinv_l.
      + (* cel: 1 < e * (INR n * h) ... *)
    admit.
  + apply Rmult_pos; [apply lt_0_INR; lia | lra].      
    + (* r^n <= 1/(n*h) przez Bernoulliego *)
      (* (1/r)^n >= 1 + n*h >= n*h, więc r^n <= 1/(n*h) *)
      apply Rle_div_r.
      * apply Rmult_pos; [apply lt_0_INR; lia | lra].
      * assert (HBern : (1 + h) ^ n >= 1 + INR n * h).
        { apply pow_1_plus_INR_ge. lra. }
        unfold h in HBern.
        replace (/ r) with (1 + (/ r - 1)) by ring.
        apply Rle_trans with (1 + INR n * (/ r - 1)).
        - lra.
        - rewrite <- Rinv_pow by lra.
          apply HBern.
Qed.