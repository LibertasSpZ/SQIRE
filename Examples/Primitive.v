Require Export Complex.
Require Export Compose.
Require Import Prelude.
Require Import QWIRE.Dirac.
Require Import List.

Open Scope R_scope.
Open Scope C_scope.

Bind Scope R_scope with R.
Bind Scope C_scope with C.

(* This file verifies some computational properties of the cyclic group of 
primitive roots of unity {w_{2^n}^j}_j. These computational properties are
needed for verifying the correctness of QFT, which is part of a larger ongoing
research project. 
*)




(** Definition for the j-th power of primitive 2^n-th root of unity: \omega_n^j := (e^{2*PI* (sqrt(-1)) / 2^n})^j.
   Note that we only care about the primitive _2^n-th_ roots for the purpose of proving 
   QFT.  **)

Definition unit_root (n i : nat) : C := Cexp ((2 * PI * (INR i)) / (INR 2^n)).


(** As the 2^n-th root of unity is defined using Cexp from Complex.v, we explore some computational
properties of Cexp useful for the proof of the main lemmas.  **)


(* e^{ir + 2* PI * i} = e^{ir}.  *)
Lemma CexpPeriodical: forall (r: R), Cexp( r + 2 * PI ) = Cexp r.
Proof.
  unfold Cexp.
  Search cos.
  intros.
  rewrite cos_plus, sin_plus.
  Search 2 PI.
  rewrite cos_2PI, sin_2PI.
  rewrite Rmult_1_r, Rmult_0_r.
  rewrite Rmult_1_r, Rmult_0_r.
  rewrite Rminus_0_r, Rplus_0_r.
  easy. 
Qed.


(* e^{i r1 + i r2} = e ^ {i r1} * e ^{i r2}.  *)
Lemma CexpDistr: forall (r1 r2: R), Cexp( r1 + r2 ) = Cexp r1 * Cexp r2.
Proof.
  unfold Cexp.

  
  intros.
  rewrite cos_plus, sin_plus.
  unfold Cmult.
  simpl.
  rewrite Rplus_comm.
  easy.
Qed.

(*  e ^ {i r1} * e ^{i r2} * e ^{i r3} =  e ^ {i r1} * (e ^{i r2} * e ^{i r3}). *)
Lemma CexpAssoc: forall (r1 r2 r3: R), (Cexp r1 * Cexp r2) * Cexp r3 = Cexp r1 * (Cexp r2 * Cexp r3).
Proof.
  intros. 
  repeat rewrite <- CexpDistr.
  rewrite Rplus_assoc.
  easy.
Qed.


(**  Below is the first group property that Shouv's proof of QFT would be using: the group action
is additive in the power: i.e. , e^{sqrt(-1)* 2* PI / 2^n}^{j1} *  e^{sqrt(-1)* 2* PI / 2^n}^{j2}
= e^{sqrt(-1)* 2* PI / 2^n}^{j1 + j2}. It mainly just follows from the additive property of Cexp. **)

Lemma root_i_plus_j : forall (n i j : nat), unit_root n i * unit_root n j = unit_root n (i + j).
Proof.

  unfold unit_root.
 
  intros. 
  rewrite <- CexpDistr.
  unfold Rdiv.
  
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rmult_plus_distr_l.
  rewrite <- Rmult_plus_distr_r.
  Search INR plus.
  rewrite plus_INR.
  reflexivity.
Qed.  



(** Next, a collection of helper lemma's towards the proof of the second main lemma "roots_n_plus1". The
mathematical meaning of most of these lemma's are self-explanatory from their statements. **)


Lemma greatNeqR: forall (r : R), 0 < r -> r <> 0.
Proof. 
  intros.
  intros contra.
  lra. 
Qed.

Lemma INR2Neq0: INR 2 <> 0.
Proof.
    apply greatNeqR.
    assert (alwaysAlmostTrivial: INR 2 = 2 ) . { unfold INR. simpl. auto. }
                                               rewrite alwaysAlmostTrivial.
    Search 0 2.
    apply Rlt_0_2.
Qed.

Lemma INRINV2Neq0: / INR 2 <>0.
Proof.
    assert (Inter: (/INR 2) % R <> 0). { apply Rinv_neq_0_compat. apply INR2Neq0. }
                                      auto.
    intros contra. Search Cinv.
    assert (Inter2: /INR 2 = (/INR 2)%R) . {symmetry. apply RtoC_inv. apply INR2Neq0. }
                                           rewrite Inter2 in contra.
    Search 0.
   
    Search Prop False.
    
    rewrite neg_false in Inter.
    apply Inter.
    
    apply RtoC_inj.
    apply contra.
Qed.

Lemma INR2AllNeq0: forall (m : nat), (INR 2)^m <> 0.
Proof.
   intros.
   apply Cpow_nonzero.
   apply INR2Neq0.
Qed.

Lemma INR2AllInvNeq0: forall (m : nat), / (INR 2)^m <> 0.
Proof.
    Search Cinv.
    intros m.
    assert (WWWG: (INR 2)^m <> 0). { apply INR2AllNeq0. }
        
                                  Search Cinv.
    Search Cpow.

    Search Cinv.
    apply Cinv_r in WWWG.
    Search 1 0.
    assert (LL: C1  <> C0). {simpl. apply C0_fst. unfold C1. simpl. apply R1_neq_R0. }              
                           rewrite <- WWWG in LL.
    Search Cmult.
    intros contra.
    rewrite contra in LL.
    rewrite Cmult_0_r in LL.
    simpl in LL.
    auto. 
Qed.

  
(* The proof of the following  helper is slightly more involved than the ones above, though mathematically
 trivial. It says that for any real number z, z / (2 ^ {n+1}) + z /(2 ^ {n+1}) = z/ 2^n.   *)

Lemma sum_pow_2n: forall (z:R)(n: nat), (z */ (INR 2 * INR 2^ n) + z */ (INR 2 * INR 2^n) )%R = (z */  INR 2^n)%R.
Proof.
  intros.
  rewrite <- Rmult_plus_distr_l.
  assert (trivialToutJours: forall (r : R), (r + r)% R = ((1 + 1) * r) % R).
    {
      intros.  rewrite -> Rmult_plus_distr_r. rewrite Rmult_1_l. simpl. lra.
    }

  assert (seriouslyQuestionMark: ( /(INR 2 * INR 2^n) + / (INR 2 * INR 2^n) ) % R =
                                   ((1 + 1) * /(INR 2 * INR 2^n)) % R ).
    {
      Check ((1+1) */ INR 2 * INR 2^n)% R.
      Check ((1+1) */ (INR 2 * INR 2^n)) %R. apply trivialToutJours.
    } rewrite seriouslyQuestionMark.
    
  
  simpl.
  assert (TooYoungTooSimple: ((1+1) */ (1+1) * /(1+1)^n)%R =( /(1+1)^n)%R ).
    {
      Search Rinv. apply Rinv_r_simpl_r. apply INR2Neq0.
    }
  assert (distributee: ( / ((1 + 1) * (1 + 1) ^ n))% R = (/(1+1) * /(1+1)^n) % R). 
    { Search Rinv.
      apply Rinv_mult_distr.
      assert (INR 2 = (1 + 1)%R). trivial.
      rewrite <- H. apply INR2Neq0.
      assert (WWEKO: (INR 2^n)%R = ((1 + 1)^n)%R). {trivial. }
      intros contra.
      rewrite <- WWEKO in contra.
      assert (DIR: INR 2 ^ n <> 0). {apply INR2AllNeq0. }
                                   rewrite <- contra in DIR.
      assert (DIR2: INR 2 ^ n = (INR 2 ^ n)%R). {apply RtoC_pow. }
      auto.
    }
  rewrite distributee.
  simpl.
  assert (RMAssoc: ((1 + 1) * (/ (1 + 1) * / (1 + 1) ^ n))%R = ((1 + 1) * / (1 + 1) * / (1 + 1) ^ n)%R).
    {
      rewrite Rmult_assoc. auto.
    } rewrite RMAssoc.
    rewrite TooYoungTooSimple.
  auto.                                                                                                         
Qed.


(** This is the second major lemma in Shouv's inductive proof: (e^{sqrt(-1) * 2 * PI/ 2^n})^j = 
 (e^{sqrt(-1) * 2 * PI/ 2^{n+1})^{2 * j}. After reshaping, it mainly follows from the technical
lemma "sum_pow_2n" above.  **)

Lemma roots_n_plus1 : forall (n i : nat), unit_root n i = unit_root (n + 1) (2 * i).
Proof.

  simpl.
  intros m i.
  rewrite plus_0_r.
  rewrite <- root_i_plus_j.
  unfold unit_root.
  rewrite <- CexpDistr.
  Search Rmult.


  rewrite Nat.add_1_r.
  rewrite <- tech_pow_Rmult.
  
  assert (diruse: (2 * PI * INR i / (INR 2 * INR 2^m) + 2 * PI * INR i / (INR 2 * INR 2 ^m))%R =
                  (2 * PI * INR i / INR 2 ^m)%R ).
  {
    apply sum_pow_2n with (z:= (2 * PI * INR i)%R).
  }
  rewrite diruse.
  auto.
Qed.



(** Moving towards the third lemma for QFT, as usual we make a bunch of computational observations. **)


Lemma Neq0Geq1: forall (n : nat), INR n<> 0 -> ~(INR n < 1).
Proof.
  intros.
  intros contra.
  assert (Fine: INR n < 1 -> INR n = 0).
  {
    intros. Search 0 1. Search INR.
    assert ( Baah: (n < 1)%nat ) .
    {
      apply INR_lt.
      simpl.
      assumption.
    }
    assert (Baaaah: (1 > n)%nat).
    {
      assumption.
    }
    assert (Gooo: (n = 0)%nat).
    {
      auto.
      Search nat 1.
      inversion Baah; subst.
      reflexivity.
      inversion H2.
    } rewrite Gooo.
    auto.
  }
  auto.
Qed.


Lemma notless1ThenGet1: forall (n : nat),  ~(INR n < 1) -> INR n >= 1. Proof. intros. auto.  lra. Qed.

Lemma cexp2Pi: Cexp(2 * PI) = 1. Proof. unfold Cexp. rewrite cos_2PI, sin_2PI. lca. Qed.

Search cos.

Lemma Cos2PiN1: forall (n:nat), cos(2 * PI * INR n) = 1.
Proof.
  induction n. (* Key point: directly induct; don't intros! Won't be general enough.  *)
  - simpl.
    rewrite Rmult_0_r.
    rewrite cos_0. auto.
  - rewrite <- Nat.add_1_r.
    assert (Change0: INR (n + 1) = (INR n + INR 1)%R ).
    {
      Search INR. apply plus_INR.
    } rewrite Change0.
    assert (Change1: (2 * PI * ( INR n + INR 1))%R = (2 * PI * INR n + 2 * PI * INR 1)%R ).
    {
      apply Rmult_plus_distr_l with (r1:= (2 * PI)%R).
    } rewrite Change1.

    rewrite cos_plus.
    simpl.
    rewrite Rmult_1_r.
    rewrite sin_2PI, cos_2PI.
    rewrite Rmult_1_r, Rmult_0_r.
    rewrite Rminus_0_r.
    assumption.
Qed.

Lemma Sin2PiN0: forall (n:nat), sin(2 * PI * INR n) = 0.
Proof. (* Similar approach to the above. *)
  induction n.
  - simpl.
    rewrite Rmult_0_r.
    rewrite sin_0. auto.
  - rewrite <- Nat.add_1_r.
    assert (Change0: INR (n + 1) = (INR n + INR 1)%R ).
    {
      Search INR. apply plus_INR.
    } rewrite Change0.
    assert (Change1: (2 * PI * ( INR n + INR 1))%R = (2 * PI * INR n + 2 * PI * INR 1)%R ).
    {
      apply Rmult_plus_distr_l with (r1:= (2 * PI)%R).
    } rewrite Change1.

    rewrite sin_plus.
    simpl.
    rewrite Rmult_1_r.
    rewrite sin_2PI, cos_2PI.
    rewrite Rmult_1_r, Rmult_0_r.
    rewrite Rplus_0_r.
    assumption.
Qed. 


Lemma Cexp2PipowAlways1: forall (pow : nat), Cexp(2 * PI * INR pow) = 1.
Proof.
  intros.
  unfold Cexp.
  Search sin.
  destruct pow eqn:EE.
  - assert (contraH1: INR 0 < 1).
    {
      Search 0 1.
      assert (obv: 0 < 1).
      {
        apply Rlt_0_1.
      }
      unfold INR.
      assumption.
    }
    simpl.
    rewrite Rmult_0_r.
    rewrite cos_0, sin_0.
    lca.
  - rewrite <- Nat.add_1_r.
    assert (Change0: INR (n + 1) = (INR n + INR 1)%R ).
    {
      Search INR. apply plus_INR.
    } rewrite Change0.
    assert (Change1: (2 * PI * ( INR n + INR 1))%R = (2 * PI * INR n + 2 * PI * INR 1)%R ).
    {
      apply Rmult_plus_distr_l with (r1:= (2 * PI)%R).
    } rewrite Change1.
    Search sin.
    rewrite sin_plus, cos_plus.
    simpl.
    rewrite Rmult_1_r.
    rewrite sin_2PI, cos_2PI.
    rewrite Rmult_0_r, Rmult_1_r.
    rewrite Rmult_0_r.
    rewrite Rplus_0_r, Rminus_0_r.
    rewrite Rmult_1_r.
    rewrite Cos2PiN1, Sin2PiN0.
    auto.     
Qed. 


Lemma pwpw1: forall (n :nat),  1 ^ n = 1.
Proof.
  induction n.
  - simpl. reflexivity.
  - assert (1 ^ S n = (1 ^ S n) % R).
    {
      apply RtoC_pow.
    } rewrite H.
    rewrite <- tech_pow_Rmult.
    assert (1 ^ n = (1 ^ n) % R).
    {
      apply RtoC_pow.
    }  rewrite H0 in IHn.
    rewrite Rmult_1_l.
    assumption.
Qed.



(* Our third lemma would address the fact that 1 + w_d + w_d^2 + ... w_d^{d-1} = 0, with d:= 2^n.
To do that we make a definition for this sum.  *)

Fixpoint sum_of_roots (n j : nat): C :=
  match j with
  | O => (0,0)
  | S j' => (sum_of_roots n j') + (unit_root n j')
  end.

(* Turns out this definition, denoting 1 + w_d^{2} + w_d^{4} + ... + w_d^{2(p-1)}, is a handy tool
for showing the key factorization property (recorded in Lemma sumRootsSubdivision later), which leads
towards the proof of the main lemma 1 + w_d + w_d^2 + ... w_d^{d-1} = 0.   *)  
Fixpoint sum_of_Even_Pow_roots (n j : nat): C :=
  match j with
  |0 => (0,0)
  |S j' => sum_of_Even_Pow_roots n j' + unit_root n (2 * j')
  end.


(* SumRootsSub1 and SumRootsSub2 records the intermediate steps leading towards Lemma sumRootsSubdivision. 
SumRootsSub1 states that 1 + w_{2^{n+2}}^2 + ... + w_{2^{n+2}}^{2*(2 * pow -1)} = (w_{2^{n+1}} + 1)*
                         (1 + w_{2^{n+1}}^2 + ... + w_{2^{n+1}}^{2*(pow -1)}). 
 *)
Lemma SumRootsSub1: forall (n pow: nat), sum_of_Even_Pow_roots (n + 1 + 1) (2 *  pow) =
                                  (unit_root (n + 1) 1) * sum_of_Even_Pow_roots (n + 1) (pow) +
                                  sum_of_Even_Pow_roots (n + 1) (pow).
Proof.
  intros.
  generalize dependent n.
  induction pow.
  - simpl.
    intros.
    rewrite Cmult_0_r.                     
    auto.
    rewrite Cplus_0_l.
    auto. 
  - intros.
    assert ( sum_of_Even_Pow_roots (n + 1 + 1) (2 * S pow) =
             sum_of_Even_Pow_roots (n + 1 + 1) ( S ( S (2 * pow)))).
    {
      assert (WDD: S pow = (pow + 1)%nat).
      {
        auto. rewrite Nat.add_1_r. auto.
      } rewrite WDD.
      Search nat mult.
      rewrite <- double_mult.
      rewrite plus_assoc.
      assert ((pow + 1 + pow + 1)%nat  = (2 * pow + 1 + 1)%nat ).
      {
        assert ((pow + 1 + pow)%nat  = (pow + pow + 1)%nat ).
        {
          rewrite plus_comm. rewrite plus_assoc.  auto.
        } rewrite H.
        rewrite double_mult. auto.
      }
      rewrite H.
      auto.
      assert (S(S(2*pow)) = (2 * pow + 1 + 1)%nat ).
      {
        rewrite Nat.add_1_r. rewrite Nat.add_1_r.  auto.
      } rewrite H0.
      auto.
    }
    rewrite H.
    assert (sum_of_Even_Pow_roots (n + 1 + 1) (S (S (2 * pow))) =
            sum_of_Even_Pow_roots (n + 1 + 1) (S (2 * pow)) +
            unit_root (n + 1 + 1) (2 * S(2 * pow))).
    {
      reflexivity.
    } rewrite H0.                                                                                                         assert (H3: sum_of_Even_Pow_roots (n + 1 + 1)  (S (2 * pow)) =
                                                                                                                                      sum_of_Even_Pow_roots (n + 1 + 1)  (2 * pow) +
                                                                                                                                      unit_root (n + 1 + 1) (2 * (2 * pow))). {reflexivity. } rewrite H3.                                       assert (H4: sum_of_Even_Pow_roots (n + 1)  (S (pow)) =
                                                                                                                                                                                                                                                            sum_of_Even_Pow_roots (n + 1 )  (pow) +
                                                                                                                                                                                                                                                            unit_root (n + 1) (2 * (pow))). {reflexivity. } rewrite H4.
    rewrite IHpow.             
    rewrite Cmult_plus_distr_l.
    rewrite <- roots_n_plus1.
    rewrite root_i_plus_j.
    assert (H6: unit_root (n + 1 + 1) (2 * S (2 * pow)) = unit_root (n + 1) ( 1+ (2 * pow)) ).
    {
      rewrite <- roots_n_plus1.
      assert (WWWWKKK: S(2 * pow) = (1 + 2*pow)%nat). {auto. } rewrite WWWWKKK.
      auto.
    } rewrite H6.
    rewrite Cplus_assoc. auto.
    assert (rearrange: forall (x y z t : C), x + y + z + t = x + t + y + z).
    {
      intros.
      assert (y + z + t = t + y + z). rewrite Cplus_comm. rewrite Cplus_assoc. auto .
      assert (x+y+z+t = x + (y+z+t)). {repeat rewrite Cplus_assoc. auto. }
      assert (x+t+y+z = x+ (t+y+z)). { repeat rewrite Cplus_assoc. auto. } rewrite H2, H5, H1. 
      auto.
    }
    apply rearrange. 
Qed.           

(* SumRootsSub2 establish the connection between the two sums we defined, closing the final link
 with the cricial helper lemma sumRootsSubdivision. Mathematically it just says
 1 + w_{n+1}^{2} + w_{n+1}^4 + ... + w_{n+1}^{2(p-1)} = 
 1 + w_{n}^{1} + w_{n}^2 + ... + w_{n}^{(p-1)}, which is a direct corollary of
 Lemma roots_n_plus1.  *)

Lemma SumRootsSub2: forall (n pow: nat), sum_of_Even_Pow_roots (n+1) (pow) = sum_of_roots n (pow).
Proof.
  intros.
  generalize dependent n.
  induction pow.
  -
    simpl.
    intros n.
    simpl.    
    auto.

   -   
    intros. 
    rewrite Nat.add_1_r.  
    assert (Cool: sum_of_Even_Pow_roots (n+1 ) (S (pow)) =
                  sum_of_Even_Pow_roots (n+1) (pow) + unit_root (n+1) (2 * (pow))).
    {reflexivity. }
    assert (Cool2: sum_of_roots n ( S (pow ) ) = sum_of_roots n (pow ) + unit_root n (pow )).
    {reflexivity. }
    assert (duh: S n = (n + 1)%nat).
    {rewrite Nat.add_1_r. auto. }
    rewrite duh.                                                                                                          rewrite Cool, Cool2.
    rewrite IHpow.
    rewrite <- roots_n_plus1.
    auto.
Qed. 

(* At this point the crucial lemma stating 1 + w_{2^{n+1}} + ... + w_{2^{n+1}}^{2^{p+1}-1} =
                                           (w_{2^{n+1}} + 1)*
                                           (1 + w_{2^{n}} + ... + w_{2^{n}}^{2^{p}-1})
becomes a direct corollary of the two helper lemmas above.  *)
Lemma sumRootsSubdivision: forall (n pow:nat),  sum_of_roots (n+1) (2* 2^pow) =
                                         ((unit_root (n+1) 1) + 1) * (sum_of_roots n (2^pow)). 
Proof.
  intros. 
  rewrite Cmult_plus_distr_r.
  repeat rewrite <- SumRootsSub2.
  rewrite Cmult_1_l.
  rewrite <- SumRootsSub1.
  auto.
Qed. 

(* To inherently use the integral domain property of C (which eventually leads to conclusion of the 3rd lemma), 
we need to fully factorize (unit_root n (2^pow)) - 1. Lemma sumRootsSubdivision gave the less intuitive step
for factorization; the lemma below gives another step, which is slighly more intuitive to see but cumbersome to
prove anyway.  *)

Lemma unitRootFactorization: forall (n :nat), (unit_root n 1) - 1 = ((unit_root (n+1) 1) - 1) * ((unit_root (n+1) 1) + 1).
Proof.
  intros. 
  rewrite Cmult_plus_distr_l.
  assert (WAA: (unit_root (n + 1) 1) - 1 = (unit_root (n + 1) 1) + -1).
  {
    rewrite Cminus_unfold. simpl.  auto.
    assert (-(1) = -1). {lca. } rewrite H. auto.
  } rewrite WAA.

  rewrite Cmult_plus_distr_r.                                                                        
  simpl.
  rewrite  root_i_plus_j.
  assert (reallypawsome: (1+1)%nat = 2%nat). (* Was watching some dog video apparently. *)
  {simpl. auto. } rewrite reallypawsome.
  assert (pawpew: 2%nat  = (2 * 1)%nat ). {simpl. auto. } rewrite pawpew.
  rewrite <- roots_n_plus1.
  rewrite Cmult_1_r.
  rewrite Cminus_unfold.
  rewrite Cplus_assoc.
  assert(ddddfakf: unit_root n 1 + -1 * unit_root (n + 1) 1 + unit_root (n + 1) 1 =
                   unit_root n 1 + (-1 * unit_root (n + 1) 1 + unit_root (n + 1) 1)).
  {rewrite Cplus_assoc. auto. } rewrite ddddfakf.                                                                       assert (lalala: -1 * unit_root (n + 1) 1 + unit_root (n + 1) 1 =  0).
  {
    assert (la2: -1 * unit_root (n + 1) 1 =  (unit_root (n + 1) 1) * (-1)). {rewrite Cmult_comm. auto. }
    rewrite la2.
    assert (la3:  (unit_root (n + 1) 1) * (-1) = -(    (unit_root (n + 1) 1) * 1)).
    {
      remember  (unit_root (n + 1) 1) as r1.
      assert ( -(1) = -1). lca.
      rewrite <- H.
      rewrite <- Copp_mult_distr_r.  auto.
    }
    rewrite la3.
  
    Search Copp.
    rewrite Cmult_1_r.
    apply Cplus_opp_l.
  }
  rewrite lalala.
  rewrite Cplus_0_r.
  assert ( -(1) = -1). lca.
  rewrite <- H.
  auto.
Qed.
 

(* As promised, we deliver the lemma for using the integral domain property (c1 * c2 = 0 -> c1 <> 0 -> c2 = 0).
We do not directly prove that property in general; instead we later apply it to c1 := (unit_root n 1) - 1,
c2 = sum_of_roots n (2^pow), with n >=1. 

The lemma below is a specialization to the factorization of polynomials:
 x^{2^p} -1 = (x-1)(1 + x + x^2 + ... + x^{2^p-1}) with x:= (unit_root n 1). As we would rather not define
polynomials and factorization thereof from scratch, we only prove this specialization, since it is all we need for
QFT.  *)

Lemma decomp_n_pow_minus_6: forall (n pow:nat), (unit_root n (2^pow)) - 1 = ((unit_root n 1) - 1) * (sum_of_roots n (2^pow)).
Proof. 
  intros m pow.
  generalize dependent pow.
  induction m.
  - simpl.
    
    unfold unit_root.
    simpl.
    Search 1.
    unfold Cinv.
    remember ((2 * PI * 1)% R) as arr.
    Search Rinv.
    rewrite Rdiv_unfold.
    
    rewrite RMicromega.Rinv_1.
    rewrite Rmult_1_r in Heqarr.
    rewrite Heqarr.
    intros pow.
    remember ((2 * PI * INR (2^pow))% R) as arr2.
    Search Rinv.
    rewrite Rdiv_unfold. 
    rewrite RMicromega.Rinv_1.
    rewrite Heqarr2.
    rewrite cexp2Pi.
    assert (wv: (1 - 1)%R = 0).
    {
      Search Rminus.
      apply Rminus_diag_eq with (r1:= 1) ( r2:=1).
      reflexivity.
    }
    assert (wwww: 1-1 = 0).
    {
      simpl. Search Cminus.
      rewrite Cminus_unfold. simpl.
      unfold Copp. unfold Cplus.
      simpl. simpl.
      auto.
      repeat rewrite Rplus_opp_r. auto.
    } rewrite wwww.
    
    rewrite Cmult_0_l.
    assert (BB: Cexp (2 * PI * (1+1)) = 1).
    {
      assert (DDD: (1 + 1)%R = INR 2). {simpl. lra. } rewrite DDD.
      apply Cexp2PipowAlways1.
    }
    rewrite  Cexp2PipowAlways1. 
    assumption.    
  - rewrite <- Nat.add_1_r.
  
    induction pow eqn:powsWhom.
    + simpl.
      rewrite Cplus_0_l.
      unfold unit_root, Cexp.
      remember (2* PI * INR 0)%R as arh.
      repeat rewrite Rdiv_unfold.
      simpl in Heqarh.
      repeat rewrite Rmult_0_r in Heqarh.
      rewrite Heqarh.
      rewrite Rmult_0_l.
      rewrite cos_0,sin_0.
      rewrite Cmult_1_r.
      reflexivity.
    +
      
      assert (WeAllKnow: S n = (n + 1)%nat) .
      {
        rewrite <- Nat.add_1_r. reflexivity.
      } rewrite WeAllKnow.
      assert (trivialtrivial: forall (w:nat), (2 ^ (w + 1))%nat = (2 * 2^w)%nat).
      {
        induction w.
        - simpl. reflexivity.
        - assert (Bahhh: (S w + 1)%nat = S (w + 1)).
          {
            Search nat S 1.  remember (w + 1)%nat as barr.
            rewrite  Nat.add_1_r.  rewrite Nat.add_1_r in Heqbarr. rewrite Heqbarr.
            reflexivity.
          } rewrite Bahhh. 
          assert ( (2 ^ S (w+1))%nat = (2 * 2^(w + 1))%nat).
          {simpl.    reflexivity. } rewrite H.
          assert (WeAllKnowagain: S w = (w + 1)%nat) .
          {rewrite <- Nat.add_1_r. reflexivity. }
          rewrite WeAllKnowagain.
          reflexivity.
      }   rewrite trivialtrivial.
      rewrite <- roots_n_plus1.
      rewrite IHm.
      rewrite unitRootFactorization.
      rewrite <- Cmult_assoc.
      rewrite <- sumRootsSubdivision.
      auto.
Qed. 


(* The whole approach above took some experiments to find. Below are some other lemmas i attempted and aborted before finding out the "sum of even pow roots approach":

Lemma squareSumFormulaGen: forall (n : nat), unit_root (n + 1) (2 ^(n+1)) - 1 = (unit_root (n + 1) ( 2 ^n) -1) * (unit_root (n + 1) ( 2 ^n) + 1). Proof. Admitted.
Lemma squareSumFormula2: forall (n : nat), unit_root n  1 - 1 = (unit_root (n + 1) 1 -1) * (unit_root (n + 1) 1 + 1). Proof. Admitted. 
Lemma DistributeToInductHelper: forall (n : nat), (unit_root (n + 1)   1) * sum_of_roots n 2^n = sum_of_roots (n+1) 2^(n+1). Proof. Admitted.
Lemma decomp_n_pow_minus_1: forall (n :nat),  unit_root n (2 ^ n) - 1 = (unit_root n 1 - 1) * (sum_of_roots n 2^n). Proof. induction n. Admitted. 
Lemma decomp_n_pow_minus_1_prime: forall (n i pow:nat), INR pow >= 1 -> (unit_root n 1)^pow = 1 -> unit_root n 1 <> 1 -> sum_of_roots n pow= 0. Proof. Admitted. 
                                                                  
 *)


(* With decomp_n_pow_minus_6 at hand we are almost ready to use the integral domain property. We just need to 
show that LHS of the equation in decomp_n_pow_minus_6 equals 0, and the first factor is non-0, which is what the
next two helper lemmas did.  *)

Lemma fullPowerUnitUnit: forall (n:nat), unit_root n (2^n) = 1.
Proof.
  unfold unit_root. intros. remember (2 * PI * INR (2^n))%R as r1.
  Search Rinv. rewrite Rdiv_unfold. rewrite Heqr1.
       
  remember (2 * PI)%R as r2.
  Search Rinv.
  Search INR.
  rewrite <- pow_INR.
  rewrite Rinv_r_simpl_l.
  assert (r2 = (r2 * INR 1)%R).
  {
    simpl. rewrite Rmult_1_r. reflexivity.
  } rewrite H.
  rewrite Heqr2.
  apply Cexp2PipowAlways1.
      
  rewrite  pow_INR.
  Search INR. 
  assert ( INR 2^n = (INR 2^n)%R ).
  {
    rewrite <- RtoC_pow. reflexivity.
  }
  intros contra.
  symmetry in contra.
  subst.
  assert (contra2 : INR 2^n <> 0). {apply INR2AllNeq0. }
  auto.
  rewrite contra in contra2.
  auto.  
Qed.

Lemma nplus1rootNon0: forall (n :nat), INR n>= 1 -> (unit_root n 1) - 1<> 0.
Proof.
  induction n.
  - intros.
    assert (contra: INR(0) < 1).
    {
      simpl. Search 0 1. apply Rlt_0_1.
    }
    lra.
  - intros.
    intros contra.
    rewrite <- Nat.add_1_r in contra.
    assert (((unit_root (n + 1) 1) - 1) * ((unit_root (n + 1) 1) + 1) = 0).
    {
      rewrite contra. rewrite Cmult_0_l. auto.
    } rewrite <-unitRootFactorization in H0.
    assert (~(INR n >=1)).
    {intros contracontra.
     apply IHn in contracontra.  auto.
    }
    assert (D1: not (not (n = 0)%nat)).
    {
      intros connn. Search INR. apply not_0_INR in connn.
      apply Neq0Geq1 in connn. apply notless1ThenGet1 in connn.
      lra.
    }
    simpl in D1. apply Classical_Prop.NNPP in D1.
    rewrite D1 in contra. rewrite plus_0_l in contra. simpl in contra.
    unfold unit_root in contra.
    rewrite Rdiv_unfold in contra.
    rewrite Rmult_comm in contra.
    rewrite Rmult_1_r in contra.
    assert(H789: (/INR 2^1)%R = (/2)%R ).
    {
      simpl. auto. rewrite Rmult_1_r. auto.
    } rewrite H789 in contra.
    rewrite <- Rmult_assoc in contra.
    Search Rinv.
    rewrite Rmult_comm in contra.
    simpl in contra.
    assert (WDKKKK: (/2 * 2)%R = 1).
    {
      rewrite Rmult_comm. auto. Search Rinv.
      assert (baar: (2 * /2)%R = (1 * (2 * /2))%R).
      rewrite Rmult_1_l. auto. rewrite baar. rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_l.
      auto. lra.
    } rewrite WDKKKK in contra.
    rewrite Rmult_1_r in contra.
    unfold Cexp in contra.
    Search cos.
    rewrite cos_PI in contra.
    rewrite sin_PI in contra.
    simpl in contra.
    Search 1.
    assert (absurd:  (-1, 0) = C1).
    {
      Search C 1.
      assert (C1 = C1 + C0). rewrite Cplus_0_r. auto.
      rewrite <- contra in H2.
      unfold Copp. simpl in H2.
      Search Copp.
      rewrite Cminus_unfold in H2.
      rewrite Cplus_comm in H2.
      simpl in H2.
      rewrite <- Cplus_assoc in H2.
      simpl in H2.
      Search Copp.
      rewrite Cplus_opp_l in H2.
      rewrite Cplus_0_r in H2.
      symmetry in H2.
      auto.
    }
    auto.
    assert (C1 = (1, 0)). {simpl. auto. }  rewrite H2 in absurd.
    rewrite H2 in contra.
    simpl in contra.
    rewrite Cminus_unfold in contra.
    unfold Cplus in contra.
    simpl in contra.
    apply C0_fst in contra.
    assumption.
    assert( (-1 + - (1))%R = (-2)%R). {simpl. lra. } rewrite H3.
    simpl.
    lra.
Qed. 


                                                                 
(* Using all results above, our third main lemma follows by playing with logical rules.  *)

Lemma all_roots_sum : forall (n : nat), INR n >= 1 ->  sum_of_roots n (2^n) = (0,0).
Proof.
  induction n. 
  - intros P.
    inversion P. auto. Search 0 1.
    assert (contraH: INR 0 <= 1).
    {apply Rle_0_1. }
    auto.
    lra.
    assert (contraH2: 1 <> INR 0). {Search 0 1. apply R1_neq_R0. } rewrite <- H in contraH2.
    lra.
  - intros.
    rewrite <- Nat.add_1_r.
    Search 0 Rmult.
    
    assert (EitherOr: (unit_root (n+1) 1) - 1 =  0 \/ sum_of_roots (n + 1) (2 ^ (n + 1)) = 0).
    {
      assert (NotNeitherNor: not ( (unit_root (n+1) 1) - 1 <>  0 /\ sum_of_roots (n + 1) (2 ^ (n + 1)) <> 0)).
      {
        intros contra.
        assert (W1:  (unit_root (n+1) 1) - 1 <> 0).
        {
          auto.
          apply proj1 in contra. assumption.
        }
        assert (W2:  sum_of_roots (n + 1) (2 ^ (n + 1)) <> 0).
        { auto.
          apply proj2 in contra. assumption.
        }
        assert (concon: (unit_root (n+1) 1 - 1) * (sum_of_roots (n + 1) (2 ^ (n + 1))) <> 0).
        {
          Search Cmult. apply Cmult_neq_0. assumption. assumption.
        }
        assert (concon2: ((unit_root (n+1) 1) - 1) * (sum_of_roots (n + 1) (2 ^ (n + 1))) = 0).     
        rewrite <- decomp_n_pow_minus_6.
        assert (Almostconcon2:  unit_root (n + 1) (2 ^ (n + 1)) = 1) .
        {
          apply fullPowerUnitUnit.
        } rewrite Almostconcon2.
        simpl.
        auto.
        assert (wwww: 1-1 = 0).
        {
          simpl. Search Cminus. rewrite Cminus_unfold.
          simpl. unfold Copp. unfold Cplus. simpl. simpl.
          auto. repeat rewrite Rplus_opp_r. auto.
        }
        assumption. auto. 
      }
      
      auto.
      Search Prop.
      assert (FineFine: forall (P Q R S : Prop), ((P -> R) /\ (Q -> S) ) -> ((P \/ Q) ->( R \/ S)) ).
      {
        intros P Q R S H0 H1. destruct H1 as [M | N].
       - apply or_introl.
         assert (Goofy: P -> R).
         {
           remember (P -> R) as A; remember (Q -> S) as B. apply proj1 in H0.
           assumption.
         }
         auto.
       - apply or_intror.
         assert (Goofy: Q -> S).
         {
           remember (P -> R) as A; remember (Q -> S) as B.
           apply proj2 in H0. assumption.
         }
         auto.
        }
      assert ((not  ((unit_root (n + 1) 1) - 1 <> 0)) \/ (not (sum_of_roots (n + 1) (2 ^ (n + 1)) <> 0))).
      {
        apply Classical_Prop.not_and_or. assumption.
      }
      simpl in H0.
      unfold neq in H0.
      Search Cmult 0.
      assert (Longlongago: ((not  ((unit_root (n + 1) 1) - 1 <> 0)) ->
                            ( (unit_root (n + 1) 1) - 1 = 0) ) /\   ( (not (sum_of_roots (n + 1) (2 ^ (n + 1)) <> 0))
                                                                     ->   (sum_of_roots (n + 1) (2 ^ (n + 1)) = 0))).
      {split.  apply Classical_Prop.NNPP. apply Classical_Prop.NNPP.  }
      eapply FineFine.
      eapply Longlongago.
      assumption.
      }
      assert (LeftNotCase:  (unit_root (n + 1) 1) - 1 <> 0).
      {
        apply nplus1rootNon0. rewrite Nat.add_1_r. assumption.
      }
      assert (Tired: forall (P Q: Prop), (P \/ Q) -> (not P) -> Q).
      {
        intros.  auto.
        assert ((~P) \/ Q).
        {
          Search or.
          apply or_introl.
          assumption.
        }
        auto.
        assert ((P \/ Q) /\ (~P \/ Q)).
        {
          split. assumption. auto.
        }

        Search Prop.
        assert (abc: forall (A B C: Prop), (A\/C) /\ (B\/C) ->  ((A/\B)\/ C)).
        {
          intros.
          assert(H5: A\/C).
          {
            apply proj1 in H4. assumption.
          }
          assert(H6: B\/C).
          {
            apply proj2 in H4. auto.
          }
          destruct H5.
          - destruct H6.
            assert (H7: A/\B).
            {
              split. assumption. assumption.
            }
            apply or_introl. assumption.
            apply or_intror. assumption.
          -   apply or_intror. assumption.
        }
        assert (QQQ: (P/\~P)\/ Q). {apply abc. assumption. }
                                  Search Prop.
        destruct QQQ.
        - Search False.
          apply False_ind.
          assert (H9: P).
          {
            apply proj1 in H4. assumption.
          } rewrite neg_false in H1. rewrite H1 in H9.
          auto.
        -  assumption.
      }
      apply Tired in EitherOr.
      assumption.
      assumption.
Qed. 




