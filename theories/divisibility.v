From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint .
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly.

From mathcomp Require Import algC.
From mathcomp.zify Require Import zify. 
From Hammer Require Import Tactics .
From Hammer Require Import Hammer .

Require Import Friendship.bigops.
Require Import Friendship.adj2_matrix.
Require Import Friendship.matrix_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.
(*Local Open Scope order_scope.*)
(*Import order.Order.TotalTheory.*)
(*Import order.Order.POrder.*)
From mathcomp Require Import ssrnum closed_field ssrint rat intdiv order.
  From mathcomp Require Import algebraics_fundamentals.

  From mathcomp Require Import tuple seq.

  From mathcomp Require Import div.

Section div.
  Variable n k: nat.
  Definition adj2n := adj2 n k.
  
  Context (kge1: (k >=1) %N) (nge1: (n >= 1) %N) (A: 'M[R]_(1+(n-1)))
    (A_sqr : is_square_root k A) (A_tr0 : \tr A = 0)
    (nk_eq: n = (k*k - k + 1)%N).

  
  Import Num.Theory.
  
  (* Kanske Num.nneg ?
     Vet också (x2 \is Num.nneg)
   *)
  
  Lemma idomain_sqrt (x x2: algC) :
    x ^ 2 = x2 ->
    x == (sqrtC x2) \/ x == - (sqrtC x2).
  Proof.
    clear; move=> x2_eq.
    have x2_eq' : (x ^+ 2 = x2) by sauto.
    have sqrs : (x - (sqrtC x2)) * (x + (sqrtC x2)) == 0
      by rewrite -subr_sqr x2_eq' sqrtCK  subr_eq0.
    rewrite mulf_eq0 in sqrs.
    move: sqrs; move => /orP [root|root]; [left |right].
    by rewrite -subr_eq0.
    by rewrite -subr_eq0 opprK.
  Qed.

  Lemma all2_nseq {T} (l : seq T) P (x: T) nn :
    all2 P l (nseq nn x) -> all (fun li => P li x) l.
  Proof.
    clear.
    rewrite all2E; move: nn.
    elim: l => [nn| l0 l indH nn allH] //=.
    move: allH; move=> /andP [sz allH].
    apply (elimT eqP) in sz.
    move: nn sz allH => [| nn] sz allH; [by sauto |].
    move: allH; move=> /andP [pl0x allH].
    apply (introT eqP) in sz.
    apply /andP. 
    exact (conj pl0x  (indH _ (introT andP (conj sz allH)))).
  Qed.
  
  Lemma sum_of_roots (μs : seq algC):
    let a := fun (i: 'I_(size μs)) =>
               tnth (in_tuple μs) i == sqrtC (k - 1)%:R in 
    all2 (fun μ λ => μ^2 == λ) μs (nseq (n-1) (k - 1)%:R) ->
    \sum_(μ <- μs) μ =
      (sqrtC (k - 1)%:R)
        *+ count a (index_enum (ordinal_finType (size μs)))
      -
        (sqrtC (k - 1)%:R) *+
          count (negb \o a) (index_enum (ordinal_finType (size μs))).
  Proof.
    clear nge1 A A_sqr A_tr0 nk_eq. (* prbl don't need k >= 1 *)
    simpl. move=> all2_squares. 
    have all_squares  := (all2_nseq all2_squares).
    clear all2_squares.
    rewrite big_tnth.

    set a := fun (i: 'I_(size μs)) =>
               tnth (in_tuple μs) i == sqrtC (k - 1)%:R.
    set F  := (fun (b: bool) => if b then sqrtC (k - 1)%:R
                              else -sqrtC (k - 1)%:R) : bool -> algC.
        
    rewrite (@eq_bigr algC _ _ _ _ _ _
               (fun i => F (a i))); last first. {
      move=> i _.
      subst F; subst a; simpl.
      rewrite (tnth_nth 0) //=.
      have sqr : μs`_i ^2 = (k - 1)%:R. {
        case: i => //=.
        move=> m m_leμ.
        move: (elimT (@all_nthP _ (fun li : algC => li ^ 2 == (k - 1)%:R)
                        μs 0) all_squares m m_leμ).
        apply /eqP.
      }
      
      move: sqr.
      move=> /idomain_sqrt.
      
      case: (ifP (μs`_i == sqrtC (k - 1)%:R)) => [eq_r _| neq_r fls_if]. {
        by apply/eqP.
      } {
        elim fls_if; rewrite //=.
        apply/eqP.
      }
    }
    clear all_squares.
        
    rewrite (@big_bool _ 'I_(size μs) _ a F ).

    set npos := count a (index_enum (ordinal_finType (size μs))).
    set nneg := count (negb \o a) (index_enum (ordinal_finType (size μs))).
    unfold F.
    apply: f_equal.
    by rewrite mulNrn.
  Qed.

  Lemma kn_1 : (k+n-1)%N = (k*k)%N.
    rewrite {}nk_eq.
    move: kge1 k => /ltP kge1' [|k']; lia.
  Qed.

    
  Local Open Scope int_scope.
  
  Lemma tr_adj_rel :
     Posz (k-1) %| Posz (k*k).
  Proof.
    have trN : -\tr A = 0%R
      by rewrite A_tr0 oppr0.

    have zero_char_poly : 0%R = (char_poly A)`_(1+(n-1)).-1
      by rewrite -[in LHS] trN  -char_poly_trace.

    have [μs char_poly props] := (adj_mtx_char_poly kge1 nge1 A_sqr).
    rewrite {}char_poly viete_sum in zero_char_poly; last first. {
      by rewrite size_tuple; lia.
    }
    
    have eigvals_sum0 : \sum_(μ <- μs) μ = 0%R. {
      by rewrite -(opprK (\sum_(μ <- μs) μ)) -zero_char_poly oppr0.
    }       
    clear zero_char_poly trN A_tr0 .
    move: μs props eigvals_sum0 => μs.
    case: μs => μs; case: μs => [|μ μs] sz_μs props eigvals_sum0 //=.
    simpl in *.
    
    rewrite big_cons in eigvals_sum0.
    move: props. move => /andP [μ_sq props].
    rewrite (sum_of_roots props) //= in eigvals_sum0.
    set a := count
               (fun i : 'I_(size μs) =>
                  tnth (in_tuple μs) i == sqrtC (k - 1)%:R)
               (index_enum (ordinal_finType (size μs))).
    set b := count
               (negb \o
                  (fun i : 'I_(size μs) =>
                     tnth (in_tuple μs) i == sqrtC (k - 1)%:R))
               (index_enum (ordinal_finType (size μs))).
    set sqk := sqrtC (k - 1)%:R : algC.
    rewrite -/a -/b -/sqk in eigvals_sum0.
    rewrite -mulr_natr in eigvals_sum0.
    rewrite -[sqk *+ b]mulr_natr -mulrN -mulrDr in eigvals_sum0.
    have μ_sqk : -μ = sqk * (a%:R - b%:R). {
      by rewrite - (add0r (sqk * (a%:R - b%:R)))
         -(addNr μ) -addrA eigvals_sum0 addr0.
    }
    clear eigvals_sum0.
    have sqrs := (f_equal (fun x => x *x) μ_sqk).
    rewrite mulrN mulNr opprK (*-expr2 exprnP*) in sqrs.
    rewrite [in RHS]mulrA [in RHS]mulrC in sqrs.
    rewrite exprSz expr1z in μ_sq.
    rewrite (elimT eqP μ_sq) in sqrs.
    have  sqk_: (sqk * (a%:R - b%:R) * sqk) = (k-1)%:R * (a%:R - b%:R). {
      rewrite -mulrA mulrC -mulrA  -expr2 sqrtCK mulrC.
      by apply: f_equal.
    }
    rewrite {}sqk_ mulrA in sqrs.
    rewrite [in X in X * (a%:R - b%:R)] mulrC in sqrs.
    have nk_eq_ : (k + n - 1)%N = (k*k)%N. {
      rewrite nk_eq.
      move: kge1 nge1 k n => /ltP kge1' /ltP nge1' [|k'] [|n']; lia.
    }
    rewrite nk_eq_ in sqrs.
    clear -sqrs.
    move: sqrs.
    rewrite !pmulrn  -mulrzBr -!intrM.
    move /intr_inj ->.
    apply: dvdz_mulr. apply: dvdz_mulr. apply: dvdzz.
  Qed.

  Local Open Scope nat_scope.
  Lemma tr_adj_rel_nat :
    (k-1)%N %| (k*k)%N.
  Proof.
    rewrite -(absz_nat (k*k)) -(absz_nat (k-1)) -dvdzE.
    exact tr_adj_rel.
  Qed.

  Lemma k_is_2: k = 2%N.
  Proof.
    have kd_lem := tr_adj_rel_nat.
    clear -kge1 kd_lem. 
    have k1dk: (k-1) %| k. {
      have div_k1k: (k-1) %| (k-1)*k
        by exact  (dvdn_mulr _ (dvdnn _)).
      rewrite -(dvdn_addl _ div_k1k).
      have -> : k + (k - 1) * k = k * k  . {
        move: kge1 k => /ltP kge1' [| k']; lia.
      }
      exact  kd_lem.
    }
    have k1d : k-1 %| 1. {
      rewrite -(dvdn_addl _ (dvdnn (k - 1))).
      have <- : k = 1 + (k-1) by move: kge1 =>  /ltP  ; lia.
      exact k1dk.
    }
    rewrite dvdn1 in k1d.
    move: k1d. move=>/eqP k1d.
    sauto.
  Qed.
End div.

