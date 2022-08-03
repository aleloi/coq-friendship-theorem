From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.

From Hammer Require Import Tactics .
From Hammer Require Import Hammer .

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section friendship_sec.
    
  Context (T: finType) (T_nonempty : [set: T] != set0)
    (F: rel T) (Fsym: symmetric F) (Firr: irreflexive F)
    (Co: forall (m n: T), m != n -> T)
  
  (Col : forall m n (mNn: m != n), F m (Co _ _ mNn))
  (Cor : forall m n (mNn: m != n), F n (Co _ _ mNn))
  (CoUnique : forall m n l (mNn: m != n), F m l -> F n l -> l = Co _ _ mNn).

  Lemma Co_sym m n (mNn: m != n) (nNm: n != m): Co mNn = Co nNm.
  Proof.
    firstorder.
  Qed.
    
  Lemma andWl a b : a && b -> a.
  Proof.
    move=> /andP; firstorder.
  Qed.
  Lemma andWr a b : a && b -> b.
  Proof.
    move=> /andP; firstorder.
  Qed.
    
  (* Tried with #|[set a; b; c; d]| = 4, but
     didn't manage to rewrite with 'setUC cardsU1'.
     Maybe try with 'uniq' ?
     There is '[set x in lst]' and CardEq.

    Should the result be 'path F a [b, c, d, a]' ?
   *)
  From mathcomp Require Import all_ssreflect.
  Lemma noC4 (a b c d : T):
    uniq [:: a ; b; c; d] ->
    ~(path F a [:: b; c; d; a]).
  Proof.
    clear -Fsym CoUnique.
    move=> card4.
    rewrite uniq_pairwise in card4.
      
    have bNc: b != d. {
      move: card4.
      rewrite pairwise_cons.
      move=> /andWr.
      rewrite pairwise_cons.
      move=> /andWl /andWr /andP.
      firstorder.
    }
     
    have aNc: a != c. {
      move: card4.
      rewrite pairwise_cons.
      by move => /andWl /andWr /andWl.
    }

    rewrite //= andbT;
      move=> /andP [Fab /andP [Fbc /andP [Fcd Fda] ] ].
    
    have Fcb : F c b by rewrite Fsym.
    have Fad : F a d by rewrite Fsym.
    
    have b_co_ac := CoUnique aNc Fab Fcb.
    have d_co_ac := CoUnique aNc Fad Fcd.
    rewrite b_co_ac d_co_ac in bNc.
    move:  bNc => /eqP. firstorder.
  Qed.

  Definition adj u := [set w | F u w].
  Definition deg u := #|adj u|.

  Lemma v_not_in_adj_u u v w:
    w \in adj u -> ~~(F u v) -> v != w.
  Proof.
    rewrite in_set.
    move=> Fuw nFuv.
    apply/negP.
    move=> /eqP vW.
    rewrite -vW in Fuw.
    move: nFuv => /negP.
    firstorder.
  Qed.

  Definition adj_u_adj_v_f u v 
    (uNv: u != v) (nFuv: ~~(F u v)) w (wAdjU: w \in adj u) 
    := (Co (v_not_in_adj_u  wAdjU nFuv)).

  Check (adj_u_adj_v_f _).

  Lemma adj_u_adj_v_f_to_adjv u v (uNv: u != v) 
    (nFuv: ~~(F u v)) w (wAdjU: w \in adj u) :
    adj_u_adj_v_f uNv nFuv  wAdjU \in adj v.
  Proof.
    rewrite /adj_u_adj_v_f in_set.
    apply: Col.
  Qed.

  (*Lemma adj_u_adj_v_f_injective :
    TODO: extend the function so that it is total;
    prove that it's injective {in adj u}
   *)

  
  Lemma almost_homogeneous_leq u v:
    ~~(F u v) -> deg u <= deg v.
  Admitted.
  
End friendship_sec.
