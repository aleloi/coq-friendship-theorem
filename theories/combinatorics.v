(*From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg  (*zmodp*) matrix (* mxalgebra poly (* polydiv *)
  mxpoly *)       .
From mathcomp Require Import bigop.


From Hammer Require Import Tactics .
From Hammer Require Import Hammer .

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Friendship.adj2_matrix.

Section friendship_sec.
  
  Context (T: finType) (T_nonempty :  [set: T] != set0)
    (F: rel T) (Fsym: symmetric F) (Firr: irreflexive F)
    (* I first tried with  "Co: forall (m n: T), m != n -> T"
       but gave up when I wanted a total version, and couldn't prove that
       it was equal to 'Co' whenever m != n *)
    (Co: forall (m n: T), T)
  
  (Col : forall m n (mNn: m != n), F m (Co m n))
  (Cor : forall m n (mNn: m != n), F n (Co m n))
  (CoUnique : forall m n l (mNn: m != n), F m l -> F n l -> l = Co m n).

  Lemma T_elem: T.
  Proof.
    clear -T_nonempty.
    move: (@enum_default T [set: T] ).
    move: T_nonempty; rewrite -card_gt0.
    sauto.
  Qed.

  Definition n := #|[set: T]|.
  Lemma nge1 : n >= 1.
  Proof.
    by move: T_nonempty; rewrite card_gt0.
  Qed.

  

  Lemma Co_sym m n (mNn: m != n) (nNm: n != m): Co m n = Co n m.
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
  Definition k := deg T_elem.

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


  (*Definition map_adj (u v w: T) := Co v w.*)
  
  (*Definition map_adj' u v 
    (uNv: u != v) (nFuv: ~~(F u v)) w (wAdjU: w \in adj u) 
    := (Co (v_not_in_adj_u  wAdjU nFuv)).*)
  
  Lemma map_adj_im u v (*(uNv: u != v) *)
    (nFuv: ~~(F u v)) w (wAdjU: w \in adj u) :
    Co v w \in adj v.
  Proof.
    rewrite in_set.
    apply: Col; apply: (@v_not_in_adj_u u); by [].
  Qed.

  Lemma Feq u v: F u v -> u != v.
  Proof.
    by case: (@eqP _ u v); [move => ->; rewrite Firr|].
  Qed.
  
  Lemma map_adj_inj u v (uNv: u != v) (nFuv: ~~(F u v)):
    {in adj u &, injective (Co v) }.
  Proof.
    move => w1 w2  w1adj w2adj coeq.
    rewrite in_set in w1adj; rewrite in_set in w2adj.

    have vw1 : v != w1. {
      case: (@idP (v == w1)) => /eqP vw1.
      by rewrite -vw1 in w1adj; move: nFuv => /negP; firstorder.
      by firstorder.
    }
    have vw2 : v != w2. {
      case: (@idP (v == w2)) => /eqP vw2.
      by rewrite -vw2 in w2adj; move: nFuv => /negP; firstorder.
      by firstorder.
    }
    set x := Co v w1.
    have fxw1 := (Cor vw1). 
    have fxw2 := (Cor vw2). 
    rewrite -/x in fxw1.
    rewrite -coeq -/x in fxw2.

    have w1x: w1 != x by apply Feq.
    have w2x: w2 != x by apply Feq.

    have ux : u != x. {
      case: (@eqP _ u x) => ux.
      move: (Col vw1); rewrite -/x -ux Fsym.
      by move: nFuv => /negP; clear; firstorder.
      by [].
    } 
    
    (*
      u ... w1
      .      .
      .      .
      w2 ... [v w1] = [v w2] = x 
     *)

    transitivity (Co u x). {
      apply: CoUnique => //=.
      rewrite Fsym //=.
    } {
      symmetry.
      apply: CoUnique => //=.
      rewrite Fsym //=.
    }
  Qed.

  
  Lemma almost_regular_leq u v:
    ~~(F u v) -> deg u <= deg v.
  Proof.
    case: (@eqP _ u v) => uv fuv; [by rewrite uv leqnn |].
    move: uv => /eqP uv.
    rewrite /deg -(card_in_imset (map_adj_inj uv fuv  ));
      apply subset_leq_card.
    
    have ->: [set Co v x | x in adj u] \subset adj v. {
      rewrite subsetE.
      apply  /pred0P => x //=.
      case: (@idP (x \notin adj v)) => //= xNotAdj.
      apply/eqP; rewrite eqbF_neg; apply /negP.
      move=> /imsetP [w wadj xeq].
      have in_adj := (map_adj_im  fuv wadj).
      rewrite -xeq in in_adj.
      move: xNotAdj => /negP; firstorder.
    }
    by [].
  Qed.

  Lemma almost_regular_eq u v: ~~(F u v) -> deg u = deg v.
  Proof.
    move=> fuv.
    have /eqP := almost_regular_leq fuv.
    rewrite Fsym in fuv.
    have /eqP := almost_regular_leq fuv.
    ssrnat_lia.
  Qed.
  
  Section assume_contra.
    Context (no_hub: forall u, {v | ~~(F u v) & u != v}).

    
    Lemma almost_almost_regular x u:
      T_elem != x -> ~~(F T_elem x) -> u != Co T_elem x -> deg u = k.
    Proof.
      set t := T_elem.
      set ctx := Co t x.
      move=> tx Ftx uctx.
      have degx := almost_regular_eq Ftx.
      rewrite -/k in degx.
      case: (@idP (F t u)); case: (@idP (F x u));
        [move=> fxu ftu | move=>/negP f _ |
          move=> _ /negP f  ..
        ]; try rewrite -(almost_regular_eq f) //=. {
        rewrite (CoUnique tx ftu fxu) in uctx.
        move: uctx => /eqP; firstorder.
      }
    Qed.
    
    Lemma regular u: deg u = k.
    Proof.
      set t := T_elem.
      have [x ftx tx] := no_hub t.

      have almost_all: forall v, v != Co t x -> deg v = k by
          move=> v; apply (almost_almost_regular tx ftx).
      
      case: (@idP (u != Co t x)); try apply (almost_almost_regular tx ftx  ).
      move=> /negP /negPn /eqP uco.
      rewrite -uco in almost_all.
      have [y fuy uy] := no_hub u.
      
      rewrite (almost_regular_eq fuy) .
      rewrite eq_sym in uy.
      
      exact (almost_all y uy).
    Qed.
    
    Lemma kge1: k >= 1.
    Proof.
      set t := T_elem.
      rewrite card_gt0 -/t; apply/set0Pn; apply: ex_of_sig.
      have [y _ ty] := no_hub t.
      exists (Co t y).
      rewrite finset.inE.
      apply (Col ty).
    Qed.

    Definition nn := #|[eta T]|.
    Context (R: ringType).
    Local Open Scope ring_scope.
    Definition A : 'M[R]_nn :=
      \matrix_(i < nn, j < nn) (F (enum_val i) (enum_val j))%:R.

    Lemma A_diag i: A i i = 0.
    Proof.
      by rewrite !mxE Firr.
    Qed.

    Lemma A_tr : \tr A = 0.
    Proof.
      rewrite /mxtrace  (eq_bigr (fun=> 0)).
      by rewrite big_const_ord  GRing.iter_addr GRing.addr0 GRing.mul0rn .
      by move=> i _; rewrite A_diag.
    Qed.

    Lemma A2_diag i: (A*m A) i i = k%:R.
    Proof.
      
      rewrite /mulmx !mxE (eq_bigr (fun j=> if (F (enum_val i) (enum_val j))
                                            then 1
                                            else 0)) -/nn.
      rewrite (bigID (fun x=> F (enum_val i) (enum_val x))) //= -/nn.
      rewrite [in X in X + _](eq_bigr (fun=> 1)).
      rewrite [in X in _ + X](eq_bigr (fun=> 0)).
      rewrite !GRing.sumr_const GRing.mul0rn GRing.addr0 //=.
      apply: f_equal.
      rewrite -(regular (enum_val i)) /deg /adj.
      
      rewrite -(@card_imset _ _ enum_val _ enum_val_inj) //=.
      apply: f_equal; apply: f_equal; apply: f_equal.
      apply/setP => x.

      rewrite !inE.

      case: (@idP (F (enum_val i) x)) => Fix ; apply/idP. {
        apply /(@imsetP (ordinal_finType nn) T enum_val ).
        exists (enum_rank x).
        by rewrite /in_mem //= enum_rankK.
        by rewrite enum_rankK.
      } {
        
        move => /(@imsetP (ordinal_finType nn) T enum_val ) [j].
        rewrite /in_mem //= => Fij xj.
        rewrite xj in Fix.
        firstorder.
      }
      by move => j /negPf ->.
      by move => j -> . {
        move=>  j _.
        rewrite !mxE.
        case: (@idP (F (enum_val i) (enum_val j))) => Fij. {
          rewrite Fsym in Fij.
          by rewrite GRing.mul1r  Fij.
        }
        by rewrite GRing.mul0r.
      }
    Qed.

    (*
    Lemma A2_off_diag i j:  i != j -> (A*m A) i i = k%:R.
    Proof.
     *)
      
  End assume_contra.
End friendship_sec.
