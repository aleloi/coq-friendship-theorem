(*From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype finfun bigop finset.
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg  (*zmodp*) matrix (* mxalgebra poly (* polydiv *)
  mxpoly *)       .
From mathcomp Require Import bigop.

From mathcomp Require Import algC.

From Hammer Require Import Tactics .
From Hammer Require Import Hammer .

From mathcomp.zify Require Import zify. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Friendship.adj2_matrix.
Require Import Friendship.divisibility.
Require Import Friendship.matrix_casts.

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

  Definition T_elem:  T := (xchoose (set0Pn _ T_nonempty)).
  
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
    lia.
  Qed.
  
  Section assume_contra.
    Context (no_hub': forall u, [exists v, ~~(F u v) && (u != v)]).

    (* sig version of no_hub'. This is usable, in contrast to no_hub'. *)
    Lemma no_hub: forall u, {v | ~~(F u v) & (u != v)}.
    Proof.
      move=>u.
      have /existsP nhu := (no_hub' u).
      move: (sigW nhu) => [v /andP [p1 p2]].
      by exists v.
    Qed.
    
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
    Definition R := algC.
    
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


    Definition adj' u := [set w | F u w && (w != T_elem)].
    
    Lemma adj'_disjoint (u1 u2 : T):
      u1 \in adj T_elem -> u2 \in adj T_elem ->
      u1 != u2 -> [disjoint (adj' u1) & (adj' u2)].
    Proof.
      rewrite /disjoint /adj !inE => u1adj u2adj u12.
      apply/pred0P => x //=.
      case: (@idP (x \in adj' u1)); case: (@idP (x \in adj' u2));
        rewrite /adj' //= !inE => /andP [fu2x xt] /andP [fu1x _].
      rewrite Fsym in fu2x.
      rewrite Fsym in fu1x.
      move: u12.
      rewrite (CoUnique xt fu1x u1adj) (CoUnique xt fu2x u2adj).
      by move => /eqP.
    Qed.

    Lemma adj'_and_tU u:
      u \in adj T_elem -> (adj' u) :|: [set T_elem]  = adj u.
    Proof.
      rewrite inE -setP => fut x.
      rewrite /adj /adj' !inE.
      rewrite Fsym in fut.
      case: (@idP (x == T_elem)).
      by move=> /eqP ->; rewrite fut.
      by rewrite Bool.andb_true_r Bool.orb_false_r.
    Qed.

    Lemma adj'_and_t_disj u:
      u \in adj T_elem -> [disjoint (adj' u) & [set T_elem] ].
    Proof.
      rewrite /disjoint /adj' => uadj. 
      apply/pred0P => x; rewrite !inE //=.
      by case: (x == T_elem) => //=; rewrite Bool.andb_false_r ?Bool.andb_true_r .
    Qed.

    Lemma adj'_card u:
      u \in adj T_elem -> #|adj' u| = (k-1)%N.
    Proof.
      set k' := #|adj' u|.
      move=> uadj.
      have: (k' + 1)%N = k. {
        rewrite /k' -(cards1 T_elem) -(regular u) /deg -(adj'_and_tU uadj).

        have aoue := (eq_leqif (leq_card_setU (adj' u) [set T_elem]) ).
        rewrite (adj'_and_t_disj _) in aoue.
        by move: aoue => /idP /eqP ->.
        by [].
      }
      move: k kge1 => [|k''] //=.
      lia.
    Qed.
    Definition adj_cover :=[set adj' u | u in adj T_elem].
    Definition dist2 := cover adj_cover.

    Lemma k_not_1 : k != 1%N.
      (* Bevis: om k = 1, är adj T_elem = {a}.
         Det finns x, x != T_elem med ~~F T_elem x.
         x != a, för att F T_elem a och ~~F T_elem x.
         Co x t är granne med t, alltså är det a.
         Co x t har kant till x, alltså har a 2 kanter, vilket motsäger att
           allt har 1 kant.
       *)
    Proof.
      case: (@idP (k != 1%N)) => //= /negP.
      rewrite Bool.negb_involutive => /eqP k1.
      have adj1 u: #|adj u| == 1%N
        by apply/eqP; rewrite -k1 -/(deg u)  (regular u).

      (*Definition adj_ := forall v, cards1P (adj1 v).*)
      move: (cards1P (adj1 T_elem)) => [a seta].
      move: (no_hub T_elem) => [x ftx tx].
      have aadj : a \in adj T_elem by rewrite seta set11.
      have fta : F T_elem a by rewrite inE in aadj.

      have xa : x != a. {
        case: (@idP (x != a)) => //= /negP.
        rewrite Bool.negb_involutive => /eqP xa.
        rewrite xa in ftx.
        by move: ftx  => /negP; rewrite fta.
      }

      set a' := Co x T_elem.
      rewrite eq_sym in tx.
      have coF := Cor tx.
      have a'adj : a' \in adj T_elem
          by rewrite inE /a'.
      have a'a: a' = a by rewrite seta in a'adj; move: a'adj => /set1P.
      
      have uea := Col tx.
      rewrite -/a' a'a in uea.

      have xadj : x \in adj a by rewrite inE Fsym.
      have tadj : T_elem \in adj a by rewrite inE Fsym.

      move: (cards1P (adj1 a)) => [z setz].
      rewrite setz in xadj tadj.
      move: xadj => /set1P xz.
      move: tadj => /set1P tz.
      rewrite -xz in tz.
      move: tx => /eqP tx.
      symmetry in tz.
      by move: (tx tz).
    Qed.

    Lemma card_cover:  #|adj_cover| = k.
    Proof.
      rewrite /adj_cover card_in_imset. {
        by []. } {
        move => w1 w2  w1adj w2adj coeq.
        have disjF := adj'_disjoint w1adj w2adj.
        case: (@idP (w1 == w2)) => //=. by move=> /eqP. {
          move=> /negP /disjF /setDidPl.
          rewrite coeq setDv => w20.
          have : #|adj' w2| = 0%N
            by rewrite -w20 cards0.
          
          rewrite (adj'_card w2adj).

          move=> k_eq.
          have k1 : k = 1%N
            by move: k  kge1 k_eq => [| k'] //=; lia.
          move: k_not_1; rewrite k1.
          move =>  /eqP; clear; firstorder.
        }
      }
    Qed.


    Lemma disjoint_cover : trivIset adj_cover.
    Proof.
      apply/trivIsetP => A B /imsetP [u ut] -> /imsetP [v vt] -> sets_diff.
      case: (@idP (u != v)).
      by move=> uv; exact (adj'_disjoint ut vt uv). {
        move => /idP /eqP uv.
        rewrite uv in sets_diff.
        move: sets_diff; rewrite eq_refl //=.
      }
    Qed.

    Lemma dist2_card : #|dist2| = (k*(k-1))%N.
    Proof.
      have := (eq_leqif (leq_card_cover adj_cover) ).
      rewrite disjoint_cover /dist2; move=> /eqP -> .
      rewrite (eq_bigr (fun=> (k-1)%N)). {
        rewrite big_const iter_addn_0 [in RHS]mulnC.
        apply: f_equal.
        exact card_cover.
      }
      move=> A /imsetP [v vt] ->.
      by apply: adj'_card.
    Qed.

    Lemma adjT_subs_cover: adj T_elem \subset dist2.
    Proof.
      rewrite subsetE.
      apply/pred0P => x; rewrite !inE //=.
      apply: negPf.
      apply /negP => /andP [ xd ftx].
      set y := Co T_elem x.
      have xt : T_elem != x. {
        case: (@idP (T_elem != x)) => //= /negP /negPn /eqP tx.
        by rewrite tx Firr in ftx.
      }
      have ty := Col xt.
      have xy := Cor xt.
      rewrite -/y in ty xy.
      have xadjy : x \in adj' y. { 
        rewrite inE.
        rewrite eq_sym in xt.
        by rewrite xt Bool.andb_true_r Fsym.
      }
      rewrite /dist2 /cover in xd.
      move: xd => /bigcupP notin.
      apply: notin => //=.
      exists (adj' y).
      rewrite /adj_cover.
      apply /imsetP.
      exists y.
      rewrite inE.
      by [].
      by [].
      by [].
    Qed.

    Lemma adjT_cover_noT: [disjoint dist2 & [set T_elem]].
    Proof.
      rewrite disjoint_sym /dist2 /cover.
      apply /bigcup_disjointP => A /imsetP[u ut] ->.
      rewrite disjoint_sym.
      exact (adj'_and_t_disj ut).
    Qed.

    Lemma all_covered : [set: T] =  dist2 :|: [set T_elem].
    Proof.
      apply/setP => x //=.
      rewrite inE.
      symmetry.
      apply/idP.
      case: (@idP (T_elem == x)). {
        by move=> /eqP <-; rewrite set1Ur. } {
        move=> /negP tx.
        set y := Co T_elem x.
        have xy : x \in adj' y. {
          rewrite inE.
          have yx := Col tx.
          have yt := Cor tx.
          by rewrite Fsym yt Bool.andb_true_l eq_sym.
        }
        
        apply/setUP; left.
        rewrite /dist2 /cover.
        apply /bigcupP.
        exists (adj' y).
        rewrite /adj_cover.
        apply /imsetP.
        exists y. 
        by rewrite inE (Col tx).
        by [].
        by [].
      }
    Qed.

    Lemma T_size: n = ((k*(k-1))%N + 1)%N.
    Proof.
      rewrite /n -dist2_card  -(cards1 T_elem).
      have full_card := (eq_leqif (leq_card_setU dist2 [set T_elem]) ).
      rewrite adjT_cover_noT  in full_card.
      move: full_card => /idP /eqP <-.
      by rewrite all_covered.
    Qed.

    Lemma nk: n = (k*k - k + 1)%N.
      rewrite T_size.
      move: k kge1 => [| k'] //=.
      by lia.
    Qed.

    Lemma A2_off_diag i j:  i != j -> (A*m A) i j = 1%:R.
    Proof.
      move=> ij.
      rewrite /mulmx !mxE /A //=
        (eq_bigr (fun α=> if (F (enum_val i) (enum_val α)) &&
                               (F (enum_val α) (enum_val j))
                          then 1
                          else 0)) -/nn. 

      rewrite (bigID (fun α=> (F (enum_val i) (enum_val α)) &&
                                (F (enum_val α) (enum_val j)))) //= -/nn.
      rewrite [in X in X + _](eq_bigr (fun=> 1)).
      rewrite [in X in _ + X](eq_bigr (fun=> 0)).
      rewrite !GRing.sumr_const GRing.mul0rn GRing.addr0 //=.
      set x := enum_val i.
      set y := enum_val j.
      set z := Co (enum_val i) (enum_val j).
      have xy: x != y. {
        case: (@idP (x != y)) => //= /negP.
        rewrite Bool.negb_involutive => /eqP xy.
        rewrite (enum_val_inj xy) in ij.
        move: ij => /eqP; firstorder.
      }
      rewrite -(cards1 z).
      rewrite -(@card_imset _ _ enum_val _ enum_val_inj) //=.
      apply/f_equal /f_equal /f_equal /f_equal.
      apply/setP => t.
      rewrite !inE //=.
      have Fxz := Col xy.
      have Fyz := Cor xy.
      rewrite -/z in Fxz Fyz.
      rewrite Fsym in Fyz.
      
      case: (@idP (t == z)) => tz ; apply/idP. {
        apply /(@imsetP (ordinal_finType nn) T enum_val ).
        exists (enum_rank z).
        by rewrite /in_mem //= enum_rankK Fxz Fyz.
        by move: tz => /eqP ->; rewrite enum_rankK.
      } {
        
        move => /(@imsetP (ordinal_finType nn) T enum_val ) [jj].
        rewrite /in_mem //= => /andP [fxjj fjjy] tjj.
        rewrite Fsym in fjjy.
        have z_uniq := CoUnique xy fxjj fjjy.
        rewrite -tjj in z_uniq.
        rewrite z_uniq /z -/x -/y in tz.
        apply tz.
        by apply eq_refl.
      }
      by move => jj /negPf ->.
      by move => jj -> . {
        move=>  jj _.
        rewrite !mxE.
        case: (@idP (F (enum_val i) (enum_val jj)  && (F (enum_val jj) (enum_val j))))
            => fijj . {
          move: fijj => /andP [fijj fjji].
          rewrite fijj.
          rewrite fjji .
          by rewrite GRing.mul1r .
        }
        move: fijj  => /negP.
        rewrite negb_and => /orP some0.
        by case: some0 => /negPf ->; rewrite ?GRing.mul0r ?GRing.mulr0.
      }
    Qed.

    Lemma adj2_eq : A*m A = (const_mx 1) +
                              (k-1)%:R%:M.
    Proof.
      apply/matrixP => i j; 
      case: (@eqP _ i j). {
        move=> ->.
        rewrite A2_diag !mxE .
        rewrite eq_refl GRing.mulr1n.
        move: k kge1 => [|k'] //= _.
        have -> : (k'.+1-1)%N = k' by lia.
        have -> : k'.+1 = (1+k')%N by lia.
        by rewrite GRing.natrD.
      } {
        move=> /eqP ij.
        rewrite A2_off_diag //= !mxE.
        by rewrite (introFn idP ij) GRing.mulr0n GRing.addr0.
      }
    Qed.

    Lemma n_eq: nn = n.
    Proof.
      rewrite /nn /n.
      by rewrite cardsE.
    Qed.
      
    Lemma cast_eq:  nn = (1+(n-1))%N.
    Proof.
      rewrite n_eq.
      by move: n nge1 => [| n'] //=; lia.
    Qed.

    Definition A' := (castmx (cast_eq, cast_eq) A).

    (* Can't I use the previously proven version ?! *)
    Lemma A'_tr : \tr A' = 0.
    Proof.
      rewrite tr_castmx /mxtrace (eq_bigr (fun => 0)).
      by rewrite big_const_ord  GRing.iter_addr GRing.addr0 GRing.mul0rn .
      by move=> i _; rewrite A_diag.
    Qed.

    Lemma Asqrt : is_square_root k A'.
    Proof.
      by rewrite /is_square_root /adj2  /A' -mulmx_castmx  adj2_eq
          summx_castmx castmx_const scalar_mx_castmx.
    Qed.

    Lemma k_not_2: k <> 2%N.
    Proof.
      set t := T_elem.
      (*
        The proof:
        If k = 2, |adj t| = 2.
        |adj t| is not empty, so there exists a ∈ adj t
        some lemma should give [set a] \subset adj t and
        adj t = (adj t ⧵ [set a]) ⊎ [set a] as a disjoint union.
        By disjointness and 'card', |adj t ⧵ [set a]| = 1.
        Thus |adj t ⧵ [set a]| = [set b].
        a ∉ (adj t ⧵ [set a]), therefore a ∉ [set b], therfore a ≠ b.
        Then adj t = [set b] ⊎ [set a] with a != b, so adj t = [set a, b].
        --
        We have F t a and F t b, since both are in adj t.
        It follows that a != t and b != t (we already had a != b).
        There is x ∉ adj t with x ≠ t by the 'no_hub' property.
        We have x≠a, x≠b, because otherwise we would have (e.g.) both
            F t a and ~~F t a.
        Therefore all a, b, t, x are different, I think we can prove
           uniq [a, b, c, d]
        A lemma implies #|[set a, b, c, d]| = 4.
        But by some lemma #|A : {set T}| <= #|T| = 3, so 4 <= 3.
        Contradiction!
       *)
      
      move=> k2.
      have n3 : n=3%N by rewrite nk k2; lia.
      have adj1 u: #|adj u| = 2%N (* Every |adj u| is 2. *)
        by apply/eqP; rewrite -{}k2 -/(deg u)  (regular u).
      clear Co Col Cor CoUnique.
      have : 0%N < #|adj t| by rewrite adj1.
      move=> /card_gt0P [a a_adj]. (* there is an 'a' in adj t *)
      have a_sub : [set a] \subset adj t by rewrite sub1set.

      (* adj t = (adj t ⧵ [set a]) ⊎ [set a] as a disjoint union. *)
      have adjU := setD1K a_adj.
      have adjD : [disjoint [set a] & (adj t :\ a)]
        by rewrite  disjoints1; apply/negPf; rewrite setD11.

      (* By disjointness and 'card', |adj t ⧵ [set a]| = 1. *)
      set cta := #|adj t :\ a|.
      have cta12 : (1 + cta)%N = 2%N. {
        rewrite -[in LHS](cards1 a) /cta.
        have full_card := (eq_leqif (leq_card_setU [set a] (adj t :\ a) ) ).
        rewrite adjD in full_card.
        move: full_card => /idP  /eqP /esym ->.
        by rewrite adjU adj1.
      }
      have cta1 : cta == 1%N by apply/eqP; move: cta12; lia.

      (* Thus |adj t ⧵ [set a]| = [set b]. *)
      move: (cards1P cta1) => [b setb].
      
      (* a ∉ (adj t ⧵ [set a]), therefore a ∉ [set b], therfore a ≠ b. *)
      have aNb: a \notin [set b] by rewrite -disjoints1 -setb.
      rewrite in_set1 in aNb.

      (* Then adj t = [set b] ⊎ [set a] with a != b, so adj t = [set a, b]. *)
      have tab : adj t = [set a; b] by rewrite -adjU setb.

      (* We have F t a and F t b, since both are in adj t.*)
      have badj: b \in adj t by rewrite tab set22.
      have fta : F t a by rewrite inE in a_adj.
      have ftb : F t b by rewrite inE in badj.

      have Fneq u v: F u v -> u != v. {
        case: (@idP (u != v)) => //= /negP.
        by rewrite Bool.negb_involutive => /eqP ->; rewrite Firr.
      }
      (* It follows that a != t and b != t (we already had a != b). *)
      have a_t: a != t by rewrite eq_sym (Fneq _ _ fta).
      have b_t: b != t by rewrite eq_sym (Fneq _ _ ftb).

      (* There is x ∉ adj t with x ≠ t by the 'no_hub' property. *)
      move: (no_hub t) => [x ftx tx].

      (* We have x≠a, x≠b, because otherwise we would have (for a) both
         F t a and ~~F t a.*)
      have xa: x != a. {
        case: (@idP (x != a)) => //= /negP.
        rewrite Bool.negb_involutive => /eqP xa.
        rewrite xa in ftx .
        by move: ftx => /negP; rewrite fta.
      }
      have xb: x != b. {
        case: (@idP (x != b)) => //= /negP.
        rewrite Bool.negb_involutive => /eqP xb.
        rewrite xb in ftx .
        by move: ftx => /negP; rewrite ftb.
      }

      (* a, b, x, t are unique with 'uniq' *)
      have abxt: uniq [:: a ; b; x; t]. {
        rewrite uniq_pairwise pairwise_cons; apply/andP; split. {
          rewrite //= aNb a_t.
          rewrite eq_sym in xa.
          by rewrite xa.
        } {
          rewrite pairwise_cons; apply/andP; split. {
            rewrite //= b_t.
            rewrite eq_sym in xb.
            by rewrite xb.
          }
          rewrite pairwise_cons; apply/andP; split. {
            by rewrite //= eq_sym tx.
          } by [].
        }
      }


      (*  A lemma implies #|[set a, b, c, d]| = 4. *)
      have szabxt := (card_uniqP  abxt).
      have sz4: size [:: a; b; x; t] = 4%N by [].
      rewrite sz4 in szabxt.

      (* but #|[set a, b, c, d]|  is also <= #|T| = 3 
         But by lemma 'max_card' #|A : {set T}| <= #|T| = 3, so 4 <= 3.*)
      have le43: #|[:: a; b; x; t]|  <= 3 by rewrite -n3 /n cardsT max_card.

      (* Contradiction! *)
      by rewrite szabxt in le43.
    Qed.

    
    Lemma fls: False.
    Proof. exact (k_not_2 (k_is_2 kge1 nge1 Asqrt A'_tr nk)).
    Qed.

  End assume_contra.
  (* Just rewriting 'fls', which is ~(forall u : T, [exists v, ~~ F u v && (u != v)]).*)
  Lemma exists_hub: [exists x, forall v, (x != v) ==> F x v].
  Proof.
    have no_hub : ~~[forall u : T, exists v : T, ~~ F u v && (u != v)].  {
      apply/negP => /forallP.

      set frl_exs := forall u : T, [exists v : T, ~~ F u v && (u != v)].
      have not_fe :  ~frl_exs by exact fls.
      by [].
    }
    rewrite  negb_forall in no_hub.
    rewrite (@eq_existsb _ (fun x=> ~~ [exists v, ~~ F x v && (x != v)])
                       (fun x=>  [forall v, (x != v) ==> F x v ])
            ) in no_hub; last first. {
      move=> u.
      rewrite negb_exists .
      rewrite (@eq_forallb _ (fun v=> ~~ (~~ F u v && (u != v)))
                           (fun v=> (u != v) ==> F u v)); last first. {
        move=> v.
        by rewrite negb_and Bool.negb_involutive implybE Bool.orb_comm.
      }
      by [].
    }
    by [].
  Qed.

  Lemma exists_hub_sig: {u | forall v, (u != v) -> F u v}.
  Proof.
    move: exists_hub => /existsP /sigW [u /forallP prop].
    exists u => v unv.
    have propv := prop v.
    by rewrite unv implyTb in propv.
  Qed.
    
End friendship_sec.
