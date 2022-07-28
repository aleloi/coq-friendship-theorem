From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly.

(*Require Import Lia.

From Hammer Require Import Hammer. (* for `hammer` *)
From Hammer Require Import Tactics .
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sim_char_poly.
  Variable (F : fieldType).
  Import GRing.Theory.
  Import Monoid.Theory.
  Local Open Scope ring_scope.

  Lemma charpoly_uconj n (V : 'M[F]_(n.+1)) (f : 'M_n.+1) :
  V \in unitmx -> char_poly (conjmx V f) = char_poly f.
  Proof.
    move=> Vu; apply/eqP.
    unfold char_poly, char_poly_mx; rewrite conjumx //  !map_mxM.

    set lift := map_mx (polyC_rmorphism F).
    have -> : lift (invmx V) = (invmx (lift V))
      by subst lift; rewrite map_invmx.
    (* Testa senare; jag väntade aldrig klart 
    (*Set Hammer PredictMethod "nbayes".*)
    predict 1000. (* map_invmx är inte bland de 100 första.  *)
    Set Hammer ATPLimit 500.
    hammer.
     *)
     
    set theX := (@scalar_mx _ (S n) (polyX _)).
    have x_eq: theX = (lift V) *m theX *m (invmx (lift V)).
    {
      subst lift;
        (* TODO: kolla upp hur man gör när en rewrite-regel
     har premisser. Här har 'map_invmx' premisser som
fixas ganska enkelt.
         *)
        rewrite  scalar_mxC  -mulmxA mulmxV ?mulmx1 //.
      by rewrite map_unitmx; exact Vu.
    }
    rewrite {1}x_eq.
    rewrite -mulmxBl -mulmxBr  !det_mulmx  GRing.mulrC GRing.mulrA
                         det_inv mulVr ?mul1r.
    by []. by rewrite -unitmxE map_unitmx ?Vu. 
  Qed.
  
  Lemma simmx_charpoly {n} {P A B : 'M[F]_n.+1} : P \in unitmx ->
  A ~_P B -> char_poly A = char_poly B.
Proof.
  by move=> Pu /eqP<-; rewrite charpoly_uconj. Qed.

End sim_char_poly.

From mathcomp Require Import tuple.

Section det_dotmul.
  Variable R: fieldType.
  Import GRing.Theory.
  Local Open Scope ring_scope.
  (* Block matrix determinant formula *)
  Lemma det_block [n1 n2: nat] (A: 'M[R]_n1) (B: 'M_(n1, n2))
    (C: 'M_(n2, n1)) (D: 'M[R]_(n2, n2)) (Dinv: D \in unitmx):
    \det (block_mx A B C D) =
      \det D * \det (A - B *m (pinvmx D) *m C).
  Proof.
    set block2 := (block_mx 1%:M 0 (-(pinvmx D)*m C) 1%:M).
    
    have block_2_det1 : (\det block2 = 1) by rewrite det_lblock !det1 mul1r.
    have block_2_inv : block2 \in unitmx by rewrite unitmxE block_2_det1 unitr1.

    rewrite -(mulmxK block_2_inv (block_mx A B C D)).
    
    have ->:
      (block_mx A B C D) *m block2
         = block_mx (A - B *m (pinvmx D) *m C) B 0 D
      by rewrite mulmx_block !mulmx1 !mulmx0 !add0r [B *m (_ *m _)]mulmxA
           !mulNmx !mulmxN  [D *m _]mulmxA  (pinvmxE Dinv)
         -[D *m invmx D *m C]mulmxA (mulKVmx Dinv _) addrN mulNmx.
    by rewrite det_mulmx  det_inv block_2_det1 invr1 mulr1 det_ublock mulrC.
  Qed.

  Lemma dotmul nn: (const_mx 1 : 'rV[R]_nn) *m (const_mx 1 : 'cV_nn)
                   = const_mx nn%:R.

    rewrite (mx11_scalar (const_mx _)) (mx11_scalar (_ *m _)) !mxE
      (eq_bigr (fun=>1)); [| by move=> i _ /[!mxE] /[!mulr1]].
    
    rewrite big_const_ord.
    suff aou : (@iter R nn (+%R 1) 0) = nn%:R by rewrite aou.
    elim: nn => [|nn //= -> ] //= ;
                  by rewrite  -[nn.+1]/((1+nn)%N) natrD.
  Qed.

End det_dotmul.
