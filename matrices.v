From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import div fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv mxpoly.

About unitmx.
Print unitmx.
Print poly.root.
Print uniq.
Locate ":=:".

Locate "{in P  & , }".
About is_diag_mx.
Search _ char_poly.
Print stablemx (* Nåt full-rank-liknande koncept *).

Locate "%:M".

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
(*have simp := (row_free_unit, stablemx_unit, unitmx_inv, unitmx1).*)
    move=> Vu; apply/eqP.
    Check map_mxM.
    unfold char_poly, char_poly_mx; rewrite conjumx //  !map_mxM.

    set lift := map_mx (polyC_rmorphism F).
    have lift_invmx : lift (invmx V) = (invmx (lift V))
      by subst lift; rewrite map_invmx.

    set theX := (@scalar_mx _ (S n) (polyX _)).
    have: theX = (lift V) *m theX *m (lift (invmx V)).
    {
      subst lift;
        (* TODO: kolla upp hur man gör när en rewrite-regel
     har premisser. Här har 'map_invmx' premisser som
fixas ganska enkelt.
         *)
        rewrite lift_invmx scalar_mxC  -mulmxA  mulmxV ?mulmx1 //.
      by rewrite map_unitmx; exact Vu.
    }
    move=> x_eq; rewrite {1}x_eq.
    rewrite -mulmxBl -mulmxBr  !det_mulmx  GRing.mulrC GRing.mulrA
                        lift_invmx det_inv mulVr ?mul1r.
    by []. by rewrite -unitmxE map_unitmx ?Vu. 
  Qed.

  
  Lemma simmx_charpoly {n} {P A B : 'M[F]_n.+1} : P \in unitmx ->
  A ~_P B -> char_poly A = char_poly B.
Proof.
  by move=> Pu /eqP<-; rewrite charpoly_uconj. Qed.

End sim_char_poly.


Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Search _ scalar_mx.
Print insub.
Print is_scalar_mx.


Section stuff.
  Context [R : GRing.Field.type].
  (*Variable R : ringType. (* (*= int :> ringType.  := int. (* Testar med Z först *) *) *) *)
  (* Definition R :=  (*rat_fieldType. *) *)

  Definition R_sort := GRing.Zmodule.sort.
  
  (* Check [ringType of int]. *)
  (* Check [fieldType of rat]. *)
  (* Print rat_fieldType. *)
  Definition n: nat := 2.
  Variable k: nat.
  (*Variable n k : nat. *)
  Variable kge1 : k >= 1.

  Check addnA.
  Check addnI.
  Check esym.
  Locate "\matrix_".

  Locate "%:~R".

  Print GRing.Ring.type.
  About zmodType.
  About GRing.one.
  
  About intmul.
  Search _ zmodType "ring".
  Print GRing.Ring.

  (* Ringar är också Z-moduler, men returtypen för 'intmul', inte
     ring.  På nåt sätt ska man få Coq att acceptera att intmul
     bevarar ringen.
   *)

  (* Definition lift (n: nat) : (R_sort R) := *)
  (*   (intmul n (GRing.one R)). *)
  Print GRing.Zmodule.

  From mathcomp Require Import ssrint rat.
  
  Definition m : 'M_n  := \matrix_ ( i , j < n ) (
                              (intmul (GRing.one R)
                                 (if i == j
                                  then k
                                  else 1%nat))) .
    
  Lemma m_coeff : forall (i j : 'I_n), 
      (m i j) = (if i == j
                 then k
                 else 1%nat) %:R.
    by move=> i j; rewrite /m mxE //.
  Qed.

  Print GRing.Field.

  

  From Hammer Require Import Hammer. (* for `hammer` *)
  From Hammer Require Import Tactics .
  Require Import Lia.
  Check scalar_mx.
  Print R.
  Definition m' : 'M_n  := addmx (const_mx 1)
                             (@scalar_mx R n (k-1)%:R).

  Print scalar_mx.
  Locate "*+".
  Print GRing.natmul.
  Lemma m_is_ones_plus_I : m = m'.
    rewrite /m /m' /addmx;
    case: addmx_key;
    case: matrix_key;
    apply/matrixP => i j; rewrite !mxE; case: (i == j) => //=;
      move: kge1; case: k => [//| k' _] .

    
    rewrite mulr1n.
    clear i j kge1.
    
    rewrite -[Posz (S k')]/(1+(Posz k')) intrD.
    have an_eq: subn k'.+1 1 = k' by
      rewrite -[subn]/Nat.sub; lia.
    by rewrite  an_eq.

    by rewrite mulr0n addr0.
  Qed.

  Search (_ -> 'M_(_ _)) "block".
  Search row_free.

  Search (_ -> 'rV__).

  
  (* Vektor (1, 0, ... -1 , 0.. ),
     '-1' är på position (j+1)
   *)
  Definition ones_perp_vec (j: 'I_(n-1)) : 'rV[R]_n.
    Print ordinal.
    (* Ordinal : forall m : nat, m < n -> 'I_n. *)
    About lshift.

    have jj := lshift 1 j.
    rewrite -[(n-1+1)%nat]/n in jj.

    exact (
    \matrix_ ( i < 1, α < n ) (
        if α == 0
        then 1
        else if α == jj
             then -1
             else 0)).
  Defined.        
Print ones_perp_vec.    

Lemma ones_perp_coeff (j: 'I_(n-1)) : forall (α : 'I_n), 
      (ones_perp_vec j 0 α) = (if α == 0
                 then 1
                 else if α == lshift 1 j
                      then -1
                      else 0
                ).
  by move=> α; rewrite mxE.
Qed.

About big_mkord.
(* square brackets: nåt med implicita argument *)
Lemma sum_nat_mkord_trueprop [n: nat] (c: nat) :
    (\sum_(i < n) c)%N = (n * c)%N. 
Proof.
  by rewrite -[(\sum_(i < _) _)%N]/
             (\sum_(i < _ | ((fun _: nat => _) i))
                ((fun _: nat=> c) i))%N -big_mkord sum_nat_const_nat;
  unfold subn;
  unfold subn_rec;
  rewrite -(Minus.minus_n_O n).
Qed.  

Definition all_perp : 'M[R]_(n-1, n).
  by have result :=  \mxblock_(i < (n-1), j < 1) (ones_perp_vec i);
                     move: result; 
                     rewrite !sum_nat_mkord_trueprop.
Defined.

(*Search mulmx block_mx.
Print invmx.
Search unitmx.
Search determinant invmx.
Search determinant block_mx.
About pinvmx.
About invmx.
Print matrix_lmodType.
Search pinvmx.
About map_invmx.
About det_inv.
About unitmx_inv.

About mem_pred.
Print unitmx.*)
(*Set Printing All.*)
Print pinvmx.
(* Block matrix determinant formula *)
Lemma det_block [n1 n2: nat] (A: 'M[R]_n1) (B: 'M_(n1, n2))
  (C: 'M_(n2, n1)) (D: 'M[R]_(n2, n2)):
  (D \in unitmx) -> \det (block_mx A B C D) =
                      \det D * \det (A - B *m (pinvmx D) *m C).
Proof.
  move=> Dinv.
  set block2 := (block_mx 1%:M 0 (-(pinvmx D)*m C) 1%:M).
  have block_eq:
    (block_mx A B C D) *m block2
    = block_mx (A - B *m (pinvmx D) *m C) B 0 D
    by rewrite mulmx_block !mulmx1 !mulmx0 !add0r [B *m (_ *m _)]mulmxA
    !mulNmx !mulmxN  [D *m _]mulmxA  (pinvmxE Dinv)
          -[D *m invmx D *m C]mulmxA (mulKVmx Dinv _) addrN mulNmx.
  have block_2_det1 : (\det block2 = 1)
    by rewrite det_lblock !det1 mul1r.
  have block_2_inv : block2 \in unitmx
      by rewrite unitmxE block_2_det1 unitr1.
  have mulmx_inv : forall nn (E F : 'M[R]_nn),
      F \in unitmx -> E *m F *m (invmx F) = E
        by move=> nn E F F_unit; rewrite (mulmxK F_unit).
  by rewrite -(mulmx_inv _ (block_mx A B C D) block2 block_2_inv) block_eq
             det_mulmx  det_inv block_2_det1 invr1 mulr1 det_ublock mulrC.
Qed.

Search 1%:M.

About const_mx.
About block_mx.

Definition P : 'M[R]_(1%N + (n-1)%N) := (@block_mx R 1 (n-1)%N (n-1)%N (n-1)%N
                                           (const_mx 1)  (const_mx 1)
                                           (const_mx 1) ((-1)%:M)).
Lemma P_unit : P \in unitmx.
  Search unitmx determinant.
  rewrite unitmxE.
  have neg1M_det : forall m,
    (\det ((-1)%:M : 'M[R]_m)) = (-1) ^+ (odd m) by
  move=> m; rewrite det_scalar -[in LHS]signr_odd.

  have neg1M_unit : forall m, ((-1)%:M : 'M[R]_m) \in unitmx
      by move => m; rewrite unitmxE neg1M_det; case: (odd m);
    rewrite ?expr1 ?expr0 ?unitrN1 ?unitr1.
  
  rewrite det_block // neg1M_det (pinvmxE (neg1M_unit _)) invmx_scalar
    det_mx11 invrN1  scalar_mxC.

  (* Suck. *)
  have mul_c: (const_mx 1 : 'rV_n) *m (const_mx 1 : 'cV_n)
              = (n-1)%:M.

  About const_mx.
  Search "dotmul".
  Search _ ('cV__) mulmx.
  Search ((_ : 'rV__) *m (_ : 'cV__)).

  Print mulmx.
  
  Search 'cV_1.
  Search _ "mx11".
  About scalar_mx.
  Search (@scalar_mx _ 1).
  
  Search (_ *m _%:M).
  
  Set Printing All.
  Search ((-1) ^ _).
  Search odd.
  Print signr_odd.
  rewrite -[(-1)^-1]/signr_odd.
  Search (invmx (_%:M)).
  Search pinvmx invmx.

  -mulN1r det_mulmx det1 mulr1.
  (* Vi har en n x n - matris, vilket framgår av det-argumentet.
     det händer nån skum implicit konvertering tror jag.
     Kollar i MatrixZmodule och MatrixRing. Vad  GRing.opp ligger i zmodule?
   *)
  
          (@GRing.opp
             (GRing.Ring.zmodType
                (matrix_ringType (GRing.Field.ringType R) 1))
             (GRing.one (matrix_ringType (GRing.Field.ringType R) 1)))
    
  Search determinant scalar_mx.
  
  rewrite det_scalar.

