From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import div fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv mxpoly.

From Hammer Require Import Hammer. (* for `hammer` *)
From Hammer Require Import Tactics .

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


Section m_matrix_properties.
  From mathcomp Require Import ssrint.
  Require Import Lia.
  (* Doesn't really work well for me. It times out or crashes the Coq
     process due to OOM.

     From Hammer Require Import Hammer. (* for `hammer` *)
     From Hammer Require Import Tactics .  
   *)
  
  Context [R : GRing.Field.type]
    (n k: nat) (kge1: k >=1) (nge1: n >= 1)
    (* Check the comments in ssralg.v for an explanation, or
       just print. Use together with 'charf0P'
     *)
    (field_has_char_zero : [char R] =i pred0).

  
  (* First attempt at defining the P matrix. Defined in block form below.
     In block form it seems easier to prove that it's invertable and that
     it diagonalizes m.
   *)
  (* Vektor (1, 0, ... -1 , 0.. ),
     '-1' är på position (j+1)
   *)
  (*
  Definition ones_perp_vec (j: 'I_(n-1)) : 'rV[R]_n.

    have jj := lshift 1 j.
    rewrite -[(n-1+1)%nat]/n in jj.

    exact (
    \matrix_ ( i < 1, α < n ) (
        if α == 0
        then 1
        else if α == jj
             then -1
             else 0)).
  Defined.        *)
(*Print ones_perp_vec.    *)

(*Lemma ones_perp_coeff (j: 'I_(n-1)) : forall (α : 'I_n), 
      (ones_perp_vec j 0 α) = (if α == 0
                 then 1
                 else if α == lshift 1 j
                      then -1
                      else 0
                ).
  by move=> α; rewrite mxE.
Qed.
*)

(* square brackets: nåt med implicita argument *)
(*Lemma sum_nat_mkord_trueprop [nn: nat] (c: nat) :
    (\sum_(i < nn) c)%N = (nn * c)%N. 
Proof.
  by rewrite big_const_ord iter_addn_0 mulnC.
Qed.
*)

(*Definition all_perp : 'M[R]_(n-1, n).
  by have result :=  \mxblock_(i < (n-1), j < 1) (ones_perp_vec i);
                     move: result; 
                     rewrite !sum_nat_mkord_trueprop.
Defined.
*)

(* Block matrix determinant formula *)
Lemma det_block [n1 n2: nat] (A: 'M[R]_n1) (B: 'M_(n1, n2))
  (C: 'M_(n2, n1)) (D: 'M[R]_(n2, n2)) (Dinv: D \in unitmx):
  \det (block_mx A B C D) =
                      \det D * \det (A - B *m (pinvmx D) *m C).
Proof.
  clear n k nge1 kge1 field_has_char_zero.
  set block2 := (block_mx 1%:M 0 (-(pinvmx D)*m C) 1%:M).
  
  have block_eq:
    (block_mx A B C D) *m block2
    = block_mx (A - B *m (pinvmx D) *m C) B 0 D
    by rewrite mulmx_block !mulmx1 !mulmx0 !add0r [B *m (_ *m _)]mulmxA
    !mulNmx !mulmxN  [D *m _]mulmxA  (pinvmxE Dinv)
          -[D *m invmx D *m C]mulmxA (mulKVmx Dinv _) addrN mulNmx.
  have block_2_det1 : (\det block2 = 1) by rewrite det_lblock !det1 mul1r.
  have block_2_inv : block2 \in unitmx by rewrite unitmxE block_2_det1 unitr1.
  by rewrite -(mulmxK block_2_inv (block_mx A B C D)) block_eq
                det_mulmx  det_inv block_2_det1 invr1 mulr1 det_ublock mulrC.
Qed.


Definition P : 'M[R]_(1%N + (n-1)%N) := (@block_mx _ 1 (n-1)%N 1 (n-1)%N
                                           (const_mx 1)  (const_mx 1)
                                           (const_mx 1) ((-1)%:M)).

Lemma dotmul nn: (const_mx 1 : 'rV[R]_nn) *m (const_mx 1 : 'cV_nn)
                 = const_mx nn%:R.

  rewrite (mx11_scalar (const_mx _)) (mx11_scalar (_ *m _)) !mxE
    (eq_bigr (fun=>1)); [| by move=> i _ /[!mxE] /[!mulr1]].
  
  rewrite big_const_ord.
  suff aou : (@iter R nn (+%R 1) 0) = nn%:R by rewrite aou.
  elim: nn => [|nn //= -> ] //= ;
                by rewrite  -[nn.+1]/((1+nn)%N) natrD.
Qed.

(* Proof by computation; Use the block determinant formula to show
   that the determinant is ±n, and then use the field characteristic
   assumption to show that it's not zero. *)
Lemma P_unit : P \in unitmx.
  
  have neg1M_det m : 
    (\det ((-1)%:M : 'M[R]_m)) = (-1) ^+ (odd m) by
    rewrite det_scalar -[in LHS]signr_odd.
  
  have neg1M_unit m : ((-1)%:M : 'M[R]_m) \in unitmx
      by rewrite unitmxE neg1M_det; case: (odd m); 
    rewrite ?expr1 ?expr0 ?unitrN1 ?unitr1.

  
  rewrite unitmxE  det_block // neg1M_det (pinvmxE (neg1M_unit _))
    invmx_scalar det_mx11 invrN1  scalar_mxC
          -mulmxA dotmul  mul_scalar_mx scalemx_const !mxE  mulN1r opprK
          -{2}(mulr1n 1) -mulrnDr.
    generalize nge1;
      case n => [_|n' _] //= ;
                rewrite subSS  /subn /subn_rec  PeanoNat.Nat.sub_0_r  unitfE .

  suff aou: (@GRing.natmul R 1 (1 + n')) != 0.
  case: (odd n') => //=; rewrite ?expr1 ?expr0 ?unitrN1 ?unitr1;
                    apply: GRing.mulf_neq0;
                    [ exact (lreg_neq0 (lregN (@lreg1 _)))
                    | exact aou|   |exact aou ].
  
  exact (oner_neq0 _).
  
  by rewrite -[(1+n')%N]/n'.+1  (iffLR (charf0P _)
                                   field_has_char_zero _).
Qed.

(* Nästa steg: m diagonaliseras med P *)

(* Sen: karakteristiskt polynom (men det är enkelt) *)

(* Sen: kvadratrot till matris som diagonaliseras i samma bas,
   och har kvadratrötter som egenvärden (svårt) *)

About diag_mx.
Search "block" matrix.
Search "mx11".
About row_mx.
Locate "%:M".
Print scalar_mx.

(*
Jag vill kunna definiera D som diagonalmatrisen
*)
Lemma dim_is_n: (1+(n-1))%N = n.
  by move:
    n nge1  => [|n'] _ //=; rewrite /subn /subn_rec //=
                         PeanoNat.Nat.sub_0_r.
Qed.

(* Originally
https://stackoverflow.com/questions/52514957/coq-use-equality-of-types-for-type-checking-a-term-in-a-definition,
I simplified for my needs to remove the 'f'
*)
Definition cast {T1 T2 : nat} (H : T1 = T2)
  (f : nat -> Type) (x : f T1) :=
  eq_rect T1 (fun T3 : nat => f T3) x T2 H.

About cast.
(* No idea why I need the full-arg version @cast. {T1, T2} should be
implicit (and Coq happily infers the holes), but I can't leave them
out. 

TODO: Check 'castmx' in matrix.v. I think it comes with lemmas for 
substitution.
 *)
Definition diag_vec : 'rV[R]_n :=
  @cast _ _ dim_is_n (fun t=> 'rV[R]_t)
       (row_mx ((k+n-(S O))%:R%:M : 'rV_1)
          (@const_mx R _ _ (k-1)%:R : 'rV_(n-1))).

Definition diag_vec' : 'rV[R]_(1 + (n-1)) :=
  (row_mx ((k+n-(S O))%:R%:M : 'rV_1)
     (@const_mx R _ _ (k-1)%:R : 'rV_(n-1))).

Definition D : 'M[R]_n := diag_mx diag_vec.
Definition D' : 'M_(1+(n-1)) := diag_mx diag_vec'.


Lemma D_block_form : D' = @block_mx _ 1 (n-1)%N 1 (n-1)%N
                           (const_mx (k+n-1)%:R) 0
                           0            (k-1)%:R%:M.
  rewrite /D' /diag_vec' diag_mx_row diag_const_mx.

  suff oeua: (diag_mx (@scalar_mx _ 1 (k+n-1)%N%:R)) = 
               (@const_mx R 1 1 (k+n-1)%N%:R)
    by rewrite oeua.
  
  by rewrite (mx11_scalar (const_mx _)) (mx11_scalar (diag_mx _)) !mxE
  //=.
Qed.

(* The adjacency matrix in the Friendship Theorem
     in an arbitrary field with characteristic 0.
   *)
  (*Definition m : 'M_n  := \matrix_ ( i , j < n ) (
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
  *)

  Definition m' : 'M_(1 + (n-1))  := addmx (const_mx 1)
                                      (@scalar_mx R _ (k-1)%:R).
  (*Lemma m_is_ones_plus_I : m = m'.
    (* Seems 3x longer than this should take *)
    rewrite /m /m' /addmx.
    apply/matrixP => i j; rewrite !mxE;
                     case: (i == j) => //=; clear i j.
    move: kge1; case: k => [//| k' _].
    {
      have an_eq: subn k'.+1 1 = k' by rewrite -[subn]/Nat.sub; lia.
      by rewrite mulr1n  -[Posz (S k')]/(1+(Posz k')) intrD an_eq.
    }
    by rewrite mulr0n addr0.
  Qed.
   *)

  Print m'.
  Lemma m'_block_form :
    m' = @block_mx _ 1 (n-1)%N 1 (n-1)%N
           (const_mx k%:R)     (const_mx 1)
           (const_mx 1)        (addmx (const_mx 1) (k - 1)%:R%:M).
    apply/matrixP => i j.
    rewrite !mxE.
    case (split i) => [ (* forall o : 'I_1, *)
        [[|m'] e]
      |] //=.
    (* TODO: Check the rowmx / colmx, submx lemmas in matrix.v
       AND/OR read chapter 7 of the math-comp book. *)
    About unsplitK.
    About lsubmx.
    Search 'I_1.
    Print all_equal_to.
    (*ord1*)
     
  Admitted.
    
Lemma D_m_P_eq : (P *m m') = (D' *m P).

  rewrite /P m'_block_form D_block_form
    !mulmx_block !mul0mx !addr0 !add0r !mul_scalar_mx
    (mx11_scalar (const_mx (k + n - 1)%:R)) (mx11_scalar (const_mx 1))
    [in RHS](mx11_scalar (const_mx 1))
    !mxE -scalar_mxM //= !mul_scalar_mx !scalemx_const !mulr1  scale_scalar_mx.

  (* Top left block : *)
  rewrite mul1r dotmul  (mx11_scalar (const_mx k%:R))
    (mx11_scalar (const_mx (n-1)%:R))
    !mxE (mx11_scalar (k%:R%:M + (n - 1)%:R%:M)) mxE  !(mxE _ _ 0 0) //=
    !mulr1n -natrD.
  have kn_expr : (k + (n - 1))%N = (k + n -1)%N.
  rewrite /subn /subn_rec /addn /addn_rec;
    move: nge1. case: n => [|n'] _ //=; lia.
  rewrite kn_expr.
  clear kn_expr field_has_char_zero.
  

  (* Bot left block: *)
  rewrite scalar_mxC mul_scalar_mx scalemx_const mulr1.
  have bot_left_eq:
    (@const_mx R (n-1) 1 k%:R + const_mx (-1)) = const_mx (k-1)%:R .
  apply/matrixP => i j; rewrite !mxE.
  
  move: kge1; case: k => [//| k' _].
  by rewrite /subn /subn_rec //= PeanoNat.Nat.sub_0_r  [_.+1]/((1+k')%N) -/addn
    natrD addrC addrA (addNr 1) add0r.
  rewrite bot_left_eq.
  (* bot left block done *)

  (* TODO: CONTINUE FROM HERE

     Left (in this proof):
        - ones : 'M_n = col_ones *m row_ones
        - use that to rewrite the top right and bot right expression
     Left (in other parts):
        - block form for 'm' (possibly look into 'cast' and submx
        - ring characteristic; rewrite the 
   *)

(*
Lemma D_diag_form : D = diag_mx (
      row_mx ((k+n-(S O))%:R%:M : 'rV_1)
        (@const_mx R _ _ (k-1)%:R : 'rV_(n-1))).
Print D. 
Lemma diagonalizable_m : A ~_P B
*)
