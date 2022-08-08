From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly.

(*
Only works with pure ring expressions, and I couldn't find any in this proof.
Maybe it would work with "generalize <expr>; field"? TODO: try that.
From mathcomp.algebra_tactics Require Import ring .
 *)


From mathcomp Require Import algC.
Require Import Lia.
From Hammer Require Import Tactics .

Require Import Friendship.square_char_poly.
Require Import Friendship.matrix_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.

From mathcomp Require Import tuple seq.

Ltac ssrnat_lia := rewrite /leq /subn /subn_rec /addn /addn_rec
                     /muln /muln_rec; lia.
Section adj2_matrix_props.
  
  
  Definition R := algC.
  Context (n k: nat) (kge1: (k >=1) %N) (nge1: (n >= 1) %N).
  
  Definition matN := 'M[R]_(1%N + (n-1)%N).

  Definition P : matN := (@block_mx _ 1 (n-1)%N 1 (n-1)%N
                            (const_mx 1)  (const_mx 1)
                            (const_mx 1) ((-1)%:M)).

  
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
     invmx_scalar det_mx11  invrN1  scalar_mxC
            -mulmxA dotmul  mul_scalar_mx scalemx_const  !mxE mulN1r opprK
            -{2}(mulr1n 1) -mulrnDr.
    generalize nge1;
      case n => [_|n' _] //= ;
                rewrite subSS  /subn /subn_rec  PeanoNat.Nat.sub_0_r  unitfE .

    
    suff aou: (@GRing.natmul (ZmodType algC _ ) 1 (1 + n')) != 0.
    case: (odd n') => //=; rewrite ?expr1 ?expr0 ?unitrN1 ?unitr1;
                      apply: GRing.mulf_neq0; 
                      [ exact (lreg_neq0 (lregN (@lreg1 _)))
                      | exact (aou )|   |exact (aou) ].
    exact (oner_neq0 _).
    
    by rewrite -[(1+n')%N]/n'.+1  (iffLR (charf0P _) Cchar _).
  Qed.

  Definition diag_vec : 'rV[R]_(1 + (n-1)) :=
    (row_mx ((k+n-1)%:R%:M : 'rV_1)
       (@const_mx R _ _ (k-1)%:R : 'rV_(n-1))).

  Definition adj2_diag : matN := diag_mx diag_vec.


  Lemma adj_diag_block_form : adj2_diag = @block_mx _ 1 (n-1)%N 1 (n-1)%N
                                            (const_mx (k+n-1)%:R) 0
                                            0            (k-1)%:R%:M.
    rewrite /adj2_diag /diag_vec diag_mx_row diag_const_mx.

    suff oeua: (diag_mx (@scalar_mx _ 1 (k+n-1)%N%:R)) = 
                 (@const_mx R 1 1 (k+n-1)%N%:R)
      by rewrite oeua.
    
    by rewrite (mx11_scalar (const_mx _)) (mx11_scalar (diag_mx _)) !mxE
    //=.
  Qed.

  
  Definition adj2 : 'M[R]_(1 + (n-1))  := (const_mx 1) +
                                            (k-1)%:R%:M.
  
  Lemma adj2_block_form :
    adj2 = @block_mx _ 1 (n-1)%N 1 (n-1)%N
             (const_mx k%:R)     (const_mx 1)
             (const_mx 1)        ((const_mx 1) + (k - 1)%:R%:M).
  Proof.
    rewrite -(@submxK R 1 (n-1)%N 1 (n-1)%N adj2).
    
    have -> : (@ulsubmx _ 1 _ 1 _ adj2) = const_mx k%:R.
    {
      apply/matrixP=> i j; rewrite !mxE .

      have {i} {j} -> : lshift (n - 1) i == lshift (n - 1) j
        by rewrite !ord1; apply/eqP.
      
      rewrite -{1}(mulr1n 1) -mulrnDr.
      suff -> : (1 + (k - 1))%N = k by [].
      {
        by move: kge1; case k => [|k' _] //=; ssrnat_lia.
      }
    }
    
    have -> : (@ursubmx _ 1 _ 1 _ adj2) = const_mx 1. {
      apply/matrixP=> i j; rewrite !mxE !ord1.
      have -> : (lshift (n - 1) 0 == rshift 1 j) = false 
        by rewrite eq_lrshift.
      by rewrite mulr0n addr0.
    }

    have -> : (@dlsubmx _ 1 _ 1 _ adj2) = const_mx 1. {
      apply/matrixP=> i j; rewrite !mxE !ord1.
      have -> : (rshift 1 i == lshift (n-1) 0) = false 
        by rewrite eq_rlshift.
      by rewrite mulr0n addr0.
    }

    suff -> : (@drsubmx _ 1 _ 1 _ adj2) = const_mx 1 + (k - 1)%:R%:M by []. {
      by apply/matrixP=> i j; rewrite !mxE eq_rshift.
    }
  Qed.

  
  Lemma D_m_P_eq : P *m adj2 = adj2_diag *m P.

    rewrite /P adj2_block_form adj_diag_block_form
      !mulmx_block !mul0mx !addr0 !add0r !mul_scalar_mx
      (mx11_scalar (const_mx (k + n - 1)%:R)) (mx11_scalar (const_mx 1))
      [in RHS](mx11_scalar (const_mx 1))
      !mxE -scalar_mxM //= !mul_scalar_mx !scalemx_const !mulr1  scale_scalar_mx.

    (* Top left block : *)
    rewrite mul1r dotmul  (mx11_scalar (const_mx k%:R))
      (mx11_scalar (const_mx (n-1)%:R))
      !mxE (mx11_scalar (k%:R%:M + (n - 1)%:R%:M)) mxE  !(mxE _ _ 0 0) //=
      !mulr1n -natrD.
    have -> : (k + (n - 1))%N = (k + n -1)%N
      by move:  nge1 => /ltP; ssrnat_lia.
    
    (* Bot left block: *)
    rewrite scalar_mxC mul_scalar_mx scalemx_const mulr1.
    have ->:
      (@const_mx R (n-1) 1 k%:R + const_mx (-1)) = const_mx (k-1)%:R .
    apply/matrixP => i j; rewrite !mxE.
    move: kge1; case: k => [//| k' _].
    
    by rewrite /subn /subn_rec //= PeanoNat.Nat.sub_0_r  [_.+1]/((1+k')%N) -/addn
         natrD addrC addrA (addNr 1) add0r.
    (* bot left block done *)

    (* 1×1^T = ones; used in 2 places. *)
    have -> : (@const_mx R (n-1) (n-1) 1) =
                (const_mx 1 : 'cV__) *m (const_mx 1 : 'rV__).
    apply/matrixP => i j; rewrite !mxE  (eq_bigr (fun=>1))  ?big_const_ord
                            ?iter_addr ?addr0 //=.
    by move=> i' _; rewrite !mxE mulr1.
    (* end proof  of 1×1 = ones*)

    (* Top right piece *)
    rewrite mulmxDr  [in LHS]mulmxA dotmul
      (mx11_scalar (const_mx _)) (mxE _ _ 0 0)
      mul_scalar_mx  mul_mx_scalar !scalemx_const -!raddfD //=.

    have -> : 1 + ((n - 1)%:R * 1 + (k - 1)%:R * 1) = ((k + n - 1)%:R :R).
    rewrite !mulr1  -{1}[in 1](mulr1n 1) -!natrD.
    suff -> : (1 + (n - 1 + (k - 1)))%N = (k + n - 1)%N by [].
    by move: nge1 kge1 => /ltP nge1' /ltP kge1'; ssrnat_lia.

    (* Top right piece done *)

    (* Bot right piece *)
    by rewrite scaleN1r [in -(_ + _)] raddfD //=  addrA addrN add0r mulrN1
       -mulNrn -raddfN //= mulNrn.
  Qed.

  Lemma diagonalizable_m : adj2 ~_P adj2_diag.
    by apply/simmxW; [ rewrite row_free_unit; exact P_unit
                     |  exact D_m_P_eq].
  Qed.


  Lemma char_poly_adj2: char_poly adj2 =
                          ('X - ((k + n - 1)%:R)%:P) * ('X - ((k - 1)%:R)%:P) ^+ (n - 1).
  Proof.
    rewrite (simmx_charpoly P_unit diagonalizable_m).
    have adj2_trig : is_trig_mx adj2_diag
      by apply: (is_diag_mx_is_trig (diag_mx_is_diag _)).
    rewrite (char_poly_trig adj2_trig).

    rewrite (@big_split_ord _ _ _ 1%N (n-1) _ _) //= adj_diag_block_form
      (eq_bigr (fun=> ('X-((k + n - 1)%:R :R) %:P))); last first.
    {
      move=>i _; rewrite block_mxEul.
      suff -> : (@const_mx R 1 1 (k + n - 1)%:R i i) = (k + n - 1)%:R by [].
      by rewrite mxE.
    }

    rewrite [in X in _*X](eq_bigr (fun=> ('X-((k - 1)%:R) %:P))); last first.
    {
      move=>i _; rewrite block_mxEdr.
      suff -> : ((k - 1)%:R%:M i i) = ((k - 1)%:R :R) by [].
      rewrite mxE //=.
      have -> : (i==i) by apply/eqP .
      by rewrite mulr1n.
    }

    by rewrite !big_const_ord !iter_mulr !mulr1 expr1.
    
  Qed.

  Definition lams : (1+(n-1)).-tuple algC := cons_tuple (k + n - 1)%:R
                                               (nseq_tuple (n-1) (k - 1)%:R). 
  Lemma lams_prod: char_poly adj2 = \prod_(l <- lams) ('X - l%:P).
    rewrite char_poly_adj2  /lams big_cons.
    apply: f_equal.
    rewrite big_tnth.
    rewrite (eq_bigr (fun => ('X-((k - 1)%:R) %:P))); last first. {
      move=> i _.
      by rewrite tvalK  tcastE tnth_nseq.
    }
    by rewrite big_const_ord iter_mulr mulr1  size_tuple.
  Qed.

  Definition is_square_root A := A *m A = adj2.
  (*From mathcomp Require Import seq.*)

  

  Lemma adj_mtx_char_poly adj :
    is_square_root adj ->
    (*char_poly mtx = \prod_(μ <- μs) ('X - μ %:P) ->*)
    { μs' : (1+(n-1)).-tuple R |
      char_poly adj = \prod_(μ <- μs') ('X - μ %:P) &
        all2 (fun μ λ => μ^2 == λ) μs' (cons_tuple (k + n - 1)%:R
                                         (nseq_tuple (n-1) (k - 1)%:R))
    }.
  Proof.
    move=> adj2_eq.
    set p := char_poly adj.
    have [μs' prop] := closed_field_poly_normal p.
    rewrite (monicP (char_poly_monic adj)) scale1r in prop.
    have deg_p := size_char_poly adj.
    have size_μs' : (seq.size μs') == (1 + (n-1))%N by
      subst p; rewrite prop size_prod_XsubC  in deg_p; apply /eqP; congruence.
    clear deg_p.
    simpl in *.
    set tμs' := (@Tuple _ _ μs' size_μs').
    have tp : p = \prod_(z <- tμs') ('X - z%:P)
      by rewrite prop; apply: eq_bigr.

    have p_X2 : p \Po 'X^2 = \prod_(μ <- tμs') ('X^2 - μ%:P)
      by rewrite tp (big_endo (fun q=> q\Po 'X^2)
                       (fst (comp_poly_multiplicative 'X^2) )
                       (snd (comp_poly_multiplicative 'X^2) )
           );
      apply/eq_bigr => μ _;
                       rewrite comp_polyD comp_polyX -polyCN comp_polyC.

    set p_μ2 := (\prod_(μ <- tμs') ('X^2 - (μ%:P)^2) : {poly algC}).
    have p_μ2_eq : p_μ2 = (\prod_(μ <- tμs') ('X - (μ%:P))) *
                            (\prod_(μ <- tμs') ('X + (μ%:P))) . {
      subst p_μ2;
        rewrite (eq_bigr (fun μ => ('X - μ%:P) * ('X + μ%:P))) //=. {
        by rewrite big_split //=.
      }
      by move=> μ _; rewrite subr_sqr.
    }

    rewrite -tp in p_μ2_eq.
    have μs_subst :
      \prod_(μ <- tμs') ('X + μ%:P) = ((-1)^+(1+(n-1)))%:P * (p \Po (-'X)). {
      clear  p_X2 p_μ2 p_μ2_eq adj2_eq  k kge1.
      rewrite (eq_bigr (fun μ => (-1)*(-'X - μ%:P))); last first.
      by move=>  μ _; rewrite mulrDr !mulN1r !opprK.
      rewrite big_split //=.
      
      have  -> : (\prod_(i <- μs') -1) =
                   ((-1)^+(1+(n-1))). {
        move=> RR.
        clear prop tμs' tp p  adj .
        have <- : seq.size μs' = (1 + (n - 1))%N by apply: eqP; exact size_μs'.
        clear size_μs'.
        elim: μs' => [|μs''].
        by rewrite -signr_odd  expr0 big_nil.
        move=> l indL.
        rewrite big_cons indL.
        rewrite -exprS.
        suff -> : (seq.size l).+1 = seq.size (μs'' :: l) by [].
        sauto.
      }
      have -> : (-1) ^+ (1 + (n - 1)) = ((-1) ^+ (1 + (n - 1)))%:P. {
        clear prop tμs' tp  p adj .
        move=> RR.
        generalize ((1 + (n - 1)%N)%N) => nn.
        rewrite -signr_odd -[in RHS]signr_odd.
        case: (odd nn) => //=; rewrite ?expr0 ?expr1.
        by rewrite rmorphN1.
      }
      
      rewrite prop.
      rewrite (big_endo (fun q=> q \Po (-'X))
                 (fst (comp_poly_multiplicative (-'X) ))
                 (snd (comp_poly_multiplicative (-'X) ))
              ).
      rewrite [in RHS](eq_bigr (fun μ => -'X - μ%:P)) //=; last first. {
        move => μ _.
        by rewrite comp_polyB comp_polyX comp_polyC.
      } 
    }
    
    rewrite {}μs_subst in p_μ2_eq.
    have pNx_det : p \Po - 'X = \det ( -('X%:M) - map_mx polyC adj ). {
      clear k kge1 nge1 adj2_eq μs' prop size_μs' tμs' tp p_X2 p_μ2 p_μ2_eq.
      rewrite /p /char_poly /char_poly_mx -det_map_mx //=.
      suff -> : map_mx (comp_poly (- 'X)) ('X%:M - map_mx polyC adj) =
                  - 'X%:M - map_mx polyC adj by []. {
        rewrite map_mxD //= map_scalar_mx  //= comp_polyX rmorphN //=.
        suff -> : map_mx (comp_poly (- 'X)) (- map_mx polyC adj) = - map_mx polyC adj
          by []. {
          rewrite rmorphN //=  -map_mx_comp //=.
          suff -> : map_mx (comp_poly (- 'X) \o polyC) adj = map_mx polyC adj by []. {
            suff : comp_poly (- 'X) \o polyC =1 polyC 
              by move=> comp_comp;
                        apply/matrixP => i j;
                                         rewrite !mxE (comp_comp _).
            by move=> R {p adj } c //=;
                        rewrite comp_polyC.
          }
        }
      }
    }
    rewrite {}pNx_det in p_μ2_eq.
    have p_μ2_det : p_μ2 = \det (('X^2)%:M  - map_mx polyC adj2). {
      subst p; rewrite {}p_μ2_eq.
      clear  μs' prop size_μs' tμs' tp p_X2 p_μ2.
      have -> : ((-1) ^+ (1 + (n - 1)))%:P = ((-1) ^+ (1 + (n - 1))). {
        generalize ((1 + (n - 1))%N).
        move=> nn R. 
        rewrite -signr_odd -[in RHS]signr_odd.
        case: (odd nn) => //=; rewrite ?expr0 ?expr1.
        by rewrite rmorphN1.
      }
      by rewrite -detZ scaleN1r opprB opprK  /char_poly /char_poly_mx
         -det_mulmx  mulmxDl !mulmxDr  -rmorphN //= -scalar_mxM;
         apply: f_equal;
         rewrite [in X in X + _]addrC  expr2
           [in X in _ + _ + X]addrC addrA  map_mxN //=  comm_mx_scalar
         -[in X in X + (- _ *m _)]addrA -mulmxDr addrN mulmx0 addr0;
         apply: f_equal;
         rewrite -adj2_eq  map_mx_is_multiplicative //=  mulNmx.
    }
    clear p_μ2_eq p_X2.
    set q := char_poly adj2.
    have p_μ2_q : p_μ2 = q \Po 'X^2. {
      rewrite p_μ2_det /q /char_poly /char_poly_mx  -det_map_mx //=.
      apply: f_equal.

      rewrite [in RHS]map_mxD //= [in RHS]map_scalar_mx  //= comp_polyX.
      rewrite rmorphN //=.
      repeat apply: f_equal.

      suff -> : map_mx (comp_poly ('X^2)) ( map_mx polyC adj2) = map_mx polyC adj2
        by []. {
        rewrite  -map_mx_comp //=.
        by apply/matrixP => i j; rewrite !mxE //= comp_polyC.
      }
    }

    have aoeu : q \Po 'X^2 = \prod_(μ <- tμs') ('X^2 - (μ ^ 2)%:P). {
      rewrite -p_μ2_q /p_μ2.
      suff : forall μ, (μ ^ 2)%:P = (μ%:P ^ 2 : {poly algC}). {
        move=> hyp.
        apply eq_bigr => μ _.
        by rewrite (hyp μ).
      } {
        move=> μ.
        by rewrite !exprSzr !expr0z !mul1r  polyC_multiplicative.
      }
    }

    have [μs prop2 prop3] := (polys_and_squares_technical_lemma lams_prod aoeu). 
    exists μs. {
      by rewrite tp prop2.
    } {
      exact prop3.
    }
  Qed.

End adj2_matrix_props.
