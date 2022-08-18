From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly.

From mathcomp.algebra_tactics Require Import ring.
From mathcomp.zify Require Import zify. 

From mathcomp Require Import algC.
From Hammer Require Import Tactics .
From Hammer Require Import Hammer .

Require Import Friendship.square_char_poly.
Require Import Friendship.matrix_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.

From mathcomp Require Import tuple seq.
#[local] Hint Rewrite expr1 expr0 mulN1r mulrN1 invrN1 @opprK unitfE mulr1n
  mulr0n addr0 add0r mulr1 mul1r scaleN1r addrN iter_mulr opprB expr2
  scaler0: sring.

#[local] Hint Rewrite det_mx11 invmx_scalar dotmul mul_scalar_mx mul_mx_scalar
  scalemx_const mul0mx map_scalar_mx mulmx0: smatrix_r.

Ltac simpl_mr := autorewrite with smatrix_r sring.

Section adj2_matrix_props.
  
  
  Definition R := algC.
  Context (n k: nat) (kge1: (k >=1) %N) (nge1: (n >= 1) %N).
  
  Definition matN := 'M[R]_(1%N + (n-1)%N).

  Definition P : matN := block_mx (const_mx 1)  (const_mx 1)
                            (const_mx 1) ((-1)%:M).

  (* Proof by computation; Use the block determinant formula to show
   that the determinant is ±n, and then use the field characteristic
   assumption to show that it's not zero. *)
  Lemma P_unit : P \in unitmx.

    (* -I is invertible *)
    have neg1M_unit m: ((-1)%:M : 'M[R]_m)  \in unitmx. {
      suff : (-1)%:M *m (-1)%:M = (1%:M : 'M[R]_m) by apply mulmx1_unit.
      by rewrite -scalar_mxM; apply: f_equal; ring.
    }

    (* -I and  (1 - 1 *m -I *m 1) are invertible *) 
    rewrite unitmxE  det_block //= unitrM; apply/andP; split. {
      by rewrite -unitmxE.
    } {
      rewrite  (pinvmxE (neg1M_unit _)) det_mx11; simpl_mr;
      rewrite scalar_mxC -mulmxA; simpl_mr; rewrite !mxE;
        simpl_mr.
      
      have -> : 1 + (n - 1)%:R = ((1 + (n-1))%:R ) by
        hauto use: mulr1n, mulrnDr.
      rewrite unitfE  (iffLR (charf0P _) Cchar _).
      lia.
    }
  Qed.

  (* Sqaure of friendship graph adjacency matrix *)
  Definition adj2 : 'M[R]_(1 + (n-1))  := (const_mx 1) + (k-1)%:R%:M.
  
  Lemma adj2_block_form :
    adj2 = block_mx 
             (const_mx k%:R)     (const_mx 1)
             (const_mx 1)        ((const_mx 1) + (k - 1)%:R%:M).
  Proof.
    rewrite -(submxK adj2).
    
    have -> : (ulsubmx  adj2) = const_mx k%:R.
    {
      apply/matrixP=> i j; rewrite !mxE .

      have {i} {j} -> : lshift (n - 1) i == lshift (n - 1) j
        by rewrite !ord1; apply/eqP.
      simpl_mr.
      have -> : 1 + (k - 1)%:R = (1 + (k-1))%:R
        by hauto use: mulr1n, mulrnDr.
      apply: f_equal; lia.
    }
    
    have -> : ursubmx adj2 = const_mx 1 by
      apply/matrixP=> i j; rewrite !mxE !ord1 eq_lrshift; simpl_mr.
    
    have -> : dlsubmx adj2 = const_mx 1
      by apply/matrixP=> i j; rewrite !mxE !ord1 eq_rlshift; simpl_mr.

    by have -> : (drsubmx adj2) = const_mx 1 + (k - 1)%:R%:M
      by apply/matrixP=> i j; rewrite !mxE eq_rshift.
  Qed.

  
  (* Will be the spectrum of adj2 as a vector *)
  Definition diag_vec : 'rV[R]_(1 + (n-1)) :=
    (row_mx (k+n-1)%:R%:M (const_mx (k-1)%:R )).

  (* Will show that adj2 diagonalizes to adj2_diag *)
  Definition adj2_diag : matN := diag_mx diag_vec.

  Lemma adj_diag_block_form : adj2_diag = block_mx
                                            (const_mx (k+n-1)%:R) 0
                                            0            (k-1)%:R%:M.
    rewrite /adj2_diag /diag_vec diag_mx_row diag_const_mx.
    by have -> m : (diag_mx  m%:M) = (const_mx m : 'M[R]_1)
      by rewrite (mx11_scalar (const_mx _)) (mx11_scalar (diag_mx _))
           !mxE //=.
  Qed.

  (* Almost proves that adj2 diagonalizes to adj2_diag though basis
  change matrix P. *)
  Lemma D_m_P_eq : P *m adj2 = adj2_diag *m P.

    rewrite /P adj2_block_form adj_diag_block_form
      !mulmx_block (mx11_scalar (const_mx (k + n - 1)%:R))
      (mx11_scalar (const_mx 1))
      [in RHS](mx11_scalar (const_mx 1))
       -scalar_mxM dotmul
              (mx11_scalar (const_mx k%:R))
              (mx11_scalar (const_mx (n-1)%:R)) !mxE.
    
    simpl_mr; rewrite !scale_scalar_mx !mul_mx_scalar; simpl_mr;
    rewrite (mx11_scalar (k%:R%:M + (n - 1)%:R%:M)) !mxE //=; simpl_mr;
      rewrite -natrD -!raddfD //=.
    
    (* 1×1^T = ones; used in 2 places. *)
    have outer : (const_mx 1 : 'M[R]_(n-1)) =
                (const_mx 1 : 'cV__) *m (const_mx 1 : 'rV__). {
      apply/matrixP => i j; rewrite !mxE  (eq_bigr (fun=>1))  ?big_const_ord
                              ?iter_addr; simpl_mr. { by []. }
      by move=> i' _; rewrite !mxE; simpl_mr.
    }
    (* end proof  of 1×1 = ones*)
    
    have block_eq:  forall A B C D A' B' C' D', A = A' -> B = B' -> C = C' -> D = D' ->
                                                block_mx A B C D = block_mx A' B' C' D'
        by sauto. 
    apply: block_eq. { (* Top left block 1×1*)
      apply: f_equal;  apply: f_equal; lia.
    } { (* top right block: 1×(n-1) *)
      rewrite mulmxDr outer mulmxA dotmul  (mx11_scalar (const_mx _)) !mxE;
      simpl_mr; rewrite mul_mx_scalar; simpl_mr; rewrite -!raddfD //=.
      apply: f_equal.
      rewrite -{1}[in 1](mulr1n 1)  -!natrD; apply: f_equal; lia.
    } { (* bot left block (n-1)×1 *)
      apply: f_equal.
      rewrite natrB; last first. { by []. } 
      by [].
    } { (* bot left block (n-1 × n-1) *)
      by rewrite -outer raddfN raddfD //= addrA; simpl_mr.
    }
  Qed.

  Lemma diagonalizable_m : adj2 ~_P adj2_diag.
    by apply/simmxW; [ rewrite row_free_unit; exact P_unit
                     |  exact D_m_P_eq].
  Qed.

  (* Characteristic polynomial of adj2 as a factored polynomial *)
  Lemma char_poly_adj2: char_poly adj2 =
                          ('X - ((k + n - 1)%:R)%:P) * ('X - ((k - 1)%:R)%:P) ^+ (n - 1).
  Proof.
    (* Write as product; split in 1 + (n-1) terms. *)
    rewrite (simmx_charpoly P_unit diagonalizable_m)
      (char_poly_trig (is_diag_mx_is_trig (diag_mx_is_diag _)))
      [(n-1).+1]/((1 + (n-1))%N) -/addn  big_split_ord //=
      -/adj2_diag adj_diag_block_form
      [in X in X*_](eq_bigr (fun=> ('X-((k + n - 1)%:R) %:P))); last first.
    by move=>i _; rewrite block_mxEul mxE.

    (* rewrite product with (n-1) terms as ∏ X-(k-1) *)
    rewrite [in X in _*X](eq_bigr (fun=> ('X-((k - 1)%:R) %:P))); last first.
    by move=>i _; rewrite block_mxEdr mxE eq_refl.

    by rewrite !big_const_ord !iter_mulr;  simpl_mr.  
  Qed.

  (* Spectrum of adj2 *)
  Definition lams : seq algC := cons (k + n - 1)%:R
                                  (nseq (n-1) (k - 1)%:R). 

  (* Char poly of adj2 as a product over it's spectrum *)
  Lemma lams_prod: char_poly adj2 = \prod_(l <- lams) ('X - l%:P).
    by rewrite char_poly_adj2  /lams big_cons big_nseq iter_mulr; simpl_mr.
  Qed.

  Definition is_square_root A := A *m A = adj2.
  
  (* Spectrum of √adj2: shows that it can be linearly factored into
  X-square roots of the spectrum of adj2. *)
  Lemma adj_mtx_char_poly adj :
    is_square_root adj ->
    { μs : seq R |
      char_poly adj = \prod_(μ <- μs) ('X - μ %:P) &
        all2 (fun μ λ => μ^2 == λ) μs (cons (k + n - 1)%:R
                                         (nseq (n-1) (k - 1)%:R))
    }.
  Proof.
    (* Proof strategy:
       - Let p = char poly of adj (not adj2!)
       - by algebraic closedness, p = C× ∏_{μ ∈ μs} (X - μ)
       - by char_poly_monic, C=1
       - by size_char_poly, the 'deg p = n'
       - p(X^2) = ∏_{μ ∈ μs} X^2 - μ by substitution
       - Let q' = ∏_{μ ∈ μs} X^2 - μ^2 (this will be the char poly of 
                                           adj2 evaluated at X^2)
       - q' factors as q'= (∏_{μ ∈ μs} X - μ)⋅(∏_{μ ∈ μs} X + μ)
       - the second part of q' is (∏_{μ ∈ μs} X^2 + μ) = (-1)^n⋅p(-X)

       - p(-X) = \det ( -X⋅I- adj) by substitution
       - q'(X) = \det (X^2⋅I - adj2).
       - q'(X) = q(X^2) 

       The remainder of the proof is exactly 'polys_and_squares_technical_lemma'.
       (boring induction)
    *)
    move=> adj2_eq.
    set n' := (1 + (n-1))%N.

    (* - Let p = char poly of adj (not adj2!) *)
    set p := char_poly adj.

    (* - by algebraic closedness, p = C× ∏_{μ ∈ μs} (X - μ) *)
    have [μs p_prod] := closed_field_poly_normal p.

    (* - by size_char_poly, the 'deg p = n' *)
    rewrite (monicP (char_poly_monic adj)) scale1r in p_prod.
    have deg_p := size_char_poly adj.
    have size_μs : (seq.size μs) = n'.
      subst p; rewrite p_prod size_prod_XsubC -/n' in deg_p; congruence.
    clear deg_p.
    simpl in *.

    
    (*set tμs := (@Tuple _ _ μs size_μs).*)
    (*have tp : p = \prod_(z <- tμs) ('X - z%:P)
      by rewrite prop; apply: eq_bigr.*) 
    have p_X2 : p \Po 'X^2 = \prod_(μ <- μs) ('X^2 - μ%:P)
      by rewrite p_prod (big_endo (fun q=> q\Po 'X^2)
                       (fst (comp_poly_multiplicative 'X^2) )
                       (snd (comp_poly_multiplicative 'X^2) )
           );
      apply/eq_bigr => μ _;
                       rewrite comp_polyD comp_polyX -polyCN comp_polyC.

    (* - Let q' = ∏_{μ ∈ μs} X^2 - μ^2 (this will be the char poly of 
                                           adj2 evaluated at X^2) *)
    set q' := (\prod_(μ <- μs) ('X^2 - (μ%:P)^2) : {poly algC}).

    (* - q' factors as q'= (∏_{μ ∈ μs} X - μ)⋅(∏_{μ ∈ μs} X + μ) *)
    have q'_eq : q' = (\prod_(μ <- μs) ('X - (μ%:P))) *
                            (\prod_(μ <- μs) ('X + (μ%:P))) . {
      subst q';
        rewrite (eq_bigr (fun μ => ('X - μ%:P) * ('X + μ%:P))) //=. {
        by rewrite big_split //=.
      }
      by move=> μ _; rewrite subr_sqr.
    }

    (*- the second part of q' is (∏_{μ ∈ μs} X^2 + μ) = (-1)^n⋅p(-X) *)
    have μs_subst : \prod_(μ <- μs) ('X + μ%:P) =
                       ((-1)^+n')%:P * (p \Po (-'X)). {
      clear  p_X2 q' q'_eq adj2_eq  k kge1.
      rewrite (eq_bigr (fun μ => (-1)*(-'X - μ%:P))); last first.
      by move=>  μ _; rewrite mulrDr !mulN1r !opprK.
      rewrite big_split //=.
      have -> : (\prod_(i <- μs) -1) = ((-1)^+n')
        by move=> RR; rewrite big_tnth big_const_ord size_μs;  simpl_mr.
      have -> nn : (-1) ^+ nn = ((-1) ^+ nn)%:P by rewrite rmorphX rmorphN1.
      apply: f_equal.
      rewrite p_prod (big_endo (fun q=> q \Po (-'X))
                 (fst (comp_poly_multiplicative (-'X) ))
                 (snd (comp_poly_multiplicative (-'X) ))
              ) [in RHS](eq_bigr (fun μ => -'X - μ%:P)) //=.
      by move => μ _; rewrite comp_polyB comp_polyX comp_polyC.
    }
    rewrite {}μs_subst in q'_eq.

    (* p(-X) = \det ( -X⋅I- adj) by substitution *)
    have pNx_det : p \Po - 'X = \det ( -('X%:M) - map_mx polyC adj ). {
      clear -p.
      rewrite /p /char_poly /char_poly_mx -det_map_mx //=.
      suff -> : map_mx (comp_poly (- 'X)) ('X%:M - map_mx polyC adj) =
                  - 'X%:M - map_mx polyC adj by []. {
        rewrite map_mxD //= map_scalar_mx  //= comp_polyX rmorphN //=.
        apply f_equal. 
        rewrite rmorphN //=  -map_mx_comp //=.
        
        suff : comp_poly (- 'X) \o polyC =1 (polyC : R -> _)
          by move=> comp_comp; apply/matrixP => i j;
                                                rewrite !mxE (comp_comp _).
        by move=>  c //= ; rewrite comp_polyC.
      }
    }
    rewrite {}pNx_det in q'_eq.

    (* - q'(X) = \det (X^2⋅I - adj2). *)
    have q'_det : q' = \det (('X^2)%:M  - map_mx polyC adj2). {
      subst p; rewrite {}q'_eq -p_prod /char_poly.
      clear -adj2_eq.
      have <- nn : (-1) ^+ nn = ((-1) ^+ nn)%:P by rewrite rmorphX rmorphN1.
      by rewrite -detZ /char_poly /char_poly_mx -det_mulmx;
      simpl_mr;
      rewrite  mulmxDl !mulmxDr -rmorphN //= -scalar_mxM;
      apply: f_equal;
      rewrite [in X in X + _]addrC 
        [in X in _ + _ + X]addrC addrA  map_mxN //=  comm_mx_scalar
      -[in X in X + (- _ *m _)]addrA -mulmxDr; simpl_mr;
      apply: f_equal;
      rewrite -adj2_eq  map_mx_is_multiplicative //=  mulNmx.
    }
    
    (* - q'(X) = q(X^2), with q(X) = char poly of adj^2 *)
    clear q'_eq p_X2.
    set q := char_poly adj2.
    have q'_q : q' = q \Po 'X^2. {
      clear -q'_det.
      rewrite q'_det /q /char_poly /char_poly_mx  -det_map_mx //=.
      apply: f_equal.
      rewrite [in RHS]map_mxD //= [in RHS]map_scalar_mx  //= comp_polyX.
      rewrite rmorphN //=.
      repeat apply: f_equal.
      by apply/matrixP => i j; rewrite -map_mx_comp !mxE //= comp_polyC.
    }

    have q_μs : q \Po 'X^2 = \prod_(μ <- μs) ('X^2 - (μ ^ 2)%:P). {
      rewrite -q'_q /q'.
      apply eq_bigr => μ _.
      repeat apply: f_equal.
      by rewrite !exprSzr; simpl_mr; rewrite polyC_multiplicative.  
    }

    clear -q_μs kge1 nge1 p_prod.
    have [μs' prop2 prop3] := (polys_and_squares_technical_lemma lams_prod q_μs). 
    exists μs'. {
      by rewrite p_prod prop2.
    } {
      exact prop3.
    }
  Qed.

End adj2_matrix_props.
