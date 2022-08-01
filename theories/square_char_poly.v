From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv 
  mxpoly.

From mathcomp Require Import algC.
From Hammer Require Import Tactics .
Require Import Lia.
(*Load matrix_lemmas.*)
(*Load adj2_matrix.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.

From mathcomp Require Import tuple seq.

Definition list_insert {T} (l: seq T) a {n i: nat} (l_len : size l = n)
  (i_ln: i <= n) := seq.cat (seq.take i l) (a :: (seq.drop i l)).

Lemma split_tuples (R: eqType) (μs λs: list R) (n: nat)
  (sz_μ : seq.size μs = n) (sz_λ : seq.size λs = n)
  (i_μ : nat) (i_μ_ln : i_μ <= n) (P: R -> R -> bool) (μ λ: R):
  all2 P μs λs -> P μ λ ->
  all2 P (list_insert μ sz_μ i_μ_ln)
    (list_insert λ sz_λ i_μ_ln).
  move=> all_μλ P_μλ.
  rewrite all2E.
  apply /andP; split. {
    rewrite /list_insert !size_cat !size_takel; last first;
      try by rewrite ?sz_μ ?sz_λ i_μ_ln.
    apply /eqP; apply f_equal.
    by rewrite //= !size_drop sz_μ sz_λ.
  }

  suff peq_μλ : perm_eq (zip (μ :: μs) (λ :: λs))
                  (zip (list_insert μ sz_μ i_μ_ln)
                     (list_insert λ sz_λ i_μ_ln)). {
    rewrite -(perm_all _ peq_μλ) //=.
    apply /andP; split. { exact P_μλ. }
    rewrite all2E in all_μλ.
    move: all_μλ; move=> /andP. sauto.
  }
  rewrite zip_cat; last first. {
    by rewrite !size_takel //=; sauto.
  }
  
  rewrite //= perm_sym perm_catC cat_cons perm_cons perm_catC.
  rewrite -zip_cat. rewrite !cat_take_drop.
  by rewrite perm_refl.
  rewrite !size_takel //=; by rewrite ?sz_μ ?sz_λ i_μ_ln.
Qed.
  
  (* TO BE moved; just typing it out to se how it would look like
   Questions: how do I write polynomial root products? As
   \prod_(r <- seq) ('X - r)
   or with matrices and ordinals?
   *)
  (*From mathcomp Require Import tuple.*)

Section square_polys.
  Definition RR:= algC.
  Lemma polys_and_squares_technical_lemma
    d (λs μs: d.-tuple RR) (p : poly_ringType algCring):
    p = \prod_(λ <- λs) ('X - λ%:P) ->
    (p \Po ( 'X^2 )) = \prod_(μ <- μs) ('X^2 - (μ^2) %:P) ->
    { μs' : d.-tuple RR |
      ((\prod_(μ <- μs ) ('X - μ%:P)) = (\prod_(μ' <- μs' ) ('X - μ'%:P))) &
        all2 (fun μ λ => μ^2 == λ) μs' λs 
    }.
  Proof.
    destruct μs as [μs μs_len].
    destruct λs as [λs λs_len].
    simpl.
    move:d λs λs_len μs_len p.
    elim: μs => [d λs λs_eq μs_sz p p_eq p_subst_eq |
                  μ μs  indH d λs λs_eq μs_eq p p_eq p_subst_eq ]. {
      have d0 : d = 0%N. {
        transitivity (@seq.size algC nil).
        symmetry.
        by apply /eqP.
        by [].
      }
      clear μs_sz.
      move: λs_eq.
      rewrite d0.
      move=> λs_eq.
      exists (nil_tuple _). {
        by rewrite !big_nil.
      } {
        sauto.
      }
    }
    move: μ μs  indH λs λs_eq μs_eq p p_eq p_subst_eq.
    case: d => [|d']. {
      move=> μ μs _   λs λs_eq μs_eq.
      exfalso.
      sauto.
    }
    move=> μ μs  indH λs λs_eq μs_eq p p_eq p_subst_eq.
    rewrite big_cons in p_subst_eq.

    have p_subst_λs : p \Po 'X^2 = \prod_(λ <- λs) ('X^2 - λ%:P). {
    
      rewrite p_eq.
      rewrite (big_endo (fun q=> q \Po ('X^2))
                 (fst (comp_poly_multiplicative _ ))
                 (snd (comp_poly_multiplicative _ ))
              ).
      rewrite (eq_bigr (fun λ=>('X^2 - λ%:P))). { by []. } {
        simpl; move=> λ _.
        by rewrite comp_polyB comp_polyX comp_polyC.
      }
    }
    have p_subst2 :  p \Po 'X^2 = \prod_(λ <- λs) ('X^2 - λ%:P) by [].
    have μ_fct: ('X - μ %:P) %| p \Po 'X^2. {
      rewrite p_subst_eq.
      apply: Pdiv.Idomain.dvdp_mulr.
      suff -> : 'X^2 - (μ ^ 2)%:P = ('X - μ%:P)*('X + μ %:P)
        by apply Pdiv.Idomain.dvdp_mulIl.
      have -> : (μ ^ 2)%:P = (μ%:P ^ 2 : {poly algC}). {
        by rewrite !exprSzr !expr0z !mul1r  polyC_multiplicative.
      }
      by rewrite subr_sqr.
    }

    set i_μ := (seq.find [eta eq_op (μ ^ 2)] λs).
    have root_of_λs : seq.has  (fun λ=> μ^2 == λ) λs. {
      have /negPn μ_root_px2 : root (p \Po 'X^2) μ
        by rewrite root_factor_theorem.
      rewrite p_subst_λs in μ_root_px2.
      (*About big_map_id.*)
      set h := fun (λ: RR)=>'X^2 - λ%:P.
      have prods_eq: \prod_(λ <- λs) ('X^2 - λ%:P) =
                   \prod_(pλ <- seq.map h λs) pλ
        by rewrite big_map_id .
      rewrite prods_eq root_bigmul seq.all_predC Bool.negb_involutive
        in μ_root_px2.
      
      move: μ_root_px2 .
      move=> /seq.has_nthP μ_root_px2'.
      have μ_root_px2 := (μ_root_px2' 1).
      case: μ_root_px2 => [i i_le_d is_root].
      set λi := seq.nth 1 λs i.

      apply /(seq.has_nthP 1).
      exists i.
      rewrite seq.size_map in i_le_d; exact i_le_d.
      (*About seq.nth_map.*)
      rewrite (seq.nth_map 1) in is_root; last first. {
        rewrite seq.size_map in i_le_d; exact i_le_d.
      }
      rewrite /h in is_root.
      move:  is_root.
      move=> /rootP is_root.
      rewrite hornerD  in is_root.
      rewrite hornerN hornerC hornerXn  in is_root.
      apply subr0_eq in is_root.
      apply /eqP.
      by rewrite -exprnP.
    }
    
    (* Now: Divide the 'λs' into one which has μ^2 = λ,
       and the rest.
     *)
    set λ := seq.nth 0 λs (seq.find [eta eq_op (μ ^ 2)] λs).
    have μ_lamda : μ^2 = λ. {
      apply /eqP.
      apply (seq.nth_find 0 root_of_λs).
    }

    set λs_p := (seq.cat (cons λ (seq.take i_μ λs)) (seq.drop i_μ.+1 λs)).
    rewrite seq.cat_cons in λs_p.
    have λs_perm : seq.perm_eq λs λs_p. {
            
      rewrite /λs_p -seq.cat_cons.
      rewrite -[in X in (seq.perm_eq X _)] (seq.cat_take_drop i_μ.+1 λs).
      rewrite seq.perm_cat2r.

    have -> : (seq.take i_μ.+1 λs) =
                seq.rcons (seq.take i_μ λs) (seq.nth 0  λs i_μ). {
      apply: seq.take_nth.
      by rewrite /i_μ  -seq.has_find.
    }
    by rewrite seq.perm_rcons.
    }
    rewrite (perm_big _ λs_perm) big_cons //= in p_subst_λs.
    rewrite μ_lamda in p_subst_eq.
    set λs' := seq.cat (seq.take i_μ λs) (seq.drop i_μ.+1 λs).
    rewrite -/λs' in p_subst_λs.
    have x2_ne0 : ('X^2 - λ%:P) != 0. {
      suff : lead_coef ('X^2 - λ%:P) = 1. {
        move=> aoeu.
        apply rreg_lead0.
        rewrite aoeu.
        apply rreg1.
      }
      rewrite lead_coefDl.
      apply lead_coefXn.
      rewrite size_polyXn size_opp.
      rewrite size_polyC.
      case : (λ != 0) => [|] //=.
    }
    have p_red_eq: \prod_(j <- μs) ('X^2 - (j ^ 2)%:P) =
                     \prod_(j <- λs') ('X^2 - j%:P). {
      apply (mulfI x2_ne0).
      by rewrite -p_subst_λs  p_subst_eq.
    }
    have μs_size_λs : seq.size μs == seq.size λs'. {
      apply /eqP.
      suff : (seq.size (μ :: μs)) = (seq.size λs').+1 by sauto.
      move: μs_eq.
      move=>  /eqP ->.
      suff -> : d'.+1 = seq.size λs_p by
        rewrite /λs_p //=.
      rewrite -(seq.perm_size  λs_perm).
      symmetry.
      by apply /eqP.
    }
    

    set p' := \prod_(λ <- λs') ('X - λ%:P).
    have p'_eq : p' \Po 'X^2 = \prod_(μ <- μs) ('X^2 - (μ ^ 2)%:P). {
      apply (mulfI x2_ne0).
      (*Set Printing Implicit.*)
      rewrite -p_subst_eq.
      
      have -> : ('X^2 - λ%:P) = ('X-λ%:P) \Po 'X^2. {
        by rewrite comp_polyB comp_polyX comp_polyC.
      } 
      rewrite -comp_polyM /p'.
      
      have -> : ('X - λ%:P) * \prod_(λ0 <- λs') ('X - λ0%:P) =
                  \prod_(λ0 <- (cons λ  λs')) ('X - λ0%:P) by
        rewrite big_cons.
      
      by rewrite -/λs_p -(perm_big _ λs_perm) //=  -p_eq.
    }
      
    
    elim: (indH _ λs' (eq_refl _) μs_size_λs _ (Logic.eq_refl p')
             p'_eq
          ) => [μs'' p_prod roots_spec ].

    (* λs' = seq.cat (seq.take i_μ λs) (seq.drop i_μ.+1 λs)
       μs'' matchar med λs'.

       Det blir rätt att stoppa in μ efter i_μ element i μs''
     *)
    
    set μ_μs'' := seq.cat (seq.take i_μ μs'')
                     (cons μ (seq.drop i_μ μs'')).
    have sz_μs : seq.size μs'' = d'.
    transitivity (seq.size λs').
    by rewrite size_tuple.
    suff  : d'.+1 = seq.size λs_p by sauto. {
      rewrite -(seq.perm_size  λs_perm).
      symmetry.
      by apply /eqP.
    }

    have μ_μs''_perm : seq.perm_eq μ_μs'' (μ ::  μs''). {
      clear.
      subst μ_μs''.
      case: μs'' => [μs sz] //=.
      rewrite -[in X in (seq.perm_eq _ X)] (seq.cat_take_drop i_μ μs).
      rewrite -seq.cat_rcons -seq.cat_cons  seq.perm_cat2r.
      by rewrite seq.perm_rcons.
    }

           
    have sz_μ_μs'' : seq.size μ_μs'' = (d'.+1). {
      rewrite (seq.perm_size μ_μs''_perm). sauto.
    }
    have aoeu : seq.size μ_μs'' == d'.+1 by apply /eqP.
    exists (Tuple aoeu). {
      by rewrite  //=  (perm_big _ μ_μs''_perm) //= !big_cons  p_prod.
    } {
      (*have d_eq : d'.+1 = (1 + d')%N by [].*)
      clear indH p p_eq p_subst2 μ_fct  λs_p λs_perm
        p_subst_eq p_subst_λs x2_ne0 p_red_eq p' p'_eq μ_μs''_perm
        p_prod .
      rewrite all2E; apply /andP.
      
      split. {
        simpl.
        rewrite sz_μ_μs''.
        sauto.
      } {
        simpl.
        rewrite /μ_μs''.
        have iμ_lt : i_μ <= d' 
          by rewrite /i_μ -ltnS -(eqP λs_eq) -seq.has_find.
          
        have -> : (take i_μ μs'' ++ μ :: drop i_μ μs'') =
                    list_insert μ sz_μs iμ_lt by [].
        have -> : λs = seq.cat (seq.take i_μ λs)
                         (λ :: (seq.drop i_μ.+1 λs)). {
          rewrite -[in LHS](cat_take_drop i_μ λs).
          apply: f_equal.
          rewrite /λ -/i_μ.
          rewrite (drop_nth 0). {by []. }
          by rewrite -has_find.
        }
        
        
        have szλs' : size λs' = d'. {
          rewrite -(eqP μs_size_λs).
          clear -μs_eq.
          simpl in μs_eq.
          set aeuuea := (eqP μs_eq).
          by inversion aeuuea.
        }
        have -> : (take i_μ λs ++ λ :: drop i_μ.+1 λs) =
                    list_insert λ szλs' iμ_lt. {
          rewrite /list_insert /λs'.
          rewrite [in RHS]take_size_cat; last first. {
            rewrite size_takel //=.
            rewrite has_find in root_of_λs.
            clear -root_of_λs.
            sauto.
          }
          apply: f_equal; apply: f_equal.
          rewrite [in RHS]drop_size_cat //=.
          rewrite size_takel //=.
          rewrite has_find in root_of_λs.
          clear -root_of_λs.
          sauto.
        }

        have all2_res   := (split_tuples sz_μs szλs' iμ_lt
                             roots_spec (introT eqP μ_lamda)).
        rewrite all2E in all2_res.
        apply (elimT andP) in all2_res.
        exact (snd all2_res).
      }
    }
  Qed.
End square_polys.
