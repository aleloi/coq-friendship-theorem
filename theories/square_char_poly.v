From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly polydiv 
  mxpoly.

From mathcomp Require Import algC.

(*Load matrix_lemmas.*)
(*Load adj2_matrix.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.

From mathcomp Require Import tuple.
  

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
        (forall i : 'I_d, (tnth μs' i) ^2 = (tnth λs i))
    }.
  Proof.
    destruct μs as [μs μs_len].
    destruct λs as [λs λs_len].
    simpl.
    move:d λs λs_len μs_len.
    elim: μs => [d λs λs_eq μs_sz p_eq p_subst_eq|
                  μ μs  indH d λs λs_eq μs_eq p_eq p_subst_eq]. {
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
        move=> [m le0].
        exfalso.
        rewrite (ltn0 m) in le0. congruence.
      }
    }
    rewrite big_cons in p_subst_eq.

    have p_subst_λs : p \Po 'X^2 = \prod_(λ <- λs) ('X^2 - λ%:P).

    rewrite p_eq.
    rewrite (big_endo (fun q=> q \Po ('X^2))
               (fst (comp_poly_multiplicative _ ))
               (snd (comp_poly_multiplicative _ ))
            ).
    rewrite (eq_bigr (fun λ=>('X^2 - λ%:P))). { by [].} {
      simpl; move=> λ _.
      by rewrite comp_polyB comp_polyX comp_polyC.
    }
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
      About big_map_id.
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
      About seq.nth_map.
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
    set λ := seq.nth 1 λs (seq.find [eta eq_op (μ ^ 2)] λs).
    have μ_lamda : μ^2 = λ. {
      apply /eqP.
      apply (seq.nth_find 1 root_of_λs).
    }

    set λs_p := (seq.cat (cons λ (seq.take i_μ λs)) (seq.drop i_μ.+1 λs)).
    rewrite seq.cat_cons in λs_p.
    have λs_perm : seq.perm_eq λs λs_p. {
            
      rewrite /λs_p -seq.cat_cons.
      rewrite -[in X in (seq.perm_eq X _)] (seq.cat_take_drop i_μ.+1 λs).
      rewrite seq.perm_cat2r.

    have -> : (seq.take i_μ.+1 λs) =
                seq.rcons (seq.take i_μ λs) (seq.nth 1  λs i_μ). {
      apply: seq.take_nth.
      by rewrite /i_μ  -seq.has_find.
    }
    by rewrite seq.perm_rcons.
    }
    rewrite (perm_big _ λs_perm) big_cons //= in p_subst_λs.
    rewrite μ_lamda in p_subst_eq.
    set λs' := seq.cat (seq.take i_μ λs) (seq.drop i_μ.+1 λs).
    rewrite -/λs' in p_subst_λs.
    have p_red_eq: \prod_(j <- μs) ('X^2 - (j ^ 2)%:P) =
                     \prod_(j <- λs') ('X^2 - j%:P). {
      have ne0 : ('X^2 - λ%:P) != 0. {
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

      
      apply (mulfI ne0).
      by rewrite -p_subst_λs  p_subst_eq.
    }
    have μs_size_λs : seq.size μs == seq.size λs'. {
      admit.
    }
    Check (indH _ λs' (eq_refl _) μs_size_λs).
    
      
    Search bigop cons.
    rewrite big_cons in p_eq.
    apply indH.
    Search bigop seq.perm_eq.
    rewrite seq.cat_cons in λs_p.
    Search seq.cat cons.
    Search seq.perm_eq seq.rcons.
    
    Search seq.find seq.has.
  forall [T : Type] (x0 : T) [n : nat] [s : list T],
  n < seq.size s ->
  seq.take n.+1 s = seq.rcons (seq.take n s) (seq.nth x0 s n)
    Search seq.take seq.rcons.
    Search seq.perm_eq seq.rcons.
    Search seq.cat seq.take seq.drop.

    
  forall [T : eqType] (s1 s2 s3 : list T),
  seq.perm_eq (seq.cat s2 s1) (seq.cat s3 s1) = seq.perm_eq s2 s3
seq.perm_cat2l:
  forall [T : eqType] (s1 s2 s3 : list T),
  seq.perm_eq (seq.cat s1 s2) (seq.cat s1 s3) = seq.perm_eq s2 s3
    
    Search seq.perm_eq.

    elim root_of_λs => λ λs1 λs2 μλ.

    seq.split_find_spec [eta eq_op (μ ^ 2)] λs
                 (seq.take (seq.find [eta eq_op (μ ^ 2)] λs) λs)
                 (seq.drop (seq.find [eta eq_op (μ ^ 2)] λs).+1 λs)
    About seq.find.
    Search seq.has.
    seq.FindSplit:
  forall [T : Type] [p : pred T] [x : T] [s1 : list T] (s2 : list T),
  p x ->
  ~~ seq.has p s1 ->
  seq.split_find_spec p (seq.cat (seq.rcons s1 x) s2) s1 s2
seq.FindNth:
  forall [T : Type] [p : pred T] [x : T] [s1 : list T] (s2 : list T),
  p x ->
  ~~ seq.has p s1 ->
  seq.split_find_nth_spec p (seq.cat (seq.rcons s1 x) s2) s1 s2 x
seq.perm_has:
  forall [T : eqType] [s1 s2 : list T] (a : pred T),
  seq.perm_eq s1 s2 -> seq.has a s1 = seq.has a s2
seq.split_find:
  forall [T : Type] [p : pred T] [s : list T],
  let i := seq.find p s in
  seq.has p s -> seq.split_find_spec p s (seq.take i s) (seq.drop i.+1 s)
    have stuff : { (λ , λs') | seq.perm_eq (λ::λs') λs &
                            λ = μ^2}.
    
      Search comp_poly
    (* Polynomial with 'X substituted to 'X^2 *)
  Admitted.

End square_polys.
  


(*
Lemma algC_comm {F: numClosedFieldType} (a b: F): a+b = b+a.
  by rewrite addrC.
Qed.
Check (@algC_comm algCnumClosedField).
Variable hej1 hej2 : algC.
Check (algC_comm hej1 hej2).
(* Fails: Check (@algC_comm algC).*)
Local Open Scope C_core_scope.

Print algCnumClosedField.
Search algC.
Search _ (Phant algC).
Check (Phant Algebraics.Implementation.type).
Print Algebraics.Exports.
Check (NumClosedFieldType algC Algebraics.Implementation.conjMixin).
Canonical numClosedFieldType := NumClosedFieldType algC Algebraics.Implementation.conjMixin.

Set Printing All.
Search GRing.char.



Print Algebraics.Exports.
Print algC.
Eval simpl in
  mathcomp.field.algC.Algebraics.Implementation.numClosedFieldType.

Print Algebraics.Implementation.type.
Print mathcomp.field.algC.Algebraics.Exports.algC.
About Algebraics.Implementation.normedZmodType.
About Fundamental_Theorem_of_Algebraics.
Search "normedZmodType".
Print Algebraics.Implementation.normedZmodType.
Check (normedZmodType algC).
(* How to use algC? How do I get that it's a closed field ? How do I
   use square roots?

This says that there is a 'numClosedFieldType'.
Algebraics.Implementation.numClosedFieldType: numClosedFieldType

(also this: algCnumClosedField)

This says that 'numClosedFieldType' implies closedFieldType.
Num.ClosedField.numField_closedFieldType:
  numClosedFieldType -> closedFieldType
Num.ClosedField.closedFieldType: numClosedFieldType -> closedFieldType
Num.ClosedField.normedZmod_closedFieldType:
  numClosedFieldType -> closedFieldType
Num.ClosedField.porder_closedFieldType: numClosedFieldType -> closedFieldType
Num.ClosedField.numField_decFieldType: numClosedFieldType -> decFieldType

This says that 'algC' is normedZmodType:
Algebraics.Implementation.normedZmodType: normedZmodType algC
 *)

Search numClosedFieldType.
Algebraics.Implementation.numClosedFieldType: numClosedFieldType

Search closed_field_poly_normal.
Search closedFieldType.
Search algC.
Search "sqrtC".

About Num.Theory.sqrtC.
About closedFieldType.
About imaginary_exists.
About solve_monicpoly.
 *)
  
