From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
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
  
