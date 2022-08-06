From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Friendship.adj2_matrix.
(* I got help from Paolo Giarrusso with the crucial step in
https://coq.zulipchat.com/#narrow/stream/237664-math-comp-users/topic/.E2.9C.94.20Dependent.20types.3A.20total.20functions.20from.20.23.7C.5Bset.20w.20.7C.20P.20w.5D.7C.3D1
*)
Section StatementReduction.
  Context (T: finType) (T_nonempty: [set: T] != set0) (F: rel T)
    (Fsym: symmetric F) (Firr: irreflexive F)
    (co_set: (forall (u v: T), u != v -> #|[set w | F u w & F v w]| == 1)).

  Definition T_elem:  T := (xchoose (set0Pn _ T_nonempty)).

  Definition idP' :=
    fun b1 : bool =>
      if b1 as b return (reflect b b)
      then ReflectT true is_true_true
      else ReflectF false not_false_is_true.

  Definition f_total (f_nodiag : (forall (u v: T) (e: u != v),  T)):
    (forall (x u v: T), T) :=
    fun x u v =>
      match (@idP' (u != v)) with
      | ReflectT e => f_nodiag u v e
      | ReflectF _ => x
      end.

  Lemma f_total_agrees_with_f 
    (f_nodiag : (forall (u v: T) (e: u != v),  T)):
    forall (x u v: T) (e: u != v),
      f_nodiag u v e = (f_total f_nodiag  x u v).
  Proof.
    move=> x u v ; rewrite /f_total /idP'.
    move: (f_nodiag u v) => {f_nodiag}.
    case: (u != v) => // f' e.
    by rewrite (bool_irrelevance is_true_true e).
  Qed.

  
  Definition co_set_gt0:
    (forall (u v: T), u != v -> 0 < #|[set w | F u w & F v w]|).
  Proof. by move=> u v e; move: (co_set  e) => /eqP ->. Qed.

  Definition co_nodiag : (forall (u v: T), u != v -> T) := 
    fun (u v : T) (e: u != v) =>
       sval (sigW (card_gt0P (co_set_gt0 e))).

  Definition Co : (T -> T -> T) := f_total co_nodiag T_elem.

  Lemma Colr: forall u v : T, u != v -> F u (Co u v) /\ F v (Co u v).
  Proof.
    move=> u v e.
    rewrite /Co  -(f_total_agrees_with_f co_nodiag) /co_nodiag.
    have co_in_s :=  (proj2_sig (sigW (card_gt0P (co_set_gt0 e)))).
    set sig_proj := sval (sigW (card_gt0P (co_set_gt0 e))).
    rewrite -/sig_proj inE in co_in_s.
    by move: co_in_s => /andP [p1 p2].
  Qed.
    
  Definition Col u v (e : u != v) :=  proj1 (Colr  e).
  Definition Cor u v (e : u != v) :=  proj2 (Colr  e).

  Lemma CoUnique: forall u v w : T, u != v -> F u w -> F v w -> w = Co u v.
  Proof.
    move=> u v w e fuw fvw.
    rewrite /Co  -(f_total_agrees_with_f co_nodiag) /co_nodiag.
    move: (cards1P (co_set e)) => [x sx].
    have co_in_s :=  (proj2_sig (sigW (card_gt0P (co_set_gt0 e)))).
    set sig_proj := sval (sigW (card_gt0P (co_set_gt0 e))).
    rewrite -/sig_proj in co_in_s.
    rewrite sx in co_in_s.
    have /set1P : w \in [set x]  by rewrite -sx inE; apply/andP.
    move: co_in_s => /set1P co_in_s.
    congruence.
  Qed.
  
End StatementReduction.
