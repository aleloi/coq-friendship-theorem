From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq.
From mathcomp Require Import fintype (*tuple *) finfun bigop fintype (*fingroup perm*).
From mathcomp Require Import ssralg zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly.

(*Require Import Lia.

From Hammer Require Import Hammer. (* for `hammer` *)
From Hammer Require Import Tactics .
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section casts.
  Variable (R : ringType).
  (*Import GRing.Theory.
  Import Monoid.Theory.*)
  Local Open Scope ring_scope.
  Context (n n': nat) (nn': n=n') (A B: 'M[R]_n).
  
  Lemma summx_castmx:
    let cast := castmx (nn', nn') in 
    cast (A + B) = cast A + cast B.
  Proof.
    apply/matrixP => i j.
    rewrite  !castmxE !mxE !castmxE.
    set c := (cast_ord (esym (nn', nn').1 )).
    by [].
  Qed.

  Lemma mulmx_castmx:
    let cast := castmx (nn', nn') in 
    cast (A *m B) = cast A *m cast B.
  Proof.
    apply/matrixP => i j.
    rewrite  !castmxE !mxE.
    set c := (cast_ord (esym (nn', nn').1 )).
        
    rewrite (eq_bigr (fun α => A (c i) (c α) * B (c α) (c j))); last first. {
      move=>  α _.
      by rewrite !castmxE -/c.
    }
    simpl in c.
    have cinj := (@cast_ord_inj _ _ (esym nn')).
    
    rewrite -/c in cinj.
    
    
    rewrite (@reindex _ _ _ (ordinal_finType n) (ordinal_finType n') c) //=.
    apply: inW_bij.
    apply: (@Bijective _ _ c (cast_ord nn')).
    rewrite /c. apply:  (cast_ordKV nn').
    apply cast_ordK.
  Qed.

  Lemma scalar_mx_castmx (a: R) : castmx (nn', nn') a%:M = a%:M.
  Proof.
    apply/matrixP => i j.
    rewrite !castmxE !mxE.
    case: (@idP (i == j)) => //=. {
      by move=> /eqP ->; rewrite eq_refl.
    } {
      move=> /negP ij.
      case: (@idP (cast_ord (esym nn') i == cast_ord (esym nn') j)) => //= /eqP are_eq.
      rewrite (cast_ord_inj are_eq) eq_refl in ij.
      by move: ij => /negP.
    }
  Qed.
End casts.
