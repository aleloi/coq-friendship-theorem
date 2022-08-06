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
  Local Open Scope ring_scope.
  Context (n n': nat) (nn': n=n') (A B: 'M[R]_n).

  Lemma tr_castmx : \tr (castmx (nn', nn') A) = \tr A.
  Proof. by case: nn'; case: n' /; rewrite //=. Qed.
  
  Lemma summx_castmx:
    let cast := castmx (nn', nn') in 
    cast (A + B) = cast A + cast B.
  Proof. by case: nn'; case: n' /; rewrite //=. Qed.

  Lemma mulmx_castmx:
    let cast := castmx (nn', nn') in 
    cast (A *m B) = cast A *m cast B.
  Proof. by case: nn'; case: n' /; rewrite //=. Qed.

  Lemma scalar_mx_castmx (a: R) : castmx (nn', nn') a%:M = a%:M.
  Proof. by case: nn'; case: n' /; rewrite //=. Qed.

End casts.
