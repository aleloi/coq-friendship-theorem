From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint.
From mathcomp Require Import fintype (*tuple *) finfun bigop  (*fingroup perm*).
From mathcomp Require Import ssralg (*zmodp matrix mxalgebra poly (* polydiv *)
  mxpoly. *).
From mathcomp Require Import finset.

(*From mathcomp Require Import algC.*)
Require Import Lia.
From Hammer Require Import Tactics .

(*Require Import Friendship.adj2_matrix.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Import GroupScope.*)
Import GRing.Theory.
Local Open Scope ring_scope.

From mathcomp Require Import tuple seq.

Section bigops.

  (*
    Lära mig finset ?
    Predikat för positiv och negativ rot.
    Vill visa att SUMMAN av alla rötter
    
   *)
  Local Open Scope set_scope.
  Search GRing.natmul.
  
  Lemma big_bool [R: ringType] [S : Type]
           [I : seq S]  (a : pred S) (F : bool -> R):
    \sum_(i <- I) F (a i) =
      ((F true) *+ (count a I)) +
        ((F false) *+ (count (negb \o a) I)).
    
    elim: I => [| x I indH]. {
      rewrite big_nil //=; sauto.
    } {
      rewrite big_cons {}indH.
      set ax := (a x); have axx : (a x) = ax by [].
      move: axx.
      case: ax => axx; rewrite //= axx //= add0n mulrS addrA. {
        by [].
      } {
        by rewrite [in RHS] addrA;  rewrite [in X in X + (_ *+ _)]addrC.
      }
    }
  Qed.
  
End bigops.
