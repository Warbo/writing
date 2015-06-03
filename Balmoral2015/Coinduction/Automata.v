

Section InductiveList.

  (*Inductive type*)


  
Inductive List (A:Set) : Set :=
Nil : List A 
|Cons : A -> List A  -> List A.

(*Note this defines a set closed forwards under the above rules *)

Variable A:Set.
Arguments Nil [A].
Set Implicit Arguments.


(*Note: here the fact that every given list satisfies the forward closure is guaranteed by the construction of the type. But we could prove a similar lemma to the one on the slides *)

Inductive isL (A:Set): List A -> Prop :=
| nilc: isL Nil
| consc: forall (a:A) (l: List A), isL l -> isL (Cons A a l).


(*and have the Lemma*)

Lemma littleL: forall (A: Set) (u: List A), isL u.
intros A0 u.
(*Lets look at the inductive proof principle here:*)
induction u.
(*we have two rules, and must apply them in a forward manner*)
apply nilc.
apply consc.
trivial.

(*
  intros A0 u; induction u; try apply nilc; try apply consc;
  simpl; auto.*)
Qed.

(*Note the induction tactic now explicitely re-uses the inductive reasoning of the slide examples
*)
  

(* Alternatively, we can use  fixed-point functions on the type: *)

Fixpoint isList (A:Set)  (l: List A)  : Prop :=
  match l with
      | Nil => True
      | Cons _ a l' => isList l'
                            end.

Inductive MySet: Set :=
| a : MySet
| b: MySet.        



Eval compute in (isList  (Cons MySet a Nil) ).

(*Compare with:*)

Eval compute in (isL  (Cons MySet a Nil) ).



Lemma MySetL: isL (Cons MySet a Nil).
apply littleL.
Qed.


(*Now lets see how coinduction works*)

CoInductive LList (A:Set) : Set :=
LNil : LList A
|LCons : A -> LList A -> LList A.

(* This set defines the maximal set closed baclwards by these rules. Note: definition does not differ from 
  
Inductive List (A:Set) : Set :=
Nil : List A 
|Cons : A -> List A  -> List A.
*)


Arguments LNil [A].




(*Properties of the set *)

Inductive Finite (A: Set): LList A -> Prop :=
|Finite_LNil: Finite LNil
|Finite_LCons: forall (a : A) (l: LList A), Finite l -> Finite (LCons a l). 

CoInductive Infinite (A : Set): LList A -> Prop :=
Infinite_LCons: forall (a : A) (l: LList A), Infinite l -> Infinite (LCons a l).



Fixpoint LNth (A : Set) (n: nat) (l: LList A) {struct n}:
option A :=
match l with 
| LNil => None
| LCons x l' => match n with O => Some x | S p => LNth p l' end
end.

(*Now lets take our example from the slides*)

CoFixpoint MyLlist (a b: MySet) : LList MySet := (LCons a (LCons b (MyLlist a b))).

(*It is a variant of our usual repeat or from*)

CoFixpoint repeat (A : Set) (x : A) : LList A :=
LCons x (repeat x).
  
CoFixpoint from (n: nat) : LList nat := LCons n (from (S n)).

Definition MyLlistab := MyLlist a b.


Eval compute in (LNth 5 MyLlistab).

(*Note: here the fact that the list a::b::a::b::... is an infinite list in ensured by the consttruction of the type. But we could prove a similar lemma to the one on the slides *)


(****** To prove theorems involving coinductive sets, we need coinductive proof principle and decomposition lemmas *****)



Definition LList_decompose (A: Set) (l: LList A) : LList A :=
match l with
| LNil => LNil
| LCons x l' => LCons x l'
end.

Eval simpl in (repeat 0).
Eval simpl in (LList_decompose (repeat 0)).
Eval simpl in ( MyLlistab).
Eval simpl in (LList_decompose ( MyLlistab)).

Theorem LList_decomposition_lemma :
forall (A : Set) (l: LList A), l = LList_decompose l.
intros; case l. 
trivial.
intros.
unfold LList_decompose.
trivial.
Qed.

Eval compute in MyLlistab.

Eval compute in (LList_decomposition_lemma MyLlistab).

Definition foo : MyLlistab = LList_decompose MyLlistab := LList_decomposition_lemma
         ((cofix
           MyLlist (a b : MySet) :
             LList MySet :=
             LCons a
               (LCons b
                  (MyLlist a b)))
            a b).

Eval compute in foo.

Ltac LList_unfold term :=
  apply trans_equal with (1 := LList_decomposition_lemma term).

(*

Theorem LAppend_LNil : forall (A : Set)(v: LList A), LAppend LNil v = v.
intros.
LList_unfold (LAppend LNil v).
case v; simpl; auto.
Qed.

Theorem LAppend_LCons:
forall (A : Set) (a: A) (u v : LList A),
LAppend (LCons a u) v  = LCons a (LAppend u v).
intros A0 a u v.
LList_unfold (LAppend (LCons a u) v).
case v; simpl; auto.
Qed.

*)

Lemma from_unfold : forall n:nat, from n = LCons n (from (S n)).
intro.
LList_unfold (from n).
case n; simpl; auto.
Qed.


Lemma repeat_unfold : forall (A: Set)(x: A), repeat x = LCons x (repeat x).
intros.
LList_unfold (repeat x).
simpl; auto.
Qed.

(*The below lemma shows that the stream (from n) is included in the set of all infinite lists
The same technique of backward closure applies
*)


Theorem from_Infinite : forall n: nat, Infinite (from n).
  cofix H. (*we close backwards *)
  (*we then show that premises can be satisfied*)
  intro n; rewrite (from_unfold n).
  (*we have matched with the second rule for second constructor*)
  (*does the premise of the rule work?*)
split.
trivial.
Qed.

Print from_Infinite.

Lemma repeat_infinite : forall (A: Set) (a: A), Infinite (repeat a).
cofix H.
intros.
rewrite (repeat_unfold).
split; auto.
Qed.


(***Exercise 1. Prove the theorem from the slides that a::b::a::b::... ( MyLlistab) is Infinite *)

Lemma myllistab_infinite : Infinite MyLlistab.
cofix H.
assert (p := LList_decomposition_lemma MyLlistab).
simpl in p. rewrite p. split. split. auto.
Qed.

(*************Below are slightly more generalised versions of decomposition method -- probably not needed now****)


CoFixpoint general_omega (A: Set) (u v :LList A) : LList A :=
match v with
| LNil => u
| LCons y v' =>
   match u with 
   | LNil => LCons y (general_omega v' v)
   | LCons x u' => LCons x (general_omega u' v)
   end
end.

Definition omega (A: Set) (u: LList A): LList A :=
general_omega u u.

Print trans_equal.

Eval simpl in (LList_decompose (repeat 33)).

Fixpoint LList_decomp_n (n: nat) (A : Set) (l: LList A){struct n}: LList A :=
match n, l with 
O, l' => l'|
S n', LNil  =>  LNil| 
S n', LCons x l' => LCons x (LList_decomp_n n' l')
end.

Print LList_decomp_n.

(*
Eval simpl in (LList_decomp_n 4 (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))).*)

Eval simpl in (LList_decomp_n 6 (repeat 0)).

Theorem LList_decompose_n_lemma :
forall (A: Set)(n:nat)(l: LList A), l = LList_decomp_n n l.
induction n; intros. 
simpl; trivial.
case l.
simpl; trivial.
simpl.
intros.
rewrite <- IHn.
trivial.
Qed.

Lemma general_omega_LNil : forall A: Set, general_omega LNil LNil = LNil (A := A).
intro A0.
apply sym_equal.
rewrite LList_decomposition_lemma.
simpl; auto.
Qed.

Lemma general_omega_LCons : forall (A: Set) (x : A)
(u v :LList A), 
general_omega (LCons x u) v = LCons x (general_omega u v).
intros.
LList_unfold (general_omega (LCons x u) v).
case v; simpl; auto. 
case u; simpl; auto.
rewrite general_omega_LNil.
trivial.
intros.
rewrite LList_decomposition_lemma with (l := general_omega (LCons a0 l) LNil).
simpl; auto.
Qed.

Lemma general_omega_LNil_LCons : forall (A : Set) (x : A) (u : LList A),
general_omega LNil (LCons x u) = LCons x (general_omega u (LCons x u)).
intros.
LList_unfold (general_omega LNil (LCons x u)).
case u; simpl; auto.
Qed.

Lemma general_omega_shoots_again : forall (A : Set)(v: LList A),
general_omega LNil v  = general_omega v v.
intros.
LList_unfold (general_omega LNil v).
case v; simpl; auto.
apply sym_equal.
apply general_omega_LNil.
intros.
rewrite LList_decomposition_lemma with (l := general_omega (LCons a0 l) (LCons a0 l)).
simpl; auto.
Qed.



Lemma general_omega_infinite : forall (A: Set) (x:A)
 (u v : LList A),
Infinite (general_omega v (LCons x u)).
cofix H.
intros.
case v.
rewrite general_omega_LNil_LCons.
split; auto.
intros.
rewrite general_omega_LCons with (v := LCons x u).
split; auto.
Qed.

Theorem omega_infinite :
forall (A: Set)(x :A)(l : LList A), 
Infinite (omega (LCons x l)).
unfold omega.
cofix H.
intros.
case l. 
simpl.
rewrite LList_decomposition_lemma with (l := general_omega (LCons x LNil) (LCons x LNil)).
simpl; auto.
split; auto.
apply general_omega_infinite.
intros.
rewrite LList_decomposition_lemma with (l := general_omega (LCons x (LCons a0 l0)) (LCons x (LCons a0 l0))).
simpl; auto.
split; auto.
rewrite general_omega_LCons.
split; auto.
apply general_omega_infinite.
Qed.

(************ End of decomposition lemmas *********)




Section Automata.
Set Implicit Arguments.

  
  (*Simpler automaton *)

 Record automaton2: Type :=
    mk_auto2 {
        states2 : Set;
        actions2: Set;
        initial2: states2;
        transitions2: states2 -> actions2 -> states2
             }.


  Require Import Le Gt Minus Bool Setoid List.






(*Consider the automaton*)

(*states*)

Inductive st2 : Set := p0 | p1 .

(*actions*)

Inductive acts2 : Set := c .




(*transitions*)

Definition trans2 (q:st2) (x:acts2) :  st2 :=
  match q, x with
    | p0, c =>  p1 
    | p1, c =>  p0 
  end.


Definition A2 := mk_auto2 p0 trans2.
Print A2.


CoFixpoint TraceA (s: LList st2)  :  LList st2 :=
  match s with
    | LNil => LNil
    | LCons x xs => LCons (trans2 x c) (TraceA (LCons (trans2 x c)  xs))
  end.



Eval simpl in (TraceA (LCons p0 LNil)).


Eval simpl in (LList_decomp_n 8 (TraceA (LCons p0 LNil))).

Eval compute in (LNth 5   (TraceA (LCons p0 LNil)) ).
Eval compute in (LNth 6   (TraceA (LCons p0 LNil)) ).

(*Prove the following example from the slides*)

Theorem Inf_simpl: forall l, Infinite (TraceA (LCons p1 l)) -> Infinite (TraceA (LCons p0 l)).
  cofix H1.
  intros.
  rewrite LList_decomposition_lemma with (l := (TraceA (LCons p0 l))).
  simpl.
apply Infinite_LCons.
trivial.
Qed.

Theorem Inf_simpl2 : forall l, Infinite (TraceA (LCons p0 l)).
  intros.
  cofix H.
  assert (p := LList_decomposition_lemma (TraceA (LCons p0 l))).
  simpl in p.
  rewrite p.
  assert (p2 := LList_decomposition_lemma (TraceA (LCons p1 l))).
  simpl in p2.
  rewrite p2.
  apply Infinite_LCons. apply Infinite_LCons.
  auto.
Qed.

(*Repeat same actions for automata in the lecture slides*)


(*More elaborate automaton*)

  Record automaton: Type :=
    mk_auto {
        states : Set;
        actions: Set;
        initial: states;
        transitions: states -> actions -> list states
             }.
  Definition stopped (A:automaton)(q:states A) :=
    forall a:actions A, @transitions A q a = nil.
        
  Unset Implicit Arguments.

  Require Import Le Gt Minus Bool Setoid List.

CoInductive Trace (A: automaton) : states A -> LList (actions A) -> Prop:=
 | empty_trace : forall (q:states A), stopped A q -> Trace A q LNil
 | lcons_trace : forall (q q': states A)(a: actions A)(l: LList (actions A)),
                   In q' (transitions A q a) -> Trace A q' l -> Trace A q (LCons a l).




(*Consider the automaton*)


(*actions*)

Definition acts := MySet.

(*states*)

Inductive st : Set := q0 | q1 | q2.

(*transitions*)

Definition trans (q:st) (x:acts) : list st :=
  match q, x with
    | q0, a => cons q1 nil
    | q0, b => cons q1 nil
    | q1, a => cons q2 nil
    | q2, b => cons q2 (cons q1 nil)
    | _,_ => nil (A:=_)
 end.


Definition A1 := mk_auto q0 trans.


(*Draw this automaton, then show that every trace for A1 contains an infinite numberof b actions*)

Definition satisfies (A:Set) (l:LList A)(P:LList A -> Prop) : Prop :=
  P l.

Set Implicit Arguments.
  
  
 Inductive Eventually (A:Set) (P:LList A -> Prop) : LList A -> Prop :=
   | Eventually_here :
       forall (a:A) (l:LList A), P (LCons a l) -> Eventually P (LCons a l)
   | Eventually_further :
       forall (a:A) (l:LList A), Eventually P l -> Eventually P (LCons a l).

 Hint Resolve Eventually_here Eventually_further: llists.



 CoInductive Always  (A:Set) (P:LList A -> Prop) : LList A -> Prop :=
    Always_LCons :
        forall (a:A) (l:LList A),
          P (LCons a l) -> Always P l -> Always P (LCons a l).

  
 Hint Resolve Always_LCons: llists.



 Definition F_Infinite (A:Set) (P:LList A -> Prop) : LList A -> Prop :=
   Always (Eventually P).


 Inductive Atomic (A:Set) (At:A -> Prop) : LList A -> Prop :=
     Atomic_intro : forall (a:A) (l:LList A), At a -> Atomic At (LCons a l).

 Hint Resolve Atomic_intro: llists.

 
Theorem Infinite_bs: forall (q:st) (t:LList acts),
                       Trace A1 q t -> satisfies _ t (F_Infinite (Atomic (eq b))).
intros. auto.





End Automata.





End Coinduction.

(*Some leftovers *)


(*
CoFixpoint LAppend (A: Set) (u v :LList A) : LList A :=
match u with
| LNil => v
| LCons a u' => LCons a (LAppend u' v)
end.
*)


(* Some more Dfs

Definition isEmpty (A: Set) (l : LList A) : Prop :=
match l with LNil => True | LCons a l' => False end.

Definition LHead (A: Set) (l: LList A) : option A :=
match l with | LNil => None | LCons a l' => Some a end.

Definition LTail (A: Set) (l: LList A): LList A :=
match l with LNil => LNil | LCons a l' => l' end.


*)


Theorem LNil_not_Infinite : forall (A :Set), ~ Infinite (LNil (A := A)).
intros A0 H; inversion H.
Qed.

Theorem Infinite_of_LCons :
forall (A : Set) (a : A) (u: LList A),
Infinite (LCons a u) -> Infinite u.
intros A0 a u H0; inversion H0.
exact H1.
Qed.

(*

Lemma LAppend_of_Infinite : forall (A :Set) (u: LList A),
Infinite u -> forall v: LList A, Infinite (LAppend u v).
cofix H5.
intros A0 u H0; inversion H0.
intro.
Check LAppend_LCons.
rewrite LAppend_LCons.
split; auto.
Guarded.
Qed.

*)


Lemma Finite_not_Infinite :
forall (A : Set) (l : LList A), Finite l -> ~ Infinite l.
intros A0 l Hl.
induction Hl.
intro Hinf; inversion Hinf.
intros Hcons.
assert (Hl'_inf:Infinite l).
apply (@Infinite_of_LCons A0 a0 l); assumption.
contradiction.
Qed.


Lemma Infinite_not_Finite :
forall (A : Set) (l: LList A), Infinite l -> ~ Finite l.
unfold not.
intros A0 l H H1; induction H1; auto.
inversion H.
inversion H.
assert (Hn: ~ Infinite l).
unfold not; assumption.
contradiction.
Qed.
















 










