Inductive Nat : Set := Z : Nat
                     | S : Nat -> Nat.

Fixpoint plus      (n m : Nat) := match n with
                                      | Z    => m
                                      | S n' => S (plus n' m)
                                  end.

Fixpoint plus_tail (n m : Nat) := match n with
                                      | Z    => m
                                      | S n' => plus_tail n' (S m)
                                  end.

Fixpoint plus_tail2 (n m a : Nat) := match n with
| Z => a
| S n' => plus_tail2 n' m (S a)
end.

Fixpoint mult      (n m : Nat) := match n with
                                      | Z    => Z
                                      | S n' => plus m (mult n' m)
                                  end.

Fixpoint mult_tail (a n m : Nat) := match n with
                                         | Z    => a
                                         | S n' => mult_tail (plus a m) n' m
                                     end.

(* Solve equalities by beta-normalising both sides *)
Ltac triv := try (simpl; reflexivity).

Lemma bar : forall n m, plus n m = plus_tail2 n m Z.
  induction n. simpl.


Lemma foo : forall w x y z, plus w (mult_tail x y z) = mult_tail (plus w x) y z.
  induction w; triv.
  induction y; triv.
  induction x. simpl.
  intro z.
  rewrite (IHw z y z).

 rewrite IHw.
  induction y; triv.
  simpl. intros y z. rewrite IHx.
  induction y; triv.
  simpl. rewrite 

Theorem mequiv : forall n m, mult n m = mult_tail Z n m.
  induction n; triv.
  simpl. intro m. rewrite IHn.
  induction m; triv.

 simpl. induction n; triv. simpl.
  induction m; triv. simpl. rewrite IHm. reflexivity.

plus m (mult_tail Z n m) = mult_tail m n m


Theorem pcomm : forall n m, plus n m = plus m n.
induction n.
{ induction m; simpl.
  { reflexivity. }
  { rewrite <- IHm. reflexivity. }
} 
{ simpl. intro m. rewrite (IHn m).
  induction m; simpl.
  { reflexivity. }
  { rewrite IHm. reflexivity. }
}
Defined.


Lemma gen n m : plus (S n) m = plus n (S m).
  induction n; triv. (* Base case is trivial *)

  (* Move all S constructors outside *)
  simpl. rewrite <- IHn. simpl.

  (* Trivial *)
  reflexivity.
Defined.

(* Prove equivalence of plus and plus_tail *)
Theorem equiv : forall n m, plus n m = plus_tail n m.
  induction n; triv. (* Base case is trivial *)

  (* Inductive case: plus (S n) m = plus_tail (S n) m *)
  intro m.

  (* Beta-reduce the right-hand-side (justification is trivial) *)
  replace (plus_tail (S n) m) with (plus_tail n (S m)); triv.

  (* Use induction hypothesis to replace plus_tail with plus *)
  rewrite <- (IHn (S m)).

  (* Specialise the generalisation for our use-case to complete the proof *)
  rewrite (gen n m).
  reflexivity.
Defined.
