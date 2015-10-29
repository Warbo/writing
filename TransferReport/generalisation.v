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

(* Solve equalities by beta-normalising both sides *)
Ltac triv := try (simpl; reflexivity).

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
