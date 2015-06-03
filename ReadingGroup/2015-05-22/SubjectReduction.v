(*
 http://permalink.gmane.org/gmane.science.mathematics.logic.coq.club/2396
 *)
CoInductive U : Set
  := inf : U -> U.

CoFixpoint u : U := inf u.

Definition force : U -> U
  := fun x => match x with
                  | inf y => inf y
              end.

Definition eq : forall x, x = force x
  := fun x => match x with
                  | inf y => eq_refl
              end.

Definition equ : u = inf u
  := eq u.

Eval compute in equ.

Definition equ2 : u = inf u := eq_refl.