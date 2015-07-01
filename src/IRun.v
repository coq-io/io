Require Import Effect.
Require IC.
Require Run.

(** A run of an infinite computation. *)
CoInductive t {E : Effect.t} : forall {A : Type}, IC.t E A -> A -> Type :=
| Ret : forall {A} (x : A), t (IC.Ret (E := E) A x) x
| Call : forall (c : Effect.command E) (answer : Effect.answer E c),
  t (IC.Call (E := E) c) answer
| Let : forall {A B} {c_x : IC.t E A} {x : A} {c_f : A -> IC.t E B} {y : B},
  t c_x x -> t (c_f x) y -> t (IC.Let A B c_x c_f) y
| ChooseLeft : forall {A} {c_x1 c_x2 : IC.t E A} {x1 : A},
  t c_x1 x1 -> t (IC.Choose A c_x1 c_x2) x1
| ChooseRight : forall {A} {c_x1 c_x2 : IC.t E A} {x2 : A},
  t c_x2 x2 -> t (IC.Choose A c_x1 c_x2) x2
| Join : forall {A B} {c_x : IC.t E A} {x : A} {c_y : IC.t E B} {y : B},
  t c_x x -> t c_y y -> t (IC.Join A B c_x c_y) (x, y).

(** A lift from the finite runs. *)
Fixpoint ilift {E A} {x : C.t E A} {v : A} (r : Run.t x v) : t (IC.ilift x) v.
  destruct r; simpl.
  - apply Ret.
  - apply Call.
  - eapply Let.
    + apply (ilift _ _ _ _ r1).
    + apply (ilift _ _ _ _ r2).
  - apply ChooseLeft.
    apply (ilift _ _ _ _ r).
  - apply ChooseRight.
    apply (ilift _ _ _ _ r).
  - apply Join.
    + apply (ilift _ _ _ _ r1).
    + apply (ilift _ _ _ _ r2).
Defined.
