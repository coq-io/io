(** Runs. *)
Require Import Computation.
Require Effect.

(** A run is an execution of the program with explicit answers for the
    system calls. We define a run by induction on a computation. *)
Inductive t {E : Effect.t} : forall {A}, C.t E A -> A -> Type :=
| Ret : forall {A} (x : A), t (C.Ret x) x
| Call : forall {A} (command : Effect.command E) (answer : Effect.answer E command)
  {handler : Effect.answer E command -> C.t E A} {x : A}, t (handler answer) x ->
  t (C.Call command handler) x
| Let : forall {A B} {c_x : C.t E B} {x : B} {c_f : B -> C.t E A} {y : A},
  t c_x x -> t (c_f x) y -> t (C.Let c_x c_f) y
| Intro : forall {A} (B : Type) {c : C.t E A} {x : A}, (B -> t c x) -> t c x.
