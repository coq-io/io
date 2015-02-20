Module Effects.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effects.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do an external call and
      wait for the answer to run another computation. *)
  Inductive t (E : Effects.t) : Type -> Type :=
  | Ret : forall {A : Type} (x : A), t E A
  | Call : forall (command : Effects.command E), t E (Effects.answer E command)
  | Let : forall {A B : Type}, t E A -> (A -> t E B) -> t E B.
  Arguments Ret {E A} _.
  Arguments Call E _.
  Arguments Let {E A B} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {E : Effects.t} {A : Type} (x : A) : t E A :=
      Ret x.

    (** A nicer notation for `Call`. *)
    Definition call (E : Effects.t) (command : Effects.command E)
      : t E (Effects.answer E command) :=
      Call E command.

    (** Nicer notation for `Let`. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (Let X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (Let X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the answer. *)
    Notation "'do!' X 'in' Y" :=
      (Let X (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End C.

Module Run.
  (** A run is an execution of the program with explicit answers for the
      system calls. We define a run by induction on a computation. *)
  Inductive t : forall {E : Effects.t} {A : Type}, C.t E A -> A -> Type :=
  | Ret : forall {E A} (x : A), t (C.Ret (E := E) x) x
  | Call : forall E (command : Effects.command E) (answer : Effects.answer E command),
    t (C.Call E command) answer
  | Let : forall {E A B} {c_x : C.t E B} {x : B} {c_f : B -> C.t E A} {y : A},
    t c_x x -> t (c_f x) y -> t (C.Let c_x c_f) y
  | Intro : forall {E A} (B : Type) {c : C.t E A} {x : A}, (B -> t c x) -> t c x.
End Run.
