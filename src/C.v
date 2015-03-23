Require Import Effect.

(** The description of a computation. *)
Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall {A : Type} (x : A), t E A
| Call : forall (command : Effect.command E), t E (Effect.answer E command)
| Let : forall {A B : Type}, t E A -> (A -> t E B) -> t E B
| Join : forall {A B : Type}, t E A -> t E B -> t E (A * B)
| First : forall {A B : Type}, t E A -> t E B -> t E (A + B).
Arguments Ret {E A} _.
Arguments Call E _.
Arguments Let {E A B} _ _.
Arguments Join {E A B} _ _.
Arguments First {E A B} _ _.

(** A nicer notation for `Ret`. *)
Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
  Ret x.

(** A nicer notation for `Call`. *)
Definition call (E : Effect.t) (command : Effect.command E)
  : t E (Effect.answer E command) :=
  Call E command.

(** A nicer notation for `Join`. *)
Definition join {E : Effect.t} {A B : Type} (x : t E A) (y : t E B)
  : t E (A * B) :=
  Join x y.

(** A nicer notation for `First`. *)
Definition first {E : Effect.t} {A B : Type} (x : t E A) (y : t E B)
  : t E (A + B) :=
  First x y.

(** A run from an effect to a more general effect. *)
Fixpoint run {E1 E2 : Effect.t} {A : Type}
  (run_command : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c))
  (x : C.t E1 A) : C.t E2 A.
  destruct x as [A x | c | A B x f | A B x y | A B x y].
  - exact (C.Ret x).
  - exact (run_command c).
  - exact (C.Let (run _ _ _ run_command x) (fun x =>
      run _ _ _ run_command (f x))).
  - exact (C.Join (run _ _ _ run_command x) (run _ _ _ run_command y)).
  - exact (C.First (run _ _ _ run_command x) (run _ _ _ run_command y)).
Defined.

(** Some optional notations. *)
Module Notations.
  (** A nicer notation for `Let`. *)
  Notation "'let!' x ':=' X 'in' Y" :=
    (Let X (fun x => Y))
    (at level 200, x ident, X at level 100, Y at level 200).

  (** Let with a typed answer. *)
  Notation "'let!' x : A ':=' X 'in' Y" :=
    (Let X (fun (x : A) => Y))
    (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

  (** Let ignoring the unit answer. *)
  Notation "'do!' X 'in' Y" :=
    (Let X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).
End Notations.
