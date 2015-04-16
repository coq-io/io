Require Import Effect.

(** The description of a computation. *)
Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall {A : Type} (x : A), t E A
| Call : forall (command : Effect.command E), t E (Effect.answer E command)
| Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
| Choose : forall (A : Type), t E A -> t E A -> t E A
| Join : forall (A B : Type), t E A -> t E B -> t E (A * B).

(** The implicit arguments so that the `match` command works both with
    Coq 8.4 and Coq 8.5. *)
Arguments Call {E} _.
Arguments Let {E} _ _ _ _.
Arguments Choose {E} _ _ _.
Arguments Join {E} _ _ _ _.

(** A nicer notation for `Ret`. *)
Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
  Ret E x.

(** A nicer notation for `Call`. *)
Definition call (E : Effect.t) (command : Effect.command E)
  : t E (Effect.answer E command) :=
  Call (E := E) command.

(** A nicer notation for `Choose`. *)
Definition choose {E : Effect.t} {A : Type} (x1 x2 : t E A) : t E A :=
  Choose _ x1 x2.

(** A nicer notation for `Join`. *)
Definition join {E : Effect.t} {A B : Type} (x : t E A) (y : t E B)
  : t E (A * B) :=
  Join _ _ x y.

(** Some optional notations. *)
Module Notations.
  (** A nicer notation for `Let`. *)
  Notation "'let!' x ':=' X 'in' Y" :=
    (Let _ _ X (fun x => Y))
    (at level 200, x ident, X at level 100, Y at level 200).

  (** Let with a typed answer. *)
  Notation "'let!' x : A ':=' X 'in' Y" :=
    (Let _ _ X (fun (x : A) => Y))
    (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

  (** Let ignoring the unit answer. *)
  Notation "'do!' X 'in' Y" :=
    (Let _ _ X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).
End Notations.
