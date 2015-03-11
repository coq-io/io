Require Import Effects.

(** A computation can either return a pure value, do an external call or
    compose two computations. *)
Inductive t (E : Effects.t) : Type -> Type :=
| Ret : forall {A : Type} (x : A), t E A
| Call : forall (command : Effects.command E), t E (Effects.answer E command)
| Let : forall {A B : Type}, t E A -> (A -> t E B) -> t E B
| Join : forall {A B : Type}, t E A -> t E B -> t E (A * B)
| First : forall {A B : Type}, t E A -> t E B -> t E (A + B).
Arguments Ret {E A} _.
Arguments Call E _.
Arguments Let {E A B} _ _.
Arguments Join {E A B} _ _.
Arguments First {E A B} _ _.

(** Some optional notations. *)
Module Notations.
  (** A nicer notation for `Ret`. *)
  Definition ret {E : Effects.t} {A : Type} (x : A) : t E A :=
    Ret x.

  (** A nicer notation for `Call`. *)
  Definition call (E : Effects.t) (command : Effects.command E)
    : t E (Effects.answer E command) :=
    Call E command.

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

  (** A nicer notation for `Join`. *)
  Definition join {E : Effects.t} {A B : Type} (x : t E A) (y : t E B)
    : t E (A * B) :=
    Join x y.

  (** A nicer notation for `First`. *)
  Definition first {E : Effects.t} {A B : Type} (x : t E A) (y : t E B)
    : t E (A + B) :=
    First x y.
End Notations.
