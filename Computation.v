(** The definition of computations, used to represent interactive programs. *)
Require Effect.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do an external call and
      wait for the answer to run another computation. *)
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : forall (x : A), t E A
  | Call : forall (command : Effect.command E),
    (Effect.answer E command -> t E A) -> t E A
  | Let : forall (B : Type), t E B -> (B -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Let {E A B} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
      Ret x.

    (** External call. *)
    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    (** External call with typed answer. *)
    Notation "'call!' answer : A ':=' command 'in' X" :=
      (Call command (fun (answer : A) => X))
      (at level 200, answer ident, command at level 100, A at level 200, X at level 200).

    (** External call ignoring the answer. *)
    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).

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
