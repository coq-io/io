Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

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
  Arguments Call _ {A} _ _.
  Arguments Let {E A B} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
      Ret x.

    (** A nicer notation for `Call`. *)
    Definition call (E : Effect.t) {A : Type} (command : Effect.command E)
      (handler : Effect.answer E command -> t E A) : t E A :=
      Call E command handler.

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
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> A -> Type :=
  | Ret : forall {A} (x : A), t (C.Ret x) x
  | Call : forall {A} (command : Effect.command E) (answer : Effect.answer E command)
    {handler : Effect.answer E command -> C.t E A} {x : A}, t (handler answer) x ->
    t (C.Call E command handler) x
  | Let : forall {A B} {c_x : C.t E B} {x : B} {c_f : B -> C.t E A} {y : A},
    t c_x x -> t (c_f x) y -> t (C.Let c_x c_f) y
  | Intro : forall {A} (B : Type) {c : C.t E A} {x : A}, (B -> t c x) -> t c x.
End Run.

Module Unix.
  Require Import ListString.All.

  Inductive t :=
  (** List the files of a directory. *)
  | ListFiles (directory : LString.t)
  (** Read the content of a file. *)
  | ReadFile (file_name : LString.t)
  (** Update (or create) a file with some content. *)
  | WriteFile (file_name : LString.t) (content : LString.t)
  (** Delete a file. *)
  | DeleteFile (file_name : LString.t)
  (** Run a command. *)
  | System (command : LString.t)
  (** Print a message on the standard output. *)
  | Print (message : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | ListFiles _ => option (list LString.t)
    | ReadFile _ => option LString.t
    | WriteFile _ _ => bool
    | DeleteFile _ => bool
    | System _ => option bool
    | Print _ => bool
    end.

  Definition effect : Effect.t := {|
    Effect.command := t;
    Effect.answer := answer |}.
End Unix.
