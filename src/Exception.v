Require Import Coq.Lists.List.
Require C.
Require Evaluate.
Require List.

Import ListNotations.
Import C.Notations.

Module Command.
  Inductive t (E : Effect.t) (Exc : Type) :=
  | Ok (command : Effect.command E)
  | Exc (exc : Exc).
  Arguments Ok [E Exc] _.
  Arguments Exc [E Exc] _.
End Command.

Definition answer {E : Effect.t} {Exc : Type} (c : Command.t E Exc) : Type :=
  match c with
  | Command.Ok c => Effect.answer E c
  | Command.Exc exc => Empty_set
  end.

Definition effect (E : Effect.t) (Exc : Type) : Effect.t :=
  Effect.New (Command.t E Exc) answer.

Definition lift {E : Effect.t} {Exc A : Type} (x : C.t E A)
  : C.t (effect E Exc) A :=
  Evaluate.command (fun c => call (effect E Exc) (Command.Ok c)) x.

Definition raise {E : Effect.t} {Exc A : Type} (exc : Exc)
  : C.t (effect E Exc) A :=
  let! absurd := call (effect E Exc) (Command.Exc exc) in
  match absurd with end.

Definition eval {E : Effect.t} {Exc A : Type} (x : C.t (effect E Exc) A)
  : C.t E (A + list Exc) :=
  Evaluate.exception (fun (c : Effect.command (effect E Exc)) =>
    match c with
    | Command.Ok c =>
      let! answer := call E c in
      ret (inl answer)
    | Command.Exc exc => ret (inr [exc])
    end)
    (List.app (A := Exc)) x.

Definition handle {E : Effect.t} {Exc : Type} (run_exc : Exc -> C.t E unit)
  (x : C.t E (unit + list Exc)) : C.t E unit :=
  let! x := x in
  match x with
  | inl x => ret x
  | inr exc => List.iter_seq run_exc exc
  end.
