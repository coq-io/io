Require Effect.

(** The description of a computation. *)
Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall (A : Type) (x : A), t E A
| Call : forall (command : Effect.command E), t E (Effect.answer E command)
| Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
| Choose : forall (A : Type), t E A -> t E A -> t E A
| Join : forall (A B : Type), t E A -> t E B -> t E (A * B).

(** The implicit arguments so that the `match` command works both with
    Coq 8.4 and Coq 8.5. *)
Arguments Ret {E} _ _.
Arguments Call {E} _.
Arguments Let {E} _ _ _ _.
Arguments Choose {E} _ _ _.
Arguments Join {E} _ _ _ _.

(** Some optional notations. *)
Module Notations.
  (** A nicer notation for `Ret`. *)
  Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
    Ret A x.

  (** A nicer notation for `Call`. *)
  Definition call (E : Effect.t) (command : Effect.command E)
    : t E (Effect.answer E command) :=
    Call (E := E) command.

  (** A nicer notation for `Choose`. *)
  Definition choose {E : Effect.t} {A : Type} (x1 x2 : t E A) : t E A :=
    Choose A x1 x2.

  (** A nicer notation for `Join`. *)
  Definition join {E : Effect.t} {A B : Type} (x : t E A) (y : t E B)
    : t E (A * B) :=
    Join A B x y.

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

Module I.
  (** The description of an infinite computation. *)
  CoInductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall (A : Type) (x : A), t E A
  | Call : forall (command : Effect.command E), t E (Effect.answer E command)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
  | Choose : forall (A : Type), t E A -> t E A -> t E A
  | Join : forall (A B : Type), t E A -> t E B -> t E (A * B).

  (** The implicit arguments so that the `match` command works both with
      Coq 8.4 and Coq 8.5. *)
  Arguments Ret {E} _ _.
  Arguments Call {E} _.
  Arguments Let {E} _ _ _ _.
  Arguments Choose {E} _ _ _.
  Arguments Join {E} _ _ _ _.

  Definition unfold {E A} (x : t E A) : t E A :=
    match x with
    | Ret _ v => Ret _ v
    | Call c => Call c
    | Let _ _ x f => Let _ _ x f
    | Choose _ x1 x2 => Choose _ x1 x2
    | Join _ _ x y => Join _ _ x y
    end.

  Definition unfold_eq {E A} (x : t E A) : x = unfold x.
    destruct x; reflexivity.
  Defined.

  (** A lift from the finite computations. *)
  Fixpoint lift {E : Effect.t} {A : Type} (x : C.t E A) : t E A :=
    match x with
    | C.Ret _ v => Ret _ v
    | C.Call c => Call c
    | C.Let _ _ x f => Let _ _ (lift x) (fun v_x => lift (f v_x))
    | C.Choose _ x1 x2 => Choose _ (lift x1) (lift x2)
    | C.Join _ _ x y => Join _ _ (lift x) (lift y)
    end.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition iret {E : Effect.t} {A : Type} (x : A) : t E A :=
      Ret A x.

    (** A nicer notation for `Call`. *)
    Definition icall (E : Effect.t) (command : Effect.command E)
      : t E (Effect.answer E command) :=
      Call (E := E) command.

    (** A nicer notation for `Choose`. *)
    Definition ichoose {E : Effect.t} {A : Type} (x1 x2 : t E A) : t E A :=
      Choose A x1 x2.

    (** A nicer notation for `Join`. *)
    Definition ijoin {E : Effect.t} {A B : Type} (x : t E A) (y : t E B)
      : t E (A * B) :=
      Join A B x y.

    (** A nicer notation for `Let`. *)
    Notation "'ilet!' x ':=' X 'in' Y" :=
      (Let _ _ X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'ilet!' x : A ':=' X 'in' Y" :=
      (Let _ _ X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the unit answer. *)
    Notation "'ido!' X 'in' Y" :=
      (Let _ _ X (fun (_ : unit) => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End I.
