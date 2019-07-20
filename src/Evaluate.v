Require C.
Require Run.

Import C.Notations.
Local Open Scope type.

Fixpoint pure {E : Effect.t} {A : Type}
  (eval : forall (c : Effect.command E), Effect.answer E c)
  (eval_choose : forall A, A -> A -> A) (x : C.t E A) : A :=
  match x with
  | C.Ret v => v
  | C.Call c => eval c
  | C.Let x f =>
    let x := pure eval eval_choose x in
    pure eval eval_choose (f x)
  | C.Join x y => (pure eval eval_choose x, pure eval eval_choose y)
  | C.Choose x y =>
    eval_choose _ (pure eval eval_choose x) (pure eval eval_choose y)
  end.

(** Evaluate the commands of a computation using other commands. *)
Fixpoint command {E1 E2 : Effect.t} {A : Type}
  (eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c))
  (x : C.t E1 A) : C.t E2 A :=
  match x with
  | C.Ret v => C.Ret v
  | C.Call c => eval c
  | C.Let x f => C.Let (command eval x) (fun x => command eval (f x))
  | C.Join x y => C.Join (command eval x) (command eval y)
  | C.Choose x y => C.Choose (command eval x) (command eval y)
  end.

Fixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
  (eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c + Exc))
  (eval_join : Exc -> Exc -> Exc) (x : C.t E1 A) : C.t E2 (A + Exc) :=
  match x with
  | C.Ret v => ret (inl v)
  | C.Call c => eval c
  | C.Let x f =>
    let! x := exception eval eval_join x in
    match x with
    | inl x => exception eval eval_join (f x)
    | inr exc => ret (inr exc)
    end
  | C.Join x y =>
    let! xy := join (exception eval eval_join x) (exception eval eval_join y) in
    match xy with
    | (inl x, inl y) => ret (inl (x, y))
    | (inr exc, inl _) | (inl _, inr exc) => ret (inr exc)
    | (inr exc_x, inr exc_y) => ret (inr (eval_join exc_x exc_y))
    end
  | C.Choose x y =>
    choose (exception eval eval_join x) (exception eval eval_join y)
  end.

Fixpoint state {E1 E2 : Effect.t} {S A : Type}
  (eval : forall (c : Effect.command E1), S -> C.t E2 (Effect.answer E1 c * S))
  (eval_join : S -> S -> S) (x : C.t E1 A) (s : S) : C.t E2 (A * S) :=
  match x with
  | C.Ret v => ret (v, s)
  | C.Call c => eval c s
  | C.Let x f =>
    let! x := state eval eval_join x s in
    let (v_x, s) := x in
    state eval eval_join (f v_x) s
  | C.Join x y =>
    let! xy := join (state eval eval_join x s) (state eval eval_join y s) in
    match xy with
    | ((v_x, s_x), (v_y, s_y)) => ret ((v_x, v_y), eval_join s_x s_y)
    end
  | C.Choose x y =>
    choose (state eval eval_join x s) (state eval eval_join y s)
  end.

Module Monad.
  Record t (M : Type -> Type) : Type := New {
    ret : forall {A : Type}, A -> M A;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B }.
  Arguments ret {M} _ {A} _.
  Arguments bind {M} _ {A B} _ _.
End Monad.

Module EvalMonad.
  Record t (E : Effect.t) (M : Type -> Type) := New {
    command : forall (c : Effect.command E), M (Effect.answer E c);
    join : forall A B, M A -> M B -> M (A * B);
    choose : forall A, M A -> M A -> M A }.
  Arguments command {E M} _ _.
  Arguments join {E M} _ {A B} _ _.
  Arguments choose {E M} _ {A} _ _.
End EvalMonad.

Fixpoint monad {E : Effect.t} {A : Type} {M : Type -> Type} (m : Monad.t M)
  (eval : EvalMonad.t E M) (x : C.t E A) : M A :=
  match x with
  | C.Ret v => Monad.ret m v
  | C.Call c => EvalMonad.command eval c
  | C.Let x f =>
    Monad.bind m (monad m eval x) (fun x =>
    monad m eval (f x))
  | C.Join x y => EvalMonad.join eval (monad m eval x) (monad m eval y)
  | C.Choose x y => EvalMonad.choose eval (monad m eval x) (monad m eval y)
  end.

Module Handler.
  Definition t (E : Effect.t) (S : Type) (M : Type -> Type) : Type :=
    forall A (c : Effect.command E),
      S -> (Effect.answer E c -> S -> M A) -> M A.
End Handler.

Fixpoint algebraic {E S M A B} (h : Handler.t E S M) (x : C.t E A) (s : S)
  : (A -> S -> M B) -> M B :=
  match x with
  | C.Ret v => fun k => k v s
  | C.Call c => fun k => h _ c s k
  | C.Let x f => fun k =>
    (algebraic h x s) (fun v_x s =>
    algebraic h (f v_x) s k)
  | C.Join x y => fun k =>
    (algebraic h x s) (fun v_x s =>
    (algebraic h y s) (fun v_y s =>
    k (v_x, v_y) s))
  | C.Choose x _ => fun k => algebraic h x s k
  end.

Module I.
  Import C.I.Notations.

  CoFixpoint command {E1 E2 : Effect.t} {A : Type}
    (eval : forall (c : Effect.command E1), C.I.t E2 (Effect.answer E1 c))
    (x : C.I.t E1 A) : C.I.t E2 A :=
    match x with
    | C.I.Ret v => C.I.Ret v
    | C.I.Call c => eval c
    | C.I.Let x f =>
      C.I.Let (command eval x) (fun x => command eval (f x))
    | C.I.Join x y => C.I.Join (command eval x) (command eval y)
    | C.I.Choose x y => C.I.Choose (command eval x) (command eval y)
    end.

  CoFixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
    (eval : forall (c : Effect.command E1), C.I.t E2 (Effect.answer E1 c + Exc))
    (eval_join : Exc -> Exc -> Exc) (x : C.I.t E1 A) : C.I.t E2 (A + Exc) :=
    match x with
    | C.I.Ret v => iret (inl v)
    | C.I.Call c => eval c
    | C.I.Let x f =>
      ilet! x := exception eval eval_join x in
      match x with
      | inl x => exception eval eval_join (f x)
      | inr exc => iret (inr exc)
      end
    | C.I.Join x y =>
      ilet! xy :=
        ijoin (exception eval eval_join x) (exception eval eval_join y) in
      match xy with
      | (inl x, inl y) => iret (inl (x, y))
      | (inr exc, inl _) | (inl _, inr exc) => iret (inr exc)
      | (inr exc_x, inr exc_y) => iret (inr (eval_join exc_x exc_y))
      end
    | C.I.Choose x y =>
      ichoose (exception eval eval_join x) (exception eval eval_join y)
    end.

  CoFixpoint state {E1 E2 : Effect.t} {S A : Type}
    (eval : forall c, S -> C.I.t E2 (Effect.answer E1 c * S))
    (eval_join : S -> S -> S) (x : C.I.t E1 A) (s : S) : C.I.t E2 (A * S) :=
    match x with
    | C.I.Ret v => iret (v, s)
    | C.I.Call c => eval c s
    | C.I.Let x f =>
      ilet! x := state eval eval_join x s in
      let (v_x, s) := x in
      state eval eval_join (f v_x) s
    | C.I.Join x y =>
      ilet! xy :=
        ijoin (state eval eval_join x s) (state eval eval_join y s) in
      match xy with
      | ((v_x, s_x), (v_y, s_y)) => iret ((v_x, v_y), eval_join s_x s_y)
      end
    | C.I.Choose x y =>
      ichoose (state eval eval_join x s) (state eval eval_join y s)
    end.
End I.

Module Run.
  Fixpoint command {E1 E2 : Effect.t} {A : Type}
    {eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c)}
    (run : forall c (a : Effect.answer E1 c), Run.t (eval c) a)
    {x : C.t E1 A} {v : A} (r : Run.t x v) : Run.t (command eval x) v.
    destruct r; simpl.
    - apply Run.Ret.
    - apply run.
    - eapply Run.Let. apply (command _ _ _ _ run _ _ r1).
      apply (command _ _ _ _ run _ _ r2).
    - apply Run.ChooseLeft.
      apply (command _ _ _ _ run _ _ r).
    - apply Run.ChooseRight.
      apply (command _ _ _ _ run _ _ r).
    - apply Run.Join.
      + apply (command _ _ _ _ run _ _ r1).
      + apply (command _ _ _ _ run _ _ r2).
  Defined.

  Fixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
    {eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c + Exc)}
    {eval_join : Exc -> Exc -> Exc}
    (run : forall c (a : Effect.answer E1 c), Run.t (eval c) (inl a))
    {x : C.t E1 A} {v : A} (r : Run.t x v)
    : Run.t (exception eval eval_join x) (inl v).
    destruct r; simpl.
    - apply Run.Ret.
    - apply run.
    - eapply Run.Let. apply (exception _ _ _ _ _ _ run _ _ r1).
      apply (exception _ _ _ _ _ _ run _ _ r2).
    - apply Run.ChooseLeft.
      apply (exception _ _ _ _ _ _ run _ _ r).
    - apply Run.ChooseRight.
      apply (exception _ _ _ _ _ _ run _ _ r).
    - eapply Run.Let.
      + eapply Run.Join.
        * apply (exception _ _ _ _ _ _ run _ _ r1).
        * apply (exception _ _ _ _ _ _ run _ _ r2).
      + apply Run.Ret.
  Defined.

  Module I.
    CoFixpoint command {E1 E2 : Effect.t} {A : Type}
      {eval : forall (c : Effect.command E1), C.I.t E2 (Effect.answer E1 c)}
      (run : forall c (a : Effect.answer E1 c), Run.I.t (eval c) a)
      {x : C.I.t E1 A} {v : A} (r : Run.I.t x v) : Run.I.t (I.command eval x) v.
      rewrite (C.I.unfold_eq (I.command _ _)).
      destruct r; simpl.
      - apply Run.I.Ret.
      - assert (r := run c answer).
        rewrite (C.I.unfold_eq (eval _)) in r.
        exact r.
      - eapply Run.I.Let. apply (command _ _ _ _ run _ _ r1).
        apply (command _ _ _ _ run _ _ r2).
      - apply Run.I.ChooseLeft.
        apply (command _ _ _ _ run _ _ r).
      - apply Run.I.ChooseRight.
        apply (command _ _ _ _ run _ _ r).
      - apply Run.I.Join.
        + apply (command _ _ _ _ run _ _ r1).
        + apply (command _ _ _ _ run _ _ r2).
    Defined.
  End I.
End Run.
