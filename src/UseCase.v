Require Import Coq.Logic.JMeq.
Require C.
Require Run.

Record t {E A} (x : C.t E A) : Type := New {
  P : Type;
  v : P -> A;
  r : forall p, Run.t x (v p) }.
Arguments New {E A x} _ _ _.
Arguments P {E A x} _.
Arguments v {E A x} _ _.
Arguments r {E A x} _ _.

Module Generalize.
  Definition t {E A} {x : C.t E A} (u1 u2 : UseCase.t x) : Prop :=
    forall (p2 : P u2), exists (p1 : P u1), JMeq (r u1 p1) (r u2 p2).
End Generalize.

Fixpoint general {E A} (x : C.t E A) : UseCase.t x.
  destruct x as [A v | c | A B x f | A x1 x2 | A B x y].
  - refine (UseCase.New unit (fun _ => v) (fun _ => _)).
    apply Run.Ret.
  - refine (UseCase.New (Effect.answer E c) (fun a => a) (fun a => _)).
    apply (Run.Call c a).
  - destruct (general _ _ x) as [P_x v_x r_x].
    refine (let g_f := fun v_x => general _ _ (f v_x) in _).
    refine (
      UseCase.New {p_x : P_x & UseCase.P (g_f (v_x p_x))}
        (fun p =>
          let (p_x, p_f) := p in
          UseCase.v (g_f (v_x p_x)) p_f)
        (fun p => _)).
    destruct p as [p_x p_f].
    apply (Run.Let (r_x p_x) (UseCase.r (g_f (v_x p_x)) p_f)).
  - destruct (general _ _ x1) as [P1 v1 r1].
    destruct (general _ _ x2) as [P2 v2 r2].
    refine (
      UseCase.New (P1 + P2)
        (fun p =>
          match p with
          | inl p1 => v1 p1
          | inr p2 => v2 p2
          end)
        (fun p => _)).
    destruct p as [p1 | p2].
    + apply (Run.ChooseLeft (r1 p1)).
    + apply (Run.ChooseRight (r2 p2)).
  - destruct (general _ _ x) as [P_x v_x r_x].
    destruct (general _ _ y) as [P_y v_y r_y].
    refine (
      UseCase.New (P_x * P_y)
        (fun p =>
          let (p_x, p_y) := p in
          (v_x p_x, v_y p_y))
        (fun p => _)).
    destruct p as [p_x p_y].
    apply (Run.Join (r_x p_x) (r_y p_y)).
Defined.

Module I.
  Record t {E A} (x : C.I.t E A) : Type := New {
    P : Type;
    v : P -> A;
    r : forall p, Run.I.t x (v p) }.
  Arguments New {E A x} _ _ _.
  Arguments P {E A x} _.
  Arguments v {E A x} _ _.
  Arguments r {E A x} _ _.

  Module Generalize.
    Definition t {E A} {x : C.I.t E A} (u1 u2 : UseCase.I.t x) : Prop :=
      forall (p2 : P u2), exists (p1 : P u1), Run.I.Eq.t (r u1 p1) (r u2 p2).
  End Generalize.
End I.
