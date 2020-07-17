
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Notations.

Class Functor (F: Type -> Type) : Type :=
  { fmap : forall {x} {y}, (x->y) -> (F x->F y)
  ; fmap_id : forall x, @fmap x x id = id
  ; fmap_compose : forall {x} {y} {z} (f: y->z) (g: x->y)
                     , fmap (compose f g) = compose (fmap f) (fmap g)
  }.

Definition parallel {a} {b} {c} {d} (f: a->c) (g: b->d)
  : (a*b) -> (c*d) := fun xy => match xy with
                                | (x,y) => (f x, g y)
                                end.

Notation "f *** g" := (parallel f g) (at level 40, left associativity).

Definition rassoc {a} {b} {c} : ((a*b)*c) -> (a*(b*c))
    := fun xyz => match xyz with | ((x,y),z) => (x,(y,z)) end.

Class Monoidal F `{Functor F} : Type :=
  { unit : F unit
  ; fzip : forall {a} {b}, F a -> F b -> F (a*b)
  ; left_identity : forall {a} (v: F a)
           , fzip unit v = fmap (fun vv => (tt, vv)) v
  ; right_identity : forall {a} (v: F a)
           , fzip v unit = fmap (fun vv => (vv, tt)) v
  ; associativity : forall {a} {b} {c} (u: F a) (v: F b) (w: F c)
           , fzip u (fzip v w) = fmap rassoc (fzip (fzip u v) w)
  ; naturality : forall {a} {b} {c} {d}
                        (g: a->c) (h: b->d) (u: F a) (v: F b)
           , fmap (g***h) (fzip u v) = fzip (fmap g u) (fmap h v)
  }.

Notation "u ** v" := (fzip u v) (at level 40, left associativity).


Class Applicative F `{Functor F} : Type :=
  { pure : forall {a}, a -> F a
  ; app : forall {a} {b}, F (a->b) -> F a -> F b
  ; identity : forall {a} (v: F a)
              , app (pure id) v = v
  ; homomorphism : forall {a} {b} (f: a->b) (x: a)
              , app (pure f) (pure x) = pure (f x)
  ; interchange : forall {a} {b} (u: F (a->b)) (y: a)
              , app u (pure y) = app (pure (fun f=>f y)) u
  ; composition : forall {a} {b} {c}
                         (u: F (b->c)) (v: F (a->b)) (w: F a)
              , app u (app v w) = app (app (app (pure compose) u) v) w
  }.

Notation "fs <*> xs" := (app fs xs) (at level 40, left associativity).

