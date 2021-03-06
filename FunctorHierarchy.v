
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Notations.

Notation "f ∘ g" := (compose f g).

Class Functor (F: Type -> Type) : Type :=
  { fmap : forall {x} {y}, (x->y) -> (F x->F y)
  ; fmap_id : forall x, @fmap x x id = id
  ; fmap_compose : forall {x} {y} {z} (f: y->z) (g: x->y)
                     , fmap (f∘g) = fmap f ∘ fmap g
  }.

Lemma fmap_twice {F} `{Functor F} {x} {y} {z} (f: y->z) (g: x->y) (xs: F x)
                     : fmap (f∘g) xs = fmap f (fmap g xs).
Proof.
  rewrite fmap_compose. now compute.
Qed.

Definition parallel {a} {b} {c} {d} (f: a->c) (g: b->d)
  : (a*b) -> (c*d) := fun xy => match xy with
                                | (x,y) => (f x, g y)
                                end.

Notation "f *** g" := (parallel f g) (at level 40, left associativity).

Definition rassoc {a} {b} {c} : ((a*b)*c) -> (a*(b*c))
    := fun xyz => match xyz with | ((x,y),z) => (x,(y,z)) end.

Definition tt_ {a} (x:a) := (tt, x).
Definition _tt {a} (x:a) := (x, tt).

Class Monoidal F `{Functor F} : Type :=
  { funit : F unit
  ; fzip : forall {a} {b}, F a -> F b -> F (a*b)
  ; left_identity : forall {a} (v: F a)
           , fzip funit v = fmap tt_ v
  ; right_identity : forall {a} (v: F a)
           , fzip v funit = fmap _tt v
  ; associativity : forall {a} {b} {c} (u: F a) (v: F b) (w: F c)
           , fzip u (fzip v w) = fmap rassoc (fzip (fzip u v) w)
  ; naturality : forall {a} {b} {c} {d}
                        (g: a->c) (h: b->d) (u: F a) (v: F b)
           , fmap (g***h) (fzip u v) = fzip (fmap g u) (fmap h v)
  }.

Notation "u ** v" := (fzip u v) (at level 40, left associativity).

Lemma naturalityL {F} `{Monoidal F} {a} {b} {c}
                           (f: a->c) (u: F a) (v: F b)
           : fmap (f***id) (fzip u v) = fzip (fmap f u) v.
Proof.
  assert (v = fmap id v) as ->. { now rewrite fmap_id. }
  rewrite <- naturality.
  assert (v = fmap id v) as <-. { now rewrite fmap_id. }
  now trivial.
Qed.
Lemma naturalityR {F} `{Monoidal F} {a} {b} {c}
                           (f: b->c) (u: F a) (v: F b)
           : fmap (id***f) (fzip u v) = fzip u (fmap f v).
Proof.
  assert (u = fmap id u) as ->. { now rewrite fmap_id. }
  rewrite <- naturality.
  assert (u = fmap id u) as <-. { now rewrite fmap_id. }
  now trivial.
Qed.

Definition to {a} {b} (y: a) (f: a->b) := f y.

Class Applicative F `{Functor F} : Type :=
  { pure : forall {a}, a -> F a
  ; app : forall {a} {b}, F (a->b) -> F a -> F b
  ; identity : forall {a} (v: F a)
              , app (pure id) v = v
  ; homomorphism : forall {a} {b} (f: a->b) (x: a)
              , app (pure f) (pure x) = pure (f x)
  ; interchange : forall {a} {b} (u: F (a->b)) (y: a)
              , app u (pure y) = app (pure (to y)) u
  ; composition : forall {a} {b} {c}
                         (u: F (b->c)) (v: F (a->b)) (w: F a)
              , app u (app v w) = app (app (app (pure compose) u) v) w
  ; appFtor : forall {a} {b} (g: a->b) (x: F a)
              , fmap g x = app (pure g) x
  }.

Notation "fs <*> xs" := (app fs xs) (at level 40, left associativity).

Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.

Definition apl {a} {b} (fx: (a->b)*a)
   := match fx with |(f,x) => f x end.

Program Instance MonoidalIsApplicative {F} `{Monoidal F}
    : Applicative F
  := { pure := fun {a} (x: a) => fmap (const x) funit
     ; app := fun {a} {b} (fs: F (a->b)) (xs: F a)
              => fmap apl (fzip fs xs) }.
Next Obligation. (* identity *)
  rewrite <- naturalityL.
  rewrite -> left_identity.
  repeat (rewrite <- fmap_twice).
  rewrite -> fmap_id.
  now compute.
Qed.
Next Obligation. (* homomorphism *)
  rewrite <- naturality.
  rewrite -> left_identity.
  repeat (rewrite <- fmap_twice).
  now compute.
Qed.
Next Obligation. (* interchange *)
  rewrite <- naturalityL.
  rewrite <- naturalityR.
  repeat (rewrite <- fmap_twice).
  rewrite -> right_identity.
  rewrite -> left_identity.
  repeat (rewrite <- fmap_twice).
  now compute.
Qed.
Next Obligation. (* composition *)
  rewrite <- naturalityR.
  rewrite -> associativity.
  repeat (rewrite <- naturalityL).
  rewrite -> left_identity.
  repeat (rewrite <- naturalityL).
  repeat (rewrite <- fmap_twice).

  f_equal.                      (*    This part is just about *)
  unfold compose.                 (*  convincing Coq that two  *)
  apply functional_extensionality. (* functions are equal, it  *)
  intro x.                         (* has nothing to do with   *)
  destruct x as ((btc, atb), a0). (*  applicative or monoidal  *)
  now compute.                  (*    functors, specifically. *)
Qed.
Next Obligation. (* appFtor *)
  rewrite <- naturalityL.
  rewrite -> left_identity.
  repeat (rewrite <- fmap_twice).
  now compute.
Qed.


Lemma fmapPure {F} `{Applicative F} {a} {b}
        (f: a->b) (x: a) : fmap f (pure x: F a) = pure (f x).
Proof.
  rewrite -> appFtor.
  now apply homomorphism.
Qed.

Lemma fmapBracket {F} `{Applicative F} {a} {b} {c} {d}
      (f: c->d) (g: a->b->c) (xs: F a) (ys: F b)
     : fmap f (fmap g xs<*>ys) = fmap (fun x y => f (g x y)) xs <*> ys.
Proof.
  repeat (rewrite -> appFtor).
  rewrite -> composition.
  rewrite -> homomorphism.
  rewrite -> composition.
  repeat (rewrite -> homomorphism).
  now compute.
Qed.

Lemma fmap_both {F} `{Applicative F} {a} {b} {c} {d}
      (f: a->c->d) (g: b->c) (xs: F a) (ys: F b)
     : fmap f xs <*> fmap g ys = fmap (fun x y => f x (g y)) xs <*> ys.
Proof.
  repeat (rewrite -> appFtor).
  rewrite -> composition.
  repeat (rewrite <- appFtor).
  rewrite <- fmap_twice.
  rewrite -> interchange.
  rewrite -> appFtor.
  rewrite -> composition.
  repeat (rewrite -> homomorphism).
  rewrite <- appFtor.
  now compute.
Qed.

Definition tup {a} {b} (x:a) (y:b) : (a*b) := (x,y).

Program Instance ApplicativeIsMonoidal {F} `{Applicative F}
    : Monoidal F
  := { funit := pure tt
     ; fzip := fun {a} {b} (u: F a) (v: F b)
                   => fmap tup u <*> v }.
Next Obligation. (* left_identity *)
  repeat (rewrite -> appFtor).
  rewrite -> homomorphism.
  now compute.
Qed.
Next Obligation. (* right_identity *)
  repeat (rewrite -> appFtor).
  rewrite -> interchange.
  rewrite -> composition.
  repeat (rewrite -> homomorphism).
  now compute.
Qed.
Next Obligation. (* associativity *)
  repeat (rewrite -> fmapBracket).
  rewrite -> composition.
  repeat (rewrite <- appFtor).
  rewrite <- fmap_twice.
  rewrite -> fmap_both.
  now compute.
Qed.
Next Obligation. (* naturality *)
  rewrite -> fmap_both.
  rewrite <- fmap_twice.
  rewrite -> fmapBracket.
  now compute.
Qed.

