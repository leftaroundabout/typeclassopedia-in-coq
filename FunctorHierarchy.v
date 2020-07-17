
Require Import Coq.Program.Basics.

(* The Coq standard `id` takes the type as an explicit argument. *)
Definition id {a: Type} : a->a := fun x => x.

Class Functor (F: Type -> Type) : Type :=
  { fmap : forall {x} {y}, (x->y) -> (F x->F y)
  ; fmap_id : forall x, @fmap x x id = id
  ; fmap_compose : forall {x} {y} {z} (f: y->z) (g: x->y)
                     , fmap (compose f g) = compose (fmap f) (fmap g)
  }.





