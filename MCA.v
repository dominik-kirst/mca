Set Implicit Arguments.
Unset Strict Implicit.

Require Import Fin.
From Equations.Prop Require Import Equations.



(* Monads *)

Class Monad :=
{ 
  M : Type -> Type;
  ret {A} : A -> M A;
  bind {A B} : M A -> (A -> M B) -> M B;
        
  runit A (m : M A) : bind m ret = m;
  lunit A B (f: A -> M B) x : bind (ret x) f = f x;
  assoc A B C (f : A -> M B) (g : B -> M C) m : bind (bind m f) g = bind m (fun n => bind (f n) g);
}.

Coercion M : Monad >-> Funclass.



(* MCAs *)

Class MAS (M : Monad) :=
{
  code : Type;
  mapp : code -> code -> M code;
}.

Inductive exp {M : Monad} {mas : MAS M} n : Type :=
| var : Fin.t n -> exp n
| cst : code -> exp n
| eapp : exp n -> exp n -> exp n.

Arguments cst {_ _ _} _.

Equations subs {M : Monad} {mas : MAS M} {n} (e : exp (S n)) (c : code) : exp n :=
subs (var F1) c := cst c;
subs (var (FS x)) c := var x;
subs (cst c') c := cst c';
subs (eapp e e') c := eapp (subs e c) (subs e' c).

(*Fixpoint fin n : Type :=
  match n with 0 => False | S n => option (fin n) end.

Inductive exp {M : Monad} {mas : MAS M} : nat -> Type :=
| var n : fin n -> exp n
| cst {n} : code -> exp n
| eapp n : exp n -> exp n -> exp n.

Equations subs {M : Monad} {mas : MAS M} n (e : exp (S n)) (c : code) : exp n :=
subs (var None) c := cst c;
subs (var (Some x)) c := var x;
subs (cst c') c := cst c';
subs (eapp e e') c := eapp (subs e c) (subs e' c).*)

Equations eval {M : Monad} {mas : MAS M} (e : exp 0) : M code :=
eval (cst c) := ret c;
eval (eapp e e') := bind (eval e) (fun cf => bind (eval e') (fun ca => mapp cf ca)).

Class MCA (M : Monad) :=
{
  mca_mas : MAS M;
  lam n : exp (S n) -> code;

  lam_S n (e : exp (S (S n))) c : mapp (lam e) c = ret (lam (subs e c));
  lam_O (e : exp 1) c : mapp (lam e) c = eval (subs e c);
}.



(* PCAs *)

Definition subsingleton A :=
  { P : A -> Prop | forall x y, P x -> P y -> x = y }.

Lemma subsingleton_eq A (P Q : subsingleton A) :
  (forall x, proj1_sig P x <-> proj1_sig Q x) -> P = Q.
Proof.
Admitted.

Definition partiality_monad : Monad.
Proof.
  unshelve eapply (Build_Monad (M := subsingleton)).
  - intros A x. exists (eq x). intros y y' ->. tauto.
  - intros A B [P HP] F. exists (fun b => exists a, P a /\ proj1_sig (F a) b).
    intros x y [a [H1 H2]] [a' [H3 H4]]. apply (HP a a') in H1 as <-; trivial.
    destruct (F a) as [Q HQ]. cbn in *. now apply HQ.
  - intros A [P HP]. cbn. apply subsingleton_eq. cbn.
    intros x. split; eauto. intros [y [H ->]]. assumption.
  - intros A B f x. apply subsingleton_eq. cbn.
    intros y. split; eauto. intros [z [-> H]]. assumption.
  - intros A B C f g [P HP]. apply subsingleton_eq. cbn.
    intros c. split.
    + intros (b & (a & H1 & H2) & H3). exists a. split; trivial.
      destruct (f a) as [Q HQ]. cbn in *. now exists b.
    + intros (a & H1 & H2). destruct (f a) as [Q HQ] eqn: He. cbn in H2.
      destruct H2 as (b & H3 & H4). exists b. split; trivial.
      exists a. rewrite He. cbn. split; trivial.
Defined.



