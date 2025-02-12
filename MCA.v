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

Equations eval {M : Monad} {mas : MAS M} (e : exp 0) : M code :=
eval (cst c) := ret c;
eval (eapp e e') := bind (eval e) (fun cf => bind (eval e') (fun ca => mapp cf ca)).

Class MCA (M : Monad) (mas : MAS M) :=
{
  lam n : exp (S n) -> code;

  lam_S n (e : exp (S (S n))) c : mapp (lam e) c = ret (lam (subs e c));
  lam_O (e : exp 1) c : mapp (lam e) c = eval (subs e c);
}.

Arguments lam {_ _ _} _ _.



(* Evidenced Frames *)

Class EF : Type :=
{
  prop : Type;
  evid : Type;
  erel : prop -> evid -> prop -> Prop;

  top : prop;
  conj : prop -> prop -> prop;
  uimp : prop -> (prop -> Prop) -> prop;

  eid : evid;
  eseq : evid -> evid -> evid;
  etop : evid;
  epair : evid -> evid -> evid;
  efst : evid;
  esnd : evid;
  elam : evid -> evid;
  erho : evid -> evid;

  ef_refl phi : erel phi eid phi;
  ef_trans phi1 phi2 phi3 e e' : erel phi1 e phi2 -> erel phi2 e' phi3 -> erel phi1 (eseq e e') phi3;
  ef_top phi : erel phi etop top;
  ef_pair phi psi psi' e e' : erel phi e psi -> erel phi e' psi' -> erel phi (epair e e') (conj psi psi');
  ef_fst phi psi : erel (conj phi psi) efst phi;
  ef_snd phi psi : erel (conj phi psi) esnd psi;
  ef_curry phi phi' P e : (forall psi, P psi -> erel (conj phi phi') e psi) -> erel phi (elam e) (uimp phi' P);
  ef_uncurry phi phi' P e psi : erel phi (elam e) (uimp phi' P) -> P psi -> erel (conj phi phi') (erho e) psi;
}.



(* M-Modalities *)

Class MMod (M : Monad) (mas : MAS M) (mca : MCA mas) : Type :=
{
  Omega : Type;
  hrel : Omega -> Omega -> Prop;
  htop : Omega;
  hmeet : Omega -> Omega -> Omega;
  himp : Omega -> Omega -> Omega;
  hinf : (Omega -> Prop) -> Omega;

  after A : M A -> (A -> Omega) -> Omega;

  ax_refl x : hrel x x;
  ax_trans x y z : hrel x y -> hrel y z -> hrel x z;
  ax_top x : hrel x htop;
  ax_meet1 x y : hrel (hmeet x y) x;
  ax_meet2 x y : hrel (hmeet x y) y;
  ax_meet x y z : hrel z x -> hrel z y -> hrel z (hmeet x y);
  ax_imp x y z : hrel (hmeet x y) z <-> hrel x (himp y z);
  ax_inf P x : (forall y, P y -> hrel x y) <-> hrel x (hinf P);

  ax_ret A x (phi : A -> Omega) : hrel (phi x) (after (ret x) phi);
  ax_bind A B (f : A -> M B) phi m : hrel (after m (fun x => after (f x) phi)) (after (bind m f) phi);
  ax_mono_ext A (phi psi : A -> Omega) m : (forall c, hrel (phi c) (psi c)) -> hrel (after m phi) (after m psi);
  ax_mono_meet A (phi : A -> Omega) m x : hrel (hmeet x (after m phi)) (after m (fun a => hmeet x (phi a)));
}.

Add Parametric Relation M (mas : MAS M) (mca : MCA mas) (mod : MMod mca) :
  Omega hrel
  reflexivity proved by ax_refl
  transitivity proved by ax_trans
  as hrel_instance.

Notation "x <= y" := (hrel x y).

Definition ihinf M (mas : MAS M) (mca : MCA mas) (mod : MMod mca) :
  forall I, (I -> Omega) -> Omega :=  
  fun I F => hinf (fun o => exists i, o = F i).

Definition ax_refl' M (mas : MAS M) (mca : MCA mas) (mod : MMod mca) x x' :
  x = x' -> x <= x'.
Proof.
  intros <-. apply ax_refl.
Qed.

Definition ax_meet_comm M (mas : MAS M) (mca : MCA mas) (mod : MMod mca) x y :
  hmeet x y <= hmeet y x.
Proof.
  apply ax_meet. apply ax_meet2. apply ax_meet1.
Qed.



(* Induced EF *)

Notation "$0" :=
  (var F1).

Notation "$1" :=
  (var (FS F1)).

Notation "$2" :=
  (var (FS (FS F1))).

Notation p1 :=
  (lam 1 $0).

Notation p2 :=
  (lam 1 $1).

Theorem MCA_EF M (mas : MAS M) (mca : MCA mas) (mod : MMod mca) : EF.
Proof.
  unshelve econstructor.
  - exact (code -> Omega).
  - exact code.
  - exact (fun P e P' => forall c, P c <= after (mapp e c) P').
  - exact (fun _ => htop).
  - intros P P' e. exact (hmeet (after (mapp e p1) P) (after (mapp e p2) P')).
  - intros P P' e. apply hinf. intros o.
    exact (exists c phi, P' phi /\ o = himp (P c) (after (mapp e c) phi)).
  - exact (lam 0 $0).
  - intros f g. exact (lam 0 (eapp (cst g) (eapp (cst f) $0))).
  - exact (lam 0 $0).
  - intros e e'. exact (lam 1 (eapp (eapp $1 (eapp (cst e) $0)) (eapp (cst e') $0))).
  - exact (lam 0 (eapp $0 (cst p1))).
  - exact (lam 0 (eapp $0 (cst p2))).
  - intros e. exact (lam 1 (eapp (cst e) (eapp (eapp (cst (lam 2 (eapp (eapp $2 $0) $1))) $0) $1))).
  - intros e. exact (lam 0 (eapp (eapp (cst e) (eapp $0 (cst p1))) (eapp $0 (cst p2)))).
  - cbn. intros phi c. rewrite lam_O. autorewrite with subs eval. apply ax_ret.
  - cbn. intros phi1 phi2 phi3 e e' H1 H2 c.
    rewrite !lam_O. autorewrite with subs eval.
    rewrite !lunit. rewrite <- ax_bind, H1.
    apply ax_mono_ext. apply H2.
  - cbn. intros phi c. rewrite lam_O.
    autorewrite with subs eval.
    rewrite <- ax_ret; eauto. apply ax_top.
  - cbn. intros phi psi psi' e e' H1 H2 c.
    assert (HC : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => hmeet (psi c1) (psi' c2)))).
    { rewrite <- ax_mono_ext. rewrite <- ax_mono_meet.
      apply ax_meet. apply H2. apply H1. intros m. cbn.
      rewrite ax_meet_comm. apply ax_mono_meet. }
    assert (HC1 : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => psi c1))).
    { rewrite HC. apply ax_mono_ext. intros m. apply ax_mono_ext. intros m'. apply ax_meet1. }
    assert (HC2 : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => psi' c2))).
    { rewrite HC. apply ax_mono_ext. intros m. apply ax_mono_ext. intros m'. apply ax_meet2. }
    rewrite !lam_S. autorewrite with subs eval. rewrite <- ax_ret.
    rewrite !lam_O. autorewrite with subs eval.
    rewrite !lunit, !assoc. apply ax_meet.
    + rewrite <- ax_bind. rewrite HC1. apply ax_mono_ext.
      intros x. rewrite !lam_S. autorewrite with subs eval. rewrite lunit.
      rewrite <- ax_bind. apply ax_mono_ext. intros m.
      rewrite lam_O. autorewrite with subs eval. apply ax_ret.
    + rewrite <- ax_bind. rewrite HC2. apply ax_mono_ext.
      intros x. rewrite !lam_S. autorewrite with subs eval. rewrite lunit.
      rewrite <- ax_bind. apply ax_mono_ext. intros m.
      rewrite lam_O. autorewrite with subs eval. apply ax_ret.
  - cbn. intros phi psi c.
    rewrite lam_O. autorewrite with subs eval.
    rewrite <- ax_bind, <- ax_ret, <- ax_bind, <- ax_ret.
    apply ax_meet1.
  - cbn. intros phi psi c.
    rewrite lam_O. autorewrite with subs eval.
    rewrite <- ax_bind, <- ax_ret, <- ax_bind, <- ax_ret.
    apply ax_meet2.
  - cbn. intros phi psi P c H c'.
    rewrite lam_S. autorewrite with subs eval.
    rewrite <- ax_ret. apply ax_inf.
    intros x (m & phi' & HP & ->).
    rewrite lam_O. autorewrite with subs eval.
    rewrite lunit. apply ax_imp. rewrite <- !ax_bind, <- ax_ret, <- ax_bind, <- ax_ret.
    rewrite lam_S. autorewrite with subs eval.
    rewrite <- ax_ret. rewrite lunit.
    rewrite lam_S. autorewrite with subs eval.
    rewrite <- ax_ret.
    rewrite <- H; trivial.
    rewrite !lam_O. autorewrite with subs eval. apply ax_meet.
    + rewrite <- !ax_bind, <- ax_ret, lunit.
      rewrite lam_S. autorewrite with subs eval.
      rewrite <- ax_ret, lunit.
      rewrite lam_O. autorewrite with subs eval.
      rewrite <- ax_ret. apply ax_meet1.
    + rewrite <- !ax_bind, <- ax_ret, lunit.
      rewrite lam_S. autorewrite with subs eval.
      rewrite <- ax_ret, lunit.
      rewrite lam_O. autorewrite with subs eval.
      rewrite <- ax_ret. apply ax_meet2.
  - cbn.
Qed.
