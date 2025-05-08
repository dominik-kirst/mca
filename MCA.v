Set Implicit Arguments.
Unset Strict Implicit.

Require Import Lia Fin.
From Equations.Prop Require Import Equations.

(* Axiom!!! *)
Require Import Coq.Logic.FunctionalExtensionality.


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


(* SK Definition *)

Section SK.

  Context {M : Monad}.
  Context {mas : MAS M}.
  
  Context {Scode : code}.
  Context {Scode1 : code -> code}.
  Context {Scode2 : code -> code -> code}.
  Context {Kcode : code}.
  Context {Kcode1 : code -> code}.

  Context {appS : forall a0,
    mapp Scode a0
    = ret (Scode1 a0)}.

  Context {appS1 : forall a0 a1,
    mapp (Scode1 a0) a1
    = ret (Scode2 a0 a1)}.
  
  Context {appS2 : forall a0 a1 b,
    mapp (Scode2 a0 a1) b
    = bind (mapp a0 b) (fun f =>
      bind (mapp a1 b) (fun r =>
      mapp f r
    ))
    }.
  
  Context {appK : forall a,
    mapp Kcode a = ret (Kcode1 a)}.
  
  Context {appK1 : forall a b,
    mapp (Kcode1 a) b = ret a}.

  Definition Icode :=
    Scode2 Kcode Kcode.
  
  Definition Bcode1 :=
    fun a0 => Scode1 (Kcode1 a0).
  
  Definition Bcode2 :=
    fun a0 a1 => Scode2 (Kcode1 a0) a1.
  
  (* Goldberg's n-ary K *)

  Fixpoint Kncode (n : nat) : code :=
    match n with
    | O => Icode
    | S O => Kcode
    | S n => Bcode2 Kcode (Kncode n)
    end.

  Fixpoint Kncode1 (n : nat) (c : code) : code :=
    match n with
    | O => c
    | S O => Kcode1 c
    | S n => Kcode1 (Kncode1 n c)
    end.
  
  (* Goldberg's n-ary S *)

  Fixpoint Sncode (n : nat) : code :=
    match n with
    | O => Icode
    | S O => Scode
    | S n => Bcode2 Scode (Bcode1 (Sncode n))
    end.

  Definition Sncode2 (n : nat) (c0 c1 : code) : code :=
    match n with
    | O => Scode2 c0 c1
    | S n => Scode2 (Bcode2 (Sncode (S n)) c0) c1
    end.
  
  (* Bracket Abstraction *)

  Fixpoint size {n} (e : exp n) : nat :=
    match e with
    | var x => proj1_sig (to_nat x)
    | cst x => 42
    | eapp e e' => 1 + (size e) + size e'
    end.

  Equations? abs {n} (e : exp (S n)) : code by wf (size e) lt :=
    abs (var F1) :=
      Kncode n;
    abs (var (FS F1)) :=
      Kcode1 (abs (var F1));
    abs (var (FS (FS x))) :=
      Kcode1 (abs (var (FS x)));
    abs (cst c) :=
      Kncode1 (S n) c;
    abs (eapp e1 e2) :=
      Sncode2 n (abs e1) (abs e2).
  Proof.
    all: try lia.
    - exact 82.
    - cbn. destruct (to_nat x) as [n Hn]. cbn. lia.
  Qed.

  Ltac simpl_monad :=
    progress repeat (rewrite ?lunit, ?assoc).

  Derive Signature for t.

  Instance skmca : MCA mas.
  Proof.
    assert (LKn : forall n,
      Kncode (S (S n))
      = Bcode2 Kcode (Kncode (S n))).
    { intro n. simpl. reflexivity. }
    assert (LKn1 : forall c n,
      Kncode1 (S (S n)) c
      = Kcode1 (Kncode1 (S n) c)).
    { intro n. simpl. reflexivity. }
    split with (lam := @abs).
  - intros n e c. induction e as [ x | c' | e1 Ih1 e2 Ih2 ].
    * depelim x; simp subs; simp abs.
      induction n as [|n IHn].
        { simpl. rewrite appK. reflexivity. }
        { rewrite LKn. unfold Bcode2.
          rewrite appS2. rewrite appK1.
          simpl_monad. rewrite IHn.
          simpl_monad. rewrite appK.
          rewrite LKn1. reflexivity. }
      depelim x.
        { simp abs. (* What is abs_obligation_1?!?! *)
          (* ERROR!!!!!!!!! *)
        }
        
    * simp subs. simp abs.
    * simp subs. simp abs. induction n as [| n' Ihn ]; simpl.
      + unfold Bcode2. rewrite appS2.
        rewrite appS2.    simpl_monad.
        rewrite appK1.    simpl_monad.
        rewrite Ih1.      simpl_monad.
        rewrite appS.     simpl_monad.
        rewrite Ih2.      simpl_monad.
        rewrite appS1.    reflexivity.
      + unfold Bcode2. rewrite appS2.
        rewrite appS2.    simpl_monad.
        rewrite appK1.    simpl_monad.
        rewrite Ih1.      simpl_monad.
        rewrite appS2.    simpl_monad.
        rewrite appK1.    simpl_monad.
        unfold Bcode1.
        rewrite appS1.    simpl_monad.
        rewrite appS.     simpl_monad.
        rewrite Ih2.      simpl_monad.
        rewrite appS1. reflexivity.
  - intros e c. induction e as [ x | c' | e1 Ih1 e2 Ih2 ].
    * admit. (* TODO: prove for variables *)
    * simp subs. simp abs.
    * simp subs. simp abs.
      unfold Sncode2. rewrite appS2.
      rewrite Ih1. simp eval.
      rewrite Ih2. reflexivity.
  Admitted.

End SK.


(* Evidenced Frames *)

Class EF : Type :=
{
  prop : Type;
  evid : Type;
  erel : prop -> evid -> prop -> Prop;

  top : prop;
  bot : prop;
  conj : prop -> prop -> prop;
  uimp : prop -> (prop -> Prop) -> prop;

  eid : evid;
  eseq : evid -> evid -> evid;
  etop : evid;
  ebot : evid;
  epair : evid -> evid -> evid;
  efst : evid;
  esnd : evid;
  elam : evid -> evid;
  erho : evid -> evid;

  ef_refl phi : erel phi eid phi;
  ef_trans phi1 phi2 phi3 e e' : erel phi1 e phi2 -> erel phi2 e' phi3 -> erel phi1 (eseq e e') phi3;
  ef_top phi : erel phi etop top;
  ef_bot phi : erel bot ebot phi;
  ef_pair phi psi psi' e e' : erel phi e psi -> erel phi e' psi' -> erel phi (epair e e') (conj psi psi');
  ef_fst phi psi : erel (conj phi psi) efst phi;
  ef_snd phi psi : erel (conj phi psi) esnd psi;
  ef_curry phi phi' P e : (forall psi, P psi -> erel (conj phi phi') e psi) -> erel phi (elam e) (uimp phi' P);
  ef_uncurry phi phi' P e psi : erel phi e (uimp phi' P) -> P psi -> erel (conj phi phi') (erho e) psi;
}.



(* M-Modalities *)

Class MMod (M : Monad) (mas : MAS M) : Type :=
{
  Omega : Type;
  hrel : Omega -> Omega -> Prop;
  htop : Omega;
  hbot : Omega;
  hmeet : Omega -> Omega -> Omega;
  himp : Omega -> Omega -> Omega;
  hinf : (Omega -> Prop) -> Omega;

  after A : M A -> (A -> Omega) -> Omega;

  ax_refl x : hrel x x;
  ax_trans x y z : hrel x y -> hrel y z -> hrel x z;
  ax_top x : hrel x htop;
  ax_bot x : hrel hbot x;
  ax_meet1 x y : hrel (hmeet x y) x;
  ax_meet2 x y : hrel (hmeet x y) y;
  ax_meet x y z : hrel z x -> hrel z y -> hrel z (hmeet x y);
  ax_imp x y z : hrel (hmeet x y) z <-> hrel x (himp y z);
  ax_inf P x : (forall y, P y -> hrel x y) <-> hrel x (hinf P);

  ax_ret A x (phi : A -> Omega) : hrel (phi x) (after (ret x) phi);
  ax_bind A B (f : A -> M B) phi m : hrel (after m (fun x => after (f x) phi)) (after (bind m f) phi);
  ax_mono (phi psi : code -> Omega) m : hrel (hinf (fun x => exists c, x = himp (phi c) (psi c))) (himp (after m phi) (after m psi));
}.

Add Parametric Relation M (mas : MAS M) (mod : MMod mas) :
  Omega hrel
  reflexivity proved by ax_refl
  transitivity proved by ax_trans
  as hrel_instance.

Notation "x <= y" := (hrel x y).

Section MMod.

  Context {M : Monad}.
  Context {mas : MAS M}.
  Context {mod : MMod mas }.

  Lemma ax_refl' x x' :
    x = x' -> x <= x'.
  Proof.
    intros <-. apply ax_refl.
  Qed.

  Lemma ax_meet_comm x y :
    hmeet x y <= hmeet y x.
  Proof.
    apply ax_meet. apply ax_meet2. apply ax_meet1.
  Qed.

  Lemma ax_inf' P x :
    P x -> hinf P <= x.
  Proof.
    intros H. apply <- ax_inf; eauto. reflexivity.
  Qed.

  Lemma imp_right x y y' :
    y <= y' -> himp x y <= himp x y'.
  Proof.
    intros H. apply ax_imp. rewrite <- H. apply ax_imp. reflexivity.
  Qed.

  Lemma ax_mono_ext' (phi psi : code -> Omega) m x :
    (forall c, hmeet x (phi c) <= psi c) -> hmeet x (after m phi) <= after m psi.
  Proof.
    intros H. apply ax_imp. rewrite <- ax_mono.
    apply ax_inf. intros y [c ->]. apply ax_imp, H.
  Qed.

  Lemma ax_mono_ext (phi psi : code -> Omega) m :
    (forall c, phi c <= psi c) -> after m phi <= after m psi.
  Proof.
    intros H. erewrite <- (@ax_mono_ext' phi psi m htop).
    - apply ax_meet; try reflexivity. apply ax_top.
    - intros c. rewrite ax_meet2. apply H.
  Qed.

  Lemma ax_mono_meet (phi : code -> Omega) m x :
    hmeet x (after m phi) <= after m (fun a => hmeet x (phi a)).
  Proof.
    apply ax_mono_ext'. reflexivity.
  Qed.

  Lemma ax_mono_imp (phi : code -> Omega) m x :
    after m (fun a => himp x (phi a)) <= himp x (after m phi).
  Proof.
    apply ax_imp. rewrite ax_meet_comm. apply ax_mono_ext'.
    intros c. rewrite ax_meet_comm. apply ax_imp. reflexivity.
  Qed.

End MMod.



(* Separators *)

Section Sep.

  Context {M : Monad}.
  Context {mas : MAS M}.
  Context {mca : MCA mas}.
  Context {mod : MMod mas }.

  Variable sep : code -> Prop.

  Fixpoint subexp n (e : exp n) :=
    match e with
    | var x => True
    | cst c => sep c
    | eapp e e' => subexp e /\ subexp e'
    end.

  Definition ccomplete :=
    forall n (e : exp (S n)), subexp e -> sep (lam n e).

  Definition progress :=
    forall c c', sep c -> sep c' -> after (mapp c c') (fun _ => hbot) <= hbot.

End Sep.

Class subcode M (mas : MAS M) (Sep : code -> Prop) :=
  {
    elem : code;
    elem_proof : Sep elem;
  }.

Coercion elem : subcode >-> code.

Class separator (M : Monad) (mas : MAS M) (mca : MCA mas) (mod : MMod mas) : Type :=
  {
    subset : code -> Prop;
    Sep1 : ccomplete subset;
    Sep2 : progress subset;
  }.

Coercion subset : separator >-> Funclass.



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

Ltac simpl_mca :=
  progress repeat (rewrite ?lam_S, ?lam_O; autorewrite with subs eval; rewrite ?lunit, ?runit).

Instance MCA_EF M (mas : MAS M) (mca : MCA mas) (mod : MMod mas) (sep : separator mca mod) : EF.
Proof.
  unshelve econstructor.

  (* base types *)
  - exact (code -> Omega).
  - exact (subcode sep).

  (* propositional operations *)
  - exact (fun phi e psi => forall c, phi c <= after (mapp e c) psi).
  - exact (fun _ => htop).
  - exact (fun _ => hbot).
  - intros phi psi e. exact (hmeet (after (mapp e p1) phi) (after (mapp e p2) psi)).
  - intros phi P e. apply hinf. intros o.
    exact (exists psi, P psi /\ o = hinf (fun x => exists c, x = himp (phi c) (after (mapp e c) psi))).
  
  (* evidences *)
  - exists (lam 0 $0). apply Sep1. cbn. tauto.
  - intros f g. exists (lam 0 (eapp (cst g) (eapp (cst f) $0))). apply Sep1. cbn. intuition.
  - exists (lam 0 $0). apply Sep1. cbn. tauto.
  - exists (lam 0 $0). apply Sep1. cbn. tauto.
  - intros e e'. exists (lam 1 (eapp (eapp $1 (eapp (cst e) $0)) (eapp (cst e') $0))).
    apply Sep1. cbn. intuition.
  - exists (lam 0 (eapp $0 (cst p1))). apply Sep1. cbn. intuition. apply Sep1. cbn. tauto.
  - exists (lam 0 (eapp $0 (cst p2))). apply Sep1. cbn. intuition. apply Sep1. cbn. tauto.
  - intros e. exists (lam 1 (eapp (cst e) (eapp (eapp (cst (lam 2 (eapp (eapp $2 $0) $1))) $0) $1))).
    apply Sep1. cbn. intuition. apply Sep1. cbn. tauto.
  - intros e. exists (lam 0 (eapp (eapp (cst e) (eapp $0 (cst p1))) (eapp $0 (cst p2)))).
    apply Sep1. cbn. intuition; apply Sep1; cbn; tauto.

  (* proofs *)
  - cbn. intros phi c. simpl_mca. apply ax_ret.
  - cbn. intros phi1 phi2 phi3 e e' H1 H2 c. simpl_mca.
    rewrite <- ax_bind, H1. apply ax_mono_ext. apply H2.
  - cbn. intros phi c. simpl_mca.
    rewrite <- ax_ret; eauto. apply ax_top.
  - cbn. intros phi c. simpl_mca.
    rewrite <- ax_ret; eauto. apply ax_bot.
  - cbn. intros phi psi psi' e e' H1 H2 c.
    assert (HC : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => hmeet (psi c1) (psi' c2)))).
    { rewrite <- ax_mono_ext. rewrite <- ax_mono_meet.
      apply ax_meet. apply H2. apply H1. intros m. cbn.
      rewrite ax_meet_comm. apply ax_mono_meet. }
    assert (HC1 : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => psi c1))).
    { rewrite HC. apply ax_mono_ext. intros m. apply ax_mono_ext. intros m'. apply ax_meet1. }
    assert (HC2 : phi c <= after (mapp e c) (fun c1 => after (mapp e' c) (fun c2 => psi' c2))).
    { rewrite HC. apply ax_mono_ext. intros m. apply ax_mono_ext. intros m'. apply ax_meet2. }
    simpl_mca. rewrite <- ax_ret. simpl_mca. rewrite !assoc. apply ax_meet.
    + rewrite <- ax_bind. rewrite HC1. apply ax_mono_ext.
      intros x. simpl_mca. rewrite <- ax_bind. apply ax_mono_ext.
      intros m. simpl_mca. apply ax_ret.
    + rewrite <- ax_bind. rewrite HC2. apply ax_mono_ext.
      intros x. simpl_mca. rewrite <- ax_bind. apply ax_mono_ext.
      intros m. simpl_mca. apply ax_ret.
  - cbn. intros phi psi c. simpl_mca. apply ax_meet1.
  - cbn. intros phi psi c. simpl_mca. apply ax_meet2.
  - cbn. intros phi psi P c H c'. simpl_mca.
    rewrite <- ax_ret. apply ax_inf.
    intros x (phi' & HP & ->). apply ax_inf. intros y (m & ->).
    simpl_mca. apply ax_imp. rewrite <- H; trivial. simpl_mca. apply ax_meet.
    + rewrite <- ax_ret. apply ax_meet1.
    + rewrite <- ax_ret. apply ax_meet2.
  - cbn. intros phi phi' P e psi H HP c.
    simpl_mca. rewrite <- !ax_bind. cbn.
    rewrite ax_meet_comm, ax_imp, <- ax_mono.
    apply ax_inf. intros m [c1 ->].
    rewrite <- ax_imp, ax_meet_comm, ax_imp, <- ax_mono_imp, H.
    erewrite ax_mono_ext.
    2: { intros c2. apply ax_inf'. exists psi. split; trivial. reflexivity. }
    erewrite ax_mono_ext.
    2: { intros c2. apply (ax_mono _ _ (mapp c p2)). }
    apply ax_mono_ext.
    intros c2. apply imp_right. apply ax_bind.
Defined.

Print Assumptions MCA_EF.

Lemma agreement M (mas : MAS M) (mca : MCA mas) (mod : MMod mas) (sep : separator mca mod) :
  (htop <= hbot) <-> exists e, erel top e bot.
Proof.
  split; intros H.
  - exists eid. cbn. intros c. simpl_mca. rewrite <- ax_ret. apply H.
  - destruct H as [e H]. cbn in H. rewrite (H e). apply Sep2; intuition.
Qed.



(* Axioms *)

Axiom PE : forall (P P' : Prop), P <-> P' -> P = P'.

Axiom FE : forall X Y (f g : X -> Y), (forall x, f x = g x) -> f = g.

Lemma PI (P : Prop) (H H' : P) :
  H = H'.
Proof.
  assert (P = True) as ->.
  - apply PE. tauto.
  - destruct H, H'. reflexivity.
Qed.

Lemma CE X (P P' : X -> Prop) :
  (forall x, P x <-> P' x) -> P = P'.
Proof.
  intros H. apply FE. intros x. apply PE. apply H.
Qed.



(* PCA *)

Definition subsingleton A :=
  { P : A -> Prop | forall x y, P x -> P y -> x = y }.

Lemma subsingleton_eq A (P Q : subsingleton A) :
  (forall x, proj1_sig P x <-> proj1_sig Q x) -> P = Q.
Proof.
  intros H. destruct P as [P HP], Q as [Q HQ]; cbn in H.
  assert (HPQ : P = Q) by now apply CE.
  destruct HPQ. f_equal. apply PI.
Qed.

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
  - intros A B C f g [P HP]. apply subsingleton_eq. cbn. intros c. split.
    + intros (b & (a & H1 & H2) & H3). exists a. split; trivial.
      destruct (f a) as [Q HQ]. cbn in *. now exists b.
    + intros (a & H1 & H2). destruct (f a) as [Q HQ] eqn: He. cbn in H2.
      destruct H2 as (b & H3 & H4). exists b. split; trivial.
      exists a. rewrite He. cbn. split; trivial.
Defined.

Definition PCA := @MCA partiality_monad.



(* RCA *)

Definition powerset A :=
  A -> Prop.

Lemma powerset_eq A (P Q : powerset A) :
  (forall x, P x <-> Q x) -> P = Q.
Proof.
  apply CE.
Qed.

Definition powerset_monad : Monad.
Proof.
  unshelve eapply (Build_Monad (M := powerset)).
  - intros A x. exact (eq x).
  - intros A B P F. exact (fun b => exists a, P a /\ F a b).
  - cbn. intros A m. apply powerset_eq. intros x.
    split; eauto. intros [a [H ->]]. apply H.
  - cbn. intros A B F x. apply powerset_eq. intros y.
    split; eauto. intros [a [-> H]]. apply H.
  - cbn. intros A B C F G m. apply powerset_eq. intros x. split.
    + intros (b & (a & H1 & H2) & H3). exists a. split; trivial. now exists b.
    + intros (a & H1 & (b & H3 & H4)). exists b. split; trivial. now exists a.
Defined.

Definition RCA := @MCA powerset_monad.



(* SCA *)

Section SCA.

Variable Sig : Type.

Definition state A :=
  Sig -> powerset (prod Sig A).

Lemma state_eq A (m m' : state A) :
  (forall sig p, m sig p <-> m' sig p) -> m = m'.
Proof.
  intros H. apply FE. intros sig. apply CE. apply H.
Qed.

Definition state_monad : Monad.
Proof.
  unshelve eapply (Build_Monad (M := state)).
  - intros A x. exact (fun sig => eq (sig, x)).
  - intros A B m f. exact (fun sig p => exists sig' x, m sig (sig', x) /\ f x sig' p).
  - cbn. intros A m. apply state_eq. intros sig [sig' x']. split; eauto.
    intros [rho [x [H [=]]]]; subst. apply H.
  - cbn. intros A B f x. apply state_eq. intros sig [sig' x']. split; eauto.
    intros [rho [y [[=] H']]]; subst. apply H'.
  - cbn. intros A B C f g m. apply state_eq. intros sig [sig' z]. split.
    + intros (rho & y & (rho' & x & H1 & H2) & H3). firstorder eauto.
    + intros (rho & x & H1 & (rho' & y & H3 & H4)). firstorder eauto.
Defined.

Definition SCA := @MCA state_monad.

End SCA.



(* CPS *)

Section CPS.

Variable Con : Type.

Definition con A :=
  (A -> Con) -> Con.

Lemma con_eq A (m m' : con A) :
  (forall c, m c = m' c) -> m = m'.
Proof.
  apply FE.
Qed.

Definition continuation_monad : Monad.
Proof.
unshelve eapply (Build_Monad (M := con)).
- intros A x. exact (fun k => k x).
- intros A B m f. exact (fun c => m (fun a => f a c)).
- cbn. intros A m. apply con_eq. reflexivity.
- cbn. intros A B f x. apply con_eq. reflexivity.
- cbn. intros A B C f g m. apply con_eq. reflexivity.
Defined.

Definition CPS := @MCA continuation_monad.

End CPS.



(* ParCA *)

Section ParCA.

Variable Par : Type.

Definition par A :=
  Par -> subsingleton A.

Lemma par_eq A (m m' : par A) :
  (forall p x, proj1_sig (m p) x <-> proj1_sig (m' p) x) -> m = m'.
Proof.
  intros H. apply FE. intros p. apply subsingleton_eq. apply H.
Qed.

Definition parametric_monad : Monad.
Proof.
unshelve eapply (Build_Monad (M := par)).
- intros A x p. exists (eq x). intros y y' ->. tauto.
- intros A B m f p. exists (fun b => exists a, proj1_sig (m p) a /\ proj1_sig ((f a) p) b).
  intros x y [a [H1 H2]] [a' [H3 H4]].
  destruct (m p) as [P HP]. cbn in *. apply (HP a a') in H1 as <-; trivial.
  destruct (f a p) as [Q HQ]. cbn in *. now apply HQ.
- intros A m. cbn. apply par_eq. cbn.
  intros x. split; eauto. intros [y [H ->]]. assumption.
- intros A B f x. apply par_eq. cbn.
  intros y. split; eauto. intros [z [-> H]]. assumption.
- intros A B C f g m. apply par_eq. cbn. intros c. split.
  + intros (b & (a & H1 & H2) & H3). exists a. split; trivial.
    destruct (f a) as [Q HQ]. cbn in *. now exists b.
  + intros (a & H1 & H2). destruct (f a) as [Q HQ] eqn: He. cbn in H2.
    destruct H2 as (b & H3 & H4). exists b. split; trivial.
    exists a. rewrite He. cbn. split; trivial.
Defined.

Definition ParCA := @MCA parametric_monad.

End ParCA.