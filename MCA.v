(** * Monadic Combinatory Algebras *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Lia Fin.
From Equations.Prop Require Import Equations.



(** ** Monads *)

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



(** ** MCAs *)

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



(** ** SK Definition *)

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
    - exact n.
    - cbn. destruct (to_nat x) as [n Hn]. cbn. lia.
  Defined.

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
        { simp abs.
          unfold abs_obligation_1.
          rewrite appK1. reflexivity. }
        simp abs.
    * simp subs. simp abs.
      rewrite LKn1. rewrite appK1.
      reflexivity.
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
    * depelim x.
      { simp abs. simp subs.
        simp eval. simpl.
        unfold Icode.
        rewrite appS2. rewrite appK.
        simpl_monad. rewrite appK1.
        reflexivity. }
      depelim x. 
    * simp subs. simp abs.
      rewrite appK1. simp eval.
      reflexivity.
    * simp subs. simp abs.
      unfold Sncode2. rewrite appS2.
      rewrite Ih1. simp eval.
      rewrite Ih2. reflexivity.
  Defined.

End SK.



(** ** M-Modalities *)

Class CHA : Type :=
{
  Omega : Type;
  hrel : Omega -> Omega -> Prop;
  htop : Omega;
  hbot : Omega;
  hmeet : Omega -> Omega -> Omega;
  himp : Omega -> Omega -> Omega;
  hinf : (Omega -> Prop) -> Omega;

  ax_refl x : hrel x x;
  ax_trans x y z : hrel x y -> hrel y z -> hrel x z;
  ax_top x : hrel x htop;
  ax_bot x : hrel hbot x;
  ax_meet1 x y : hrel (hmeet x y) x;
  ax_meet2 x y : hrel (hmeet x y) y;
  ax_meet x y z : hrel z x -> hrel z y -> hrel z (hmeet x y);
  ax_imp x y z : hrel (hmeet x y) z <-> hrel x (himp y z);
  ax_inf P x : (forall y, P y -> hrel x y) <-> hrel x (hinf P);
}.

Class MMod (M : Monad) : Type :=
{
  cha : CHA;
  after A : M A -> (A -> Omega) -> Omega;

  ax_ret A x (phi : A -> Omega) : hrel (phi x) (after (ret x) phi);
  ax_bind A B (f : A -> M B) phi m : hrel (after m (fun x => after (f x) phi)) (after (bind m f) phi);
  ax_mono A (phi psi : A -> Omega) m : hrel (hinf (fun x => exists c, x = himp (phi c) (psi c))) (himp (after m phi) (after m psi));
}.

Existing Instance cha.

Add Parametric Relation (cha : CHA) :
  Omega hrel
  reflexivity proved by ax_refl
  transitivity proved by ax_trans
  as hrel_instance.

Notation "x <= y" := (hrel x y).

Section MMod.

  Context {M : Monad}.
  Context {mas : MAS M}.
  Context {mod : MMod M }.

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
  
  Lemma ax_meet_assoc x y z :
    hmeet (hmeet x y) z <= hmeet x (hmeet y z).
  Proof.
    apply ax_meet. eapply ax_trans.
    apply ax_meet1. apply ax_meet1.
    apply ax_meet. eapply ax_trans.
    apply ax_meet1. apply ax_meet2.
    apply ax_meet2.
  Qed.

  Lemma ax_meet_assoc_inv x y z :
    hmeet x (hmeet y z) <= hmeet (hmeet x y) z.
  Proof.
    apply ax_meet. apply ax_meet.
    apply ax_meet1. eapply ax_trans.
    apply ax_meet2. apply ax_meet1.
    eapply ax_trans. apply ax_meet2.
    apply ax_meet2.
  Qed.

  Lemma ax_meet_left l x y :
    x <= y
    -> hmeet l x <= hmeet l y.
  Proof.
    intro H. apply ax_meet.
    apply ax_meet1. eapply ax_trans.
    apply ax_meet2. exact H.
  Qed.

  Lemma ax_meet_right r x y :
    x <= y
    -> hmeet x r <= hmeet y r.
  Proof.
    intro H. apply ax_meet.
    eapply ax_trans.
    apply ax_meet1. exact H.
    apply ax_meet2.
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

  Lemma ax_mono_ext' {A} (phi psi : A -> Omega) m x :
    (forall c, hmeet x (phi c) <= psi c) -> hmeet x (after m phi) <= after m psi.
  Proof.
    intros H. apply ax_imp. rewrite <- ax_mono.
    apply ax_inf. intros y [c ->]. apply ax_imp, H.
  Qed.

  Lemma ax_mono_ext {A} (phi psi : A -> Omega) m :
    (forall c, phi c <= psi c) -> after m phi <= after m psi.
  Proof.
    intros H. erewrite <- (@ax_mono_ext' A phi psi m htop).
    - apply ax_meet; try reflexivity. apply ax_top.
    - intros c. rewrite ax_meet2. apply H.
  Qed.

  Lemma ax_mono_meet {A} (phi : A -> Omega) m x :
    hmeet x (after m phi) <= after m (fun a => hmeet x (phi a)).
  Proof.
    apply ax_mono_ext'. reflexivity.
  Qed.

  Lemma ax_mono_imp {A} (phi : A -> Omega) m x :
    after m (fun a => himp x (phi a)) <= himp x (after m phi).
  Proof.
    apply ax_imp. rewrite ax_meet_comm. apply ax_mono_ext'.
    intros c. rewrite ax_meet_comm. apply ax_imp. reflexivity.
  Qed.

End MMod.



(** ** Separators *)

Section Sep.

  Context {M : Monad}.
  Context {mas : MAS M}.
  Context {mca : MCA mas}.
  Context {mod : MMod M }.

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

Class separator (M : Monad) (mas : MAS M) (mca : MCA mas) (mod : MMod M) : Type :=
  {
    subset : code -> Prop;
    Sep1 : ccomplete subset;
    Sep2 : progress subset;
  }.

Coercion subset : separator >-> Funclass.



(** ** Evidenced Frames *)

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



(** ** Induced Evidenced Frame *)

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

Instance MCA_EF M (mas : MAS M) (mca : MCA mas) (mod : MMod M) (sep : separator mca mod) : EF.
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

Lemma agreement M (mas : MAS M) (mca : MCA mas) (mod : MMod M) (sep : separator mca mod) :
  (htop <= hbot) <-> exists e, erel top e bot.
Proof.
  split; intros H.
  - exists eid. cbn. intros c. simpl_mca. rewrite <- ax_ret. apply H.
  - destruct H as [e H]. cbn in H. rewrite (H e). apply Sep2; intuition.
Qed.



(** ** Examples *)

(** *** Axioms *)

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



(** *** Abstract termination predicates *)

Section Examples.

Class TER {M : Monad} (mod : MMod M) : Type :=
{
  ter_pred A : M A -> Omega;
  ter_ret A (x : A) : htop <= ter_pred (ret x);
  ter_bind A B (m : M A) (f : A -> M B) :
    hmeet (ter_pred m) (after m (fun x => ter_pred (f x)))
    <= ter_pred (bind m f);
}.

Definition term_mod {M : Monad}
  (mod : MMod M) (trm : TER mod)
  : MMod M.
Proof.
  unshelve econstructor.
  - intros A m phi.
    exact (hmeet (ter_pred m) (after m phi)).
  - intros A x phi.
    apply ax_meet.
    * eapply ax_trans.
      apply ax_top. apply ter_ret.
    * apply ax_ret.
  - intros A B f phi m.
    apply ax_meet.
    * eapply ax_trans.
      + apply ax_meet_left.
        apply ax_mono_ext.
        intro c. apply ax_meet1.
      + apply ter_bind.
    * eapply ax_trans. eapply ax_trans.
      + apply ax_meet2.
      + apply ax_mono_ext.
        intro c. apply ax_meet2.
      + apply ax_bind.
  - intros A phi psi m.
    apply ax_imp.
    eapply ax_trans.
    eapply ax_trans.
    eapply ax_trans.
    * apply ax_meet_assoc_inv.
    * apply ax_meet_right.
      apply ax_meet_comm.
    * apply ax_meet_assoc.
    * apply ax_meet_left.
      apply ax_imp.
      apply ax_mono.
Defined.



(** *** PCA *)

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

Definition sub_cha (X : Type) : CHA.
Proof.
  unshelve econstructor.
  - exact (X -> Prop).
  - intros p q. exact (forall x, p x -> q x).
  - exact (fun _ => True).
  - exact (fun _ => False).
  - intros p q. exact (fun x => p x /\ q x).
  - intros p q. exact (fun x => p x -> q x).
  - intros P. exact (fun x => forall q, P q -> q x).
  - cbn. tauto.
  - cbn. intuition.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. intuition.
  - cbn. intuition.
  - cbn. intuition.
Defined.

Definition partiality_modality : MMod partiality_monad.
Proof.
  unshelve econstructor.
  - exact (sub_cha unit).
  - intros A m phi. exact (fun x => exists a, proj1_sig m a /\ phi a x).
  - cbn. eauto.
  - cbn. intros A B f phi [P HP] []. cbn. firstorder.
  - cbn. intros A phi psi [P HP] []. cbn. intros H [a [H1 H2]].
    exists a. split; trivial. apply H. exists a. apply CE. intros []. intuition.
Defined.

Context { mas_part : MAS partiality_monad }.

Lemma partiality_progress :
  forall c c', after (MMod := partiality_modality) (mapp c c') (fun _ => hbot) <= hbot.
Proof.
  intros c c'. cbn. firstorder.
Qed.



(** *** RCA *)

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

Definition pow_ang_modality : MMod powerset_monad.
Proof.
  unshelve econstructor.
  - exact (sub_cha unit).
  - intros A m phi. exact (fun x => exists a, m a /\ phi a x).
  - cbn. eauto.
  - cbn. intros A B f phi P []. cbn. firstorder.
  - cbn. intros A phi psi P []. cbn. intros H [a [H1 H2]].
    exists a. split; trivial. apply H. exists a. apply CE. intros []. intuition.
Defined.

Context { mas_power : MAS powerset_monad }.

Lemma pow_ang_progress :
  forall c c', after (MMod := pow_ang_modality) (mapp c c') (fun _ => hbot) <= hbot.
Proof.
  intros c c'. cbn. firstorder.
Qed.

Definition pow_dem_naive_modality : MMod powerset_monad.
Proof.
  unshelve econstructor.
  - exact (sub_cha unit).
  - intros A m phi. exact (fun x => forall a, m a -> phi a x).
  - cbn. intros A x1 phi [] H x2 E.
    rewrite <- E. apply H.
  - cbn. intros A B f phi P [] H y [ x [ p Fxy ] ].
    + eapply H. apply p. apply Fxy.
  - cbn. intros A phi psi m un H1 H2 x mx.
    destruct un.
    apply H1. exists x.
    apply CE. intros un. destruct un.
    split.
    + intros psi_x_tt phi_x_tt. exact psi_x_tt.
    + intros phi_psi. apply phi_psi.
      apply H2. apply mx.
Defined.

Definition pow_dem_modality (ter : TER pow_dem_naive_modality) : MMod powerset_monad :=
  term_mod ter.



(** *** SCA *)

Section SCA.

Variable Sig : Type.
Variable srel : Sig -> Sig -> Prop.
Hypothesis srel_refl : forall x, srel x x.
Hypothesis srel_tran : forall x y z, srel x y -> srel y z -> srel x z.

Definition state A :=
  { m : Sig -> powerset (prod Sig A) | forall sig0 sig1 x, m sig0 (sig1, x) -> srel sig0 sig1 }.

Lemma state_eq A (m m' : state A) :
  (forall sig p, proj1_sig m sig p <-> proj1_sig m' sig p) -> m = m'.
Proof.
  intros H. destruct m, m'. cbn in H.
  assert (x = x0) as <-.
  { apply FE. intros sig. apply CE. apply H. }
  f_equal. apply PI.
Qed.

Definition state_monad : Monad.
Proof.
  unshelve eapply (Build_Monad (M := state)).
  - intros A x. exists (fun sig => eq (sig, x)).
    intros sig0 sig1 x0 [=]. subst. apply srel_refl.
  - intros A B m f. exists (fun sig p => exists sig' x, proj1_sig m sig (sig', x) /\ proj1_sig (f x) sig' p).
    intros sig0 sig1 x (sig' & x0 & H1 & H2). apply srel_tran with sig'.
    + eapply (proj2_sig m). apply H1.
    + eapply (proj2_sig (f x0)). apply H2.
  - cbn. intros A m. apply state_eq. cbn. intros sig [sig' x']. split; eauto.
    intros [rho [x [H [=]]]]; subst. apply H.
  - cbn. intros A B f x. apply state_eq. cbn. intros sig [sig' x']. split; eauto.
    intros [rho [y [[=] H']]]; subst. apply H'.
  - cbn. intros A B C f g m. apply state_eq. cbn. intros sig [sig' z]. split.
    + intros (rho & y & (rho' & x & H1 & H2) & H3). firstorder eauto.
    + intros (rho & x & H1 & (rho' & y & H3 & H4)). firstorder eauto.
Defined.

Definition SCA := @MCA state_monad.

Definition state_cha : CHA.
Proof.
  unshelve econstructor.
  - exact { p : Sig -> Prop | forall sig sig', srel sig sig' -> p sig -> p sig' }.
  - intros p q. exact (forall x, proj1_sig p x -> proj1_sig q x).
  - exists (fun _ => True). tauto.
  - exists (fun _ => False). tauto.
  - intros [p Hp] [q Hq]. exists (fun x => p x /\ q x). firstorder.
  - intros [p Hp] [q Hq]. exists (fun x => forall y, srel x y -> p y -> q y).
    intros. apply H0; trivial. eapply srel_tran; eauto.
  - intros P. exists (fun x => forall q, P q -> proj1_sig q x).
    intros sig sig' H H' p HP. specialize (H' p). destruct p as [p Hp].
    cbn in *. apply (Hp sig); trivial. now apply H'.
  - cbn. tauto.
  - cbn. intuition.
  - cbn. tauto.
  - cbn. tauto.
  - intros [p Hp] [q Hq]. cbn. tauto.
  - intros [p Hp] [q Hq]. cbn. tauto.
  - intros [p Hp] [q Hq]. cbn. intuition.
  - intros [p Hp] [q Hq] [r Hr]. intros. cbn. firstorder.
  - intros P. cbn. intuition.
Defined.

Definition state_ang_modality : MMod state_monad.
Proof.
  unshelve econstructor.
  - exact state_cha.
  - intros A [m Hm] phi. exists (fun sig => forall sig2, srel sig sig2 -> exists x sig', m sig2 (sig', x) /\ proj1_sig (phi x) sig').
    intros sig sig' H H' sig2 Hs. destruct (H' sig2) as (x & sig0 & H1 & H2).
    + apply srel_tran with sig'; trivial.
    + exists x, sig0. split; trivial.
  - cbn. intros A x phi sig H1 sig2 HS. exists x, sig2. split; trivial.
    destruct (phi x) as [p Hp]. cbn in *. now apply Hp with sig.
  - cbn. intros A B f phi [m Hm] sig H sig2 HS. cbn in *.
    destruct (H sig2) as (x & sig' & H1 & H2); trivial.
    destruct (f x) eqn : Hf. cbn in *.
    destruct (H2 sig') as (y & sig'' & H3 & H4); trivial.
    exists y, sig''. split; trivial. exists sig', x. rewrite Hf. split; trivial.
  - cbn. intros A phi psi [m Hm] sig H sig2 HS. cbn.
    intros H' sig3 HS'. destruct (H' sig3) as (x & sig' & H1 & H2); trivial.
    exists x, sig'. split; trivial.
    specialize (H (@himp state_cha (phi x) (psi x))).
    assert (HP : proj1_sig (@himp state_cha (phi x) (psi x)) sig).
    + apply H. exists x. reflexivity.
    + cbn in HP. destruct (phi x), (psi x); cbn in *. apply HP; trivial.
      apply srel_tran with sig2; trivial.
      apply srel_tran with sig3; trivial. eapply Hm. eauto.
Defined.

Context { mas_state : MAS state_monad }.

Lemma state_ang_progress :
  forall c c', after (MMod := state_ang_modality) (mapp c c') (fun _ => hbot) <= hbot.
Proof.
  intros c c'. cbn. intros sig. cbn. destruct (mapp c c'). cbn.
  intros H. destruct (H sig) as (_ & _ & _ & []). apply srel_refl.
Qed.

End SCA.



(** *** CPS *)

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



(** *** ParCA *)

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

Definition parametric_modality : MMod parametric_monad.
Proof.
  unshelve econstructor.
  - exact (sub_cha unit).
  - intros A m phi. exact (fun x => forall p, exists a, proj1_sig (m p) a /\ phi a x).
  - cbn. eauto.
  - cbn. intros A B f phi F []. intros H p.
    destruct (H p) as (a & H1 & H2). firstorder eauto.
  - cbn. intros A phi psi F []. intros H1 H2 p. destruct (H2 p) as (a & H3 & H4).
    exists a. split; trivial. apply H1. exists a. apply CE. intros []. intuition.
Defined.

Context { mas_par : MAS parametric_monad }.

Lemma parametric_progress (p0 : Par) :
  forall c c', after (MMod := parametric_modality) (mapp c c') (fun _ => hbot) <= hbot.
Proof.
  intros c c'. cbn. firstorder.
Qed.

End ParCA.

End Examples.