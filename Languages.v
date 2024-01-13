Require Export Bool List Equalities Orders Setoid Morphisms.
Import ListNotations.

(** * Languages are sets of words over some type of letters *)

Module Lang (Letter : Typ).

Definition word := list Letter.t.
Definition t := word -> Prop.

Declare Scope lang_scope.
Bind Scope lang_scope with t.
Delimit Scope lang_scope with lang.
Local Open Scope lang_scope.

Implicit Type a : Letter.t.
Implicit Type w x y z : word.
Implicit Type L : t.

Definition eq L L' := forall x, L x <-> L' x.

Definition void : t := fun _ => False.
Definition epsilon : t := fun w => w = [].
Definition singleton a : t := fun w => w = [a].

Definition cat L L' : t :=
  fun x => exists y z, x = y++z /\ L y /\ L' z.

Definition union L L' : t := fun w => L w \/ L' w.

Definition inter L L' : t := fun w => L w /\ L' w.

Fixpoint power L n : t :=
  match n with
  | 0 => epsilon
  | S n' => cat L (power L n')
  end.

(** Kleene's star *)

Definition star L : t := fun w => exists n, power L n w.

(** language complement *)

Definition comp L : t := fun w => ~(L w).

(** Languages : notations **)

Module Notations.
Infix "==" := Lang.eq (at level 70).
Notation "∅" := void : lang_scope. (* \emptyset *)
Notation "'ε'" := epsilon : lang_scope. (* \epsilon *)
Coercion singleton : Letter.t >-> Lang.t.
Infix "·" := cat (at level 35) : lang_scope. (* \cdot *)
Infix "∪" := union (at level 50) : lang_scope. (* \cup *)
Infix "∩" := inter (at level 40) : lang_scope. (* \cap *)
Infix "^" := power : lang_scope.
Notation "L ★" := (star L) (at level 30) : lang_scope. (* \bigstar *)
Notation "¬ L" := (comp L) (at level 65): lang_scope. (* \neg *)
End Notations.
Import Notations.

(** Technical stuff to be able to rewrite with respect to "==" *)

Global Instance : Equivalence eq.
Proof. firstorder. Qed.

Global Instance cat_eq : Proper (eq ==> eq ==> eq) cat.
Proof. firstorder. Qed.
Global Instance inter_eq : Proper (eq ==> eq ==> eq) inter.
Proof. firstorder. Qed.
Global Instance union_eq : Proper (eq ==> eq ==> eq) union.
Proof. firstorder. Qed.
Global Instance comp_eq : Proper (eq ==> eq) comp.
Proof. firstorder. Qed.
Global Instance power_eq : Proper (eq ==> Logic.eq ==> eq) power.
Proof.
 intros x x' Hx n n' <-. induction n; simpl; now rewrite ?IHn, ?Hx.
Qed.

Global Instance cat_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) cat.
Proof. intros x x' Hx y y' Hy w w' <-. now apply cat_eq. Qed.
Global Instance inter_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) inter.
Proof. intros x x' Hx y y' Hy w w' <-. now apply inter_eq. Qed.
Global Instance union_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) union.
Proof. intros x x' Hx y y' Hy w w' <-. now apply union_eq. Qed.
Global Instance comp_eq' : Proper (eq ==> Logic.eq ==> iff) comp.
Proof. intros x x' Hy w w' <-. now apply comp_eq. Qed.
Global Instance power_eq' : Proper (eq ==> Logic.eq ==> Logic.eq ==> iff) power.
Proof. intros x x' Hx n n' <- w w' <-. now apply power_eq. Qed.

Global Instance star_eq : Proper (eq ==> eq) star.
Proof.
 intros x x' Hx w. unfold star. now setoid_rewrite <- Hx.
Qed.

Global Instance star_eq' : Proper (eq ==> Logic.eq ==> iff) star.
Proof. intros x x' Hx w w' <-. now apply star_eq. Qed.

(** Languages : misc properties *)

Lemma cat_void_l L : ∅ · L == ∅.
Proof.
    firstorder.
Qed.

Lemma cat_void_r L :  L · ∅ == ∅.
Proof.
  firstorder.
Qed.

Lemma cat_eps_l L : ε · L == L.
Proof.
  intro. split.
    - intro h. firstorder. rewrite H0 in H. simpl in H. subst. assumption.
    - intro h. unfold cat. exists [],x. firstorder. 
Qed.

Lemma cat_eps_r L : L · ε == L.
Proof.
  split.
    - intros h. firstorder. unfold epsilon in H1. 
      subst. rewrite app_nil_r. assumption.
    - intro h. unfold cat. exists x,[]. firstorder. symmetry. apply app_nil_r.
Qed.

Lemma cat_assoc L1 L2 L3 : (L1 · L2) · L3 == L1 · (L2 · L3).
Proof.
  split; intro h; firstorder.
    - exists x2, (x3++x1). subst. firstorder. apply app_assoc_reverse.
    - subst. exists (x0++x2), x3 . firstorder. apply app_assoc.
Qed.


Lemma power_zero x L: (L ^ 0) x -> ε x.
Proof.
  intro h. firstorder.
Qed.

Lemma star_eqn L : L★ == ε ∪ L · L ★.
Proof.
  split;intro h; firstorder.
    - induction x0; firstorder.
    - unfold epsilon in H. subst. exists 0. firstorder.
    - unfold star. exists (1+x2). subst. simpl. exists x0,x1. firstorder.
Qed.

Lemma star_void : ∅ ★ == ε.
Proof.
  split; intro h; firstorder.
    - unfold epsilon. induction x0; firstorder.
    - unfold star. exists 0. firstorder.
Qed.

Lemma power_eps n : ε ^ n == ε.
Proof.
  split; intro h; firstorder.
    - induction n; firstorder. apply IHn. 
      subst. unfold epsilon in H0. subst. simpl. assumption.
    - induction n.
      + firstorder.
      + simpl. unfold cat. exists [],[]; firstorder. 
      unfold epsilon in h. subst. assumption.
Qed.

Lemma star_eps : ε ★ == ε.
Proof.
  split; intros; firstorder.
    - induction x0; firstorder.
      apply IHx0. unfold epsilon in H0. subst. rewrite app_nil_l. assumption.
    - unfold star. exists 0. firstorder.
Qed.

Lemma power_app n m y z L :
 (L^n) y -> (L^m) z -> (L^(n+m)) (y++z).
Proof.
     generalize y,z. induction n.
    - intros. subst. apply power_zero in H. unfold epsilon in H. subst.
      rewrite app_nil_l. assumption.
    - intros. destruct H. destruct H. destruct H. destruct H1. simpl.
     rewrite H. unfold cat.
      exists x,(x0++z0). firstorder. apply app_assoc_reverse. 
Qed.

Lemma power_cat n m L : L^(n+m) == (L^n) · (L^m).
Proof.
  split. 
    - generalize x. induction n. 
      + intros.  simpl in *. apply cat_eps_l. assumption. 
      + intros. simpl in *. destruct H. destruct H. destruct H. destruct H0.
        rewrite H. apply cat_assoc. exists x1,x2. firstorder.
    - intros. unfold cat in H. destruct H. destruct H. destruct H. destruct H0.
        rewrite H. apply power_app; auto.
Qed.



Lemma star_star L : (L★)★ == L★.
Proof.
  split; intros.
    - destruct H. revert H. generalize x. induction x0.
      + intros. simpl in *. exists (0). firstorder.
      + intros. simpl in *. destruct H. destruct H. destruct H. destruct H0.
        subst. destruct H0. apply IHx0 in H1. destruct H1.
         exists (x1+x4). apply power_app; auto.
    - firstorder. unfold star. exists 1. apply cat_eps_r. exists x0. assumption. 
Qed.

Lemma cat_star L : (L★)·(L★) == L★.
Proof.
  split; intros; firstorder.
    - exists (x3+x2). subst. apply power_app; firstorder.
    - unfold cat. exists [],x; firstorder. exists 0. firstorder.
Qed.

(** ** Derivative of a language : definition **)

Definition derivative L w : t := fun x => L (w++x).

Global Instance derivative_eq : Proper (eq ==> Logic.eq ==> eq) derivative.
Proof. intros L L' HL w w' <-. unfold derivative. intro. apply HL. Qed.

(** ** Derivative of a language : properties **)

Lemma derivative_app L w w' :
  derivative L (w++w') == derivative (derivative L w) w'.
Proof.
  split; intros; firstorder.
    - unfold derivative in *. rewrite app_assoc. assumption.
    - unfold derivative in *. rewrite app_assoc_reverse. assumption.
Qed.

Lemma derivative_letter_eps a : derivative a [a] == ε.
Proof. 
  unfold derivative. split. 
    - intro h. unfold epsilon. red in h. 
    apply app_eq_unit in h. destruct h; destruct H.
      + subst. assumption.
      + assumption.
    - intros. unfold epsilon in H. subst. apply app_nil_r.
Qed.

Lemma derivative_letter_void a1 a2 : a1 <> a2 -> derivative a1 [a2] == ∅.
Proof.
  intro h. split; intros; firstorder.
    - unfold void. induction x.
      + destruct h. unfold derivative in H. red in H. apply app_eq_unit in H.
        firstorder. 
        * discriminate.
        * (rewrite <- app_nil_l in H).
         symmetry in H. (rewrite <- app_nil_l in H) .
         apply app_inj_tail in H. destruct H. assumption.  
      + apply IHx. unfold derivative in *. discriminate.
Qed.

Lemma derivative_cat_null L L' a : L [] ->
  derivative (L · L') [a] == (derivative L [a] · L') ∪ derivative L' [a].
Proof.
  split; intros.
      - firstorder. induction x0.
        + right. simpl in *. rewrite <- H0 in H2. assumption.
        + left. simpl in *. unfold cat, derivative. exists x0, x1. firstorder.
          * inversion H0. reflexivity.
          * inversion H0. subst. firstorder.
      - destruct H0.
        + destruct H0. destruct H0. destruct H0. destruct H1.
          rewrite H0. exists ([a]++x0), x1. firstorder.
        + exists [],([a]++x). firstorder. 
Qed.

Lemma derivative_cat_nonnull L L' a : ~L [] ->
  derivative (L · L') [a] == derivative L [a] · L'.
Proof.
   intro h. split; intros; firstorder.
    - unfold cat. unfold derivative. exists x0,x1. split.
      + rewrite <- H. admit.
      + split.
        * admit.
        * assumption.
    - unfold derivative, cat. exists [],([a] ++ x). firstorder.
      + admit.
      + unfold derivative in H0. subst. 
Admitted.

(* Lemma power_app n m y z L :
 (L^n) y -> (L^m) z -> (L^(n+m)) (y++z). *)

Lemma derivative_star L a :
  derivative (L★) [a] == (derivative L [a]) · (L★).
Proof.
  split.
    - intros. unfold derivative, cat. firstorder. exists x,[]. firstorder.
      + symmetry. apply app_nil_r.
      + apply power_app with (n:=0) (m:= x0) (y:= []) (z:= [a] ++x) (L:= L)  in H.
        * simpl in *.
Admitted.

End Lang.
