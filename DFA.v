From Stdlib Require Import Setoid.

(* Functional Extensionality *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall x, f x = g x) -> f = g.

(* Prop *)

Lemma de_morgan_not_or :
  forall P Q : Prop,
    ~ (P \/ Q) <-> ~P /\ ~Q.
  intros.
  split.
  - intros.
    split.
    unfold not in H.
    unfold not.
    intros.
    apply H. left. apply H0.
    unfold not.
    intros.
    apply H. right. apply H0.
  - intros.
    destruct H.
    unfold not.
    intros.
    destruct H1.
    apply H. exact H1.
    apply H0. exact H1.
Qed.

Theorem contrapositive :
  forall (P Q : Prop),
    (P -> Q) -> (~ Q -> ~ P).
  unfold not.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem contrapositive_iff :
  forall (P Q : Prop),
    (P <-> Q) -> (~ P <-> ~Q).
  intros.
  split.
  - destruct H.
    apply contrapositive.
    exact H0.
  - destruct H.
    apply contrapositive.
    exact H.
Qed.

(* Notation *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "x ^ y"  := (xorb x y).

(* Computable Equality *)

Definition is_eq {X : Type} (eq : X -> X -> bool) : Prop :=
  forall u v, eq u v = true <-> u = v.

Theorem computable_eq_refl :
  forall {X : Type} (x : X) (eq : X -> X -> bool),
    is_eq eq ->
      eq x x = true.
  intros.
  destruct (eq x x) eqn:?.
  - reflexivity.
  - rewrite <- Heqb.
    apply H.
    reflexivity.
Qed.

Theorem computable_eq_false :
  forall {X : Type} (x0 x1 : X) (eq : X -> X -> bool),
    is_eq eq -> (eq x0 x1 = false <-> x0 <> x1).
  intros.
  specialize (H x0 x1).
  apply contrapositive_iff in H.
  rewrite <- H.
  destruct (eq x0 x1).
  - split.
    + intros. discriminate.
    + intros. unfold "<>" in *. assert (true = true). { reflexivity. } destruct (H0 H1).
  - split.
    + intros. unfold "<>". intros. discriminate.
    + intros. reflexivity.
Qed.

(* In *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma in_and_not_in :
  forall {X : Type} (l : list X) (x1 x2 : X),
    In x1 l -> ~ In x2 l -> x2 <> x1.
  intros.
  induction l.
  - contradiction.
  - simpl in *.
    apply de_morgan_not_or in H0.
    destruct H0.
    destruct H.
    + subst. unfold not. intros. subst. contradiction.
    + apply (IHl H H1).
Qed.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. generalize dependent x.
  induction l.
  - intros. destruct H.
  - intros. destruct H; subst.
    + exists [], l. reflexivity.
    + apply IHl in H. destruct H, H. subst.
      exists (a :: x0), x1.
      reflexivity.
Qed.

Lemma in_suffix :
  forall {X : Type} (l1 l2 : list X) (x : X),
    In x l2 -> In x (l1 ++ l2).
  induction l1.
  - intros. simpl. exact H.
  - intros. simpl.
    specialize (IHl1 l2 x).
    apply IHl1 in H.
    right. exact H.
Qed.

Lemma in_prefix :
  forall {X : Type} (l1 l2 : list X) (x : X),
    In x l1 -> In x (l1 ++ l2).
  induction l1.
  - intros. inversion H.
  - intros. simpl.
    specialize (IHl1 l2 x).
    simpl in H.
    destruct H.
    + left. exact H.
    + right.
      apply IHl1 in H.
      exact H.
Qed.

Lemma in_app :
  forall {X : Type} (l1 l2 : list X) (x : X),
    In x (l1 ++ l2) <-> In x l1 \/ In x l2.
  induction l1.
  - intros.
    simpl.
    split.
    + intros. right. exact H.
    + intros. destruct H. contradiction. exact H.
  - intros. simpl. split.
    + intros. destruct H.
      * subst. left. left. reflexivity.
      * apply IHl1 in H. destruct H.
        -- left. right. exact H.
        -- right. exact H.
    + intros. destruct H.
      -- destruct H.
         ++ subst. left. reflexivity.
         ++ right. apply in_prefix. exact H.
      -- right. apply in_suffix. exact H.
Qed.

(* app *)

Lemma app_nil_r :
  forall {X : Type} (l : list X),
    l++  [] = l.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length : forall {X : Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1.
  - reflexivity.
  - simpl.
    intros.
    rewrite IHl1.
    reflexivity.
Qed.

(* Lists without duplicates *)

Inductive no_duplicates {X : Type} : list X -> Prop :=
| no_duplicates_nil : no_duplicates []
| no_duplicates_cons (l : list X) (x : X) (Hl : no_duplicates l) (Hx : ~ In x l) : no_duplicates (x :: l).

Lemma no_duplicates_app :
  forall {X : Type} (l1 l2 : list X),
    no_duplicates l1 -> no_duplicates l2 -> (forall x, In x l1 -> ~ In x l2) -> no_duplicates (l1 ++ l2).
  intros.
  induction l1.
  - simpl in *. exact H0.
  - simpl in *. inversion H. subst. apply IHl1 in Hl.
    + constructor.
      * exact Hl.
      * unfold not. intros.
        apply in_app in H2.
        destruct H2.
        -- contradiction.
        -- specialize (H1 a). assert ((a = a) \/ (In a l1)). { left. reflexivity. }
           apply H1 in H3. contradiction.
    + intros. assert ((a = x) \/ (In x l1)). { right. exact H2. }
      apply H1 in H3. exact H3.
Qed.

(* filter *)

Fixpoint filter {X : Type} (f: X -> bool) (l : list X) : list X :=
  match l with
  | nil => nil
  | h::t => if f h then h::(filter f t) else (filter f t)
  end.

Theorem filter_always_nil :
  forall {X : Type} (f : X -> bool) (l : list X),
    filter f l = [] <-> forall x : X, In x l -> f x = false.
  split.
  -- intros.
     induction l.
     - contradiction.
     - simpl in *.
       destruct H0.
       + subst.
         destruct (f x).
         * discriminate.
         * reflexivity.
       + destruct (f a).
         * discriminate.
         * exact (IHl H H0).
  -- intros.
     induction l.
     - reflexivity.
     - simpl in *.
       destruct (f a) eqn:?.
       + pose proof (H a).
         assert (a = a \/ In a l). { left. reflexivity. } apply H0 in H1. rewrite H1 in Heqb. discriminate.
       + apply IHl.
         intros.
         apply H.
         right.
         exact H0.
Qed.

Theorem filter_eq :
  forall {X : Type} (eq : X -> X -> bool) (x : X) (l : list X),
    In x l -> is_eq eq -> no_duplicates l -> filter (eq x) l = [x].
  intros.
  induction l.
  - contradiction.
  - simpl in *.
    inversion H1.
    subst.
    destruct H.
    + unfold is_eq in H0.
      pose proof (H0 x a).
      symmetry in H.
      apply H2 in H.
      rewrite H.
      f_equal.
      apply H0 in H.
      subst.
      reflexivity.
      apply H0 in H.
      subst.
      clear H2 IHl H1.
      apply filter_always_nil.
      intros.
      destruct (eq a x) eqn:?.
      * apply H0 in Heqb.
        subst.
        contradiction.
      * reflexivity.
    + destruct (eq x a) eqn:?.
      * f_equal.
        -- apply H0 in Heqb. subst. reflexivity.
        -- apply H0 in Heqb. subst.
           apply filter_always_nil.
           intros.
           destruct (eq a x) eqn:?.
           ++ apply H0 in Heqb. subst. contradiction.
           ++ reflexivity.
      * exact (IHl H Hl).
Qed.

(* fold *)

Fixpoint fold {X Y : Type} (f : X -> Y -> X) (i : X) (l : list Y) : X :=
  match l with
  | nil => i
  | h :: t => fold f (f i h) t
  end.

(* drop *)

Fixpoint drop {X : Type} (n : nat) (l : list X) : list X :=
  match (n, l) with
  | (0, _) | (_, []) => l
  | (S n', h::t) => drop n' t
  end.

Lemma drop_app :
  forall {X : Type} (l1 l2 : list X) (n : nat),
    length l1 = n -> drop n (l1 ++ l2) = l2.
  induction l1.
  - intros.
    simpl in H.
    subst.
    reflexivity.
  - intros.
    simpl.
    destruct n.
    + discriminate.
    + injection H.
      intros.
      simpl.
      apply IHl1.
      exact H0.
Qed.

(* map *)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | h::t => (f h)::(map f t)
  end.

Lemma map_preserves_length :
  forall {X Y : Type} (l : list X) (f : X -> Y),
    length (map f l) = length l.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    f_equal.
    apply IHl.
Qed.

Lemma map_distr_app : forall {X Y: Type} (f: X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
  induction l1.
  - reflexivity.
  - intros. simpl.
    f_equal.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma in_map :
  forall {X Y : Type} (l : list X) (f : X -> Y) (y : Y),
    In y (map f l) ->
      exists x,
        y = f x /\ In x l.
  intros.
  induction l.
  - contradiction.
  - simpl in *.
    destruct H.
    + exists a. split.
      * subst. reflexivity.
      * left. reflexivity.
    + apply IHl in H. destruct H. destruct H. exists x. split.
      * exact H.
      * right. exact H0.
Qed.

(* repeat *)

Fixpoint repeat {X : Type} (count : nat) (x : X) : list X :=
  match count with
  | 0 => []
  | S count' => cons x (repeat count' x)
  end.

Lemma repeat_split :
  forall {X : Type} (n m : nat) (x : X),
    repeat (n + m) x = (repeat n x) ++ (repeat m x).
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    reflexivity.
Qed.

Lemma repeat_len :
  forall {X : Type} (n : nat) (x : X),
    length (repeat n x) = n.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

Lemma repeat_is_map :
  forall {X Y : Type} (l : list X) (y : Y),
    map (fun _ => y) l = repeat (length l) y.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma no_duplicates_map :
  forall {X Y : Type} (l : list X) (f : X -> Y) (Hdup : no_duplicates l),
    (forall x1 x2, In x1 l -> In x2 l -> x1 <> x2 -> f x1 <> f x2) -> no_duplicates (map f l).
  induction l.
  - constructor.
  - intros. simpl in *.
    inversion Hdup. subst.
    clear Hdup.
    specialize (IHl f Hl).
    constructor.
    + apply IHl.
      intros.
      apply H; try assumption.
      * right. assumption.
      * right. assumption.
    + unfold not.
      intros.
      apply in_map in H0.
      destruct H0.
      destruct H0.
      specialize (H a x).
      assert (a = a \/ In a l). { left. reflexivity. }
      assert (a = x \/ In x l). { right. assumption. }
      specialize (H H2 H3).
      pose proof (in_and_not_in l x a H1 Hx).
      apply H in H4.
      contradiction.
Qed.

(* Universe Lists *)

Definition is_universe {X : Type} (l : list X) : Prop :=
  forall x, In x l.

(* bool_eq *)

Definition bool_eq (b1 b2 : bool) : bool :=
  negb (xorb b1 b2).

Theorem bool_eq_correct : is_eq bool_eq.
  unfold is_eq.
  split; destruct u, v; intros; try reflexivity; try discriminate.
Qed.

(* anyb and allb *)

Definition allb (l : list bool) : bool :=
  fold andb true l.

Definition anyb (l : list bool) : bool :=
  fold orb false l.

Theorem fold_andb_false :
  forall (l : list bool),
    fold andb false l = false.
  induction l.
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem allb_meaning :
  forall (l : list bool) (b : bool),
    allb (b :: l) = true -> (allb l = true /\ b = true).
  intros.
  unfold allb in *.
  simpl in *.
  destruct b.
  - split. 
    + exact H.
    + reflexivity.
  - rewrite fold_andb_false in H.
    discriminate.
Qed.

Theorem allb_true_is_repeat_true :
  forall l,
    allb l = true <-> l = repeat (length l) true.
  intros.
  split.
  - intros.
    induction l.
    + reflexivity.
    + apply allb_meaning in H.
      destruct H.
      subst.
      simpl in *.
      rewrite IHl at 1.
      * reflexivity.
      * exact H.
  - intros.
    induction l.
    + reflexivity.
    + simpl in *.
      injection H.
      intros.
      subst.
      clear H.
      apply IHl in H0.
      unfold allb.
      simpl.
      exact H0.
Qed.

Theorem anyb_true :
  forall (l : list bool),
    anyb (true :: l) = true.
  induction l.
  - reflexivity.
  - unfold anyb in *.
    simpl in *.
    exact IHl.
Qed.

Theorem anyb_false :
  forall (l : list bool),
    anyb (false :: l) = anyb l.
  destruct l.
  - reflexivity.
  - unfold anyb in *.
    simpl in *.
    reflexivity.
Qed.

Lemma anyb_repeat_false :
  forall n,
    anyb (repeat n false) = false.
  induction n.
  - reflexivity.
  - simpl. rewrite anyb_false. exact IHn.
Qed.

Theorem anyb_true_middle :
  forall (l1 l2 : list bool),
    anyb (l1 ++ true :: l2) = true.
  induction l1.
  - intros. simpl. apply anyb_true.
  - intros. simpl. destruct a.
    + apply anyb_true.
    + rewrite anyb_false. rewrite IHl1. reflexivity.
Qed.

Theorem allb_true :
  forall (l : list bool),
    allb (true :: l) = allb l.
  intros.
  destruct l.
  - reflexivity.
  - unfold allb.
    simpl.
    reflexivity.
Qed.

(* Sets *)

Definition subset (X : Type) := X -> bool.

Definition empty_set (X : Type) : subset X :=
  fun _ => false.

Definition subset_eq {X : Type}
                     (l : list X)
                     (s1 s2 : subset X) : bool :=
  allb (map (fun x => bool_eq (s1 x) (s2 x)) l). 

Theorem subset_eq_is_eq :
  forall {X : Type}
    (universe : list X),
      is_universe universe ->
        is_eq (subset_eq universe).
  intros.
  simpl in *.
  destruct universe.
  - split.
    + intros. apply functional_extensionality. intros. contradiction (H x).
    + reflexivity.
  - split.
    + intros. unfold subset_eq in H0. rewrite allb_true_is_repeat_true in H0. simpl in H0.
      injection H0.
      intros.
      clear H0.
      apply functional_extensionality.
      intros.
      pose proof (H x0).
      simpl in H0.
      destruct H0.
      * subst.
        rewrite (bool_eq_correct (u x0) (v x0)) in H2.
        assumption.
      * apply bool_eq_correct.
        apply in_split in H0.
        destruct H0, H0.
        subst.
        simpl in *.
        rewrite map_preserves_length in H1.
        remember (map (fun x : X => bool_eq (u x) (v x)) (x1 ++ (x0 :: x2))) as l1.
        remember (repeat (length (x1 ++ (x0 :: x2))) true) as l2.
        assert ((drop (length x1) l1) = (drop (length x1) l2)).
        { f_equal. subst. exact H1. }
        subst.
        rewrite map_distr_app in H0.
        simpl in *.
        rewrite drop_app in H0.
        rewrite app_length in H0.
        rewrite repeat_split in H0.
        rewrite drop_app in H0.
        simpl in H0.
        injection H0.
        intros.
        exact H4.
        rewrite repeat_len. reflexivity.
        rewrite map_preserves_length.
        reflexivity.
    + intros. subst.
      simpl in *.
      unfold subset_eq.
      rewrite allb_true_is_repeat_true.
      simpl.
      assert (bool_eq (v x) (v x) = true). { apply bool_eq_correct. reflexivity. }
      f_equal. exact H0. clear H0.
      assert ((fun x0 : X => bool_eq (v x0) (v x0)) = (fun _ => true)). { apply functional_extensionality. intros. apply bool_eq_correct. reflexivity. }
      rewrite H0. clear H0.
      rewrite map_preserves_length.
      rewrite repeat_is_map. reflexivity.
Qed.

Definition subset_add {X : Type} (eq : X -> X -> bool) (special : X) (f : subset X) : subset X :=
  fun x => if eq special x then true else f x.

Lemma subset_add_id :
  forall {X : Type} (f : subset X) (x : X) (eq : X -> X -> bool),
    is_eq eq -> f x = true -> subset_add eq x f = f.
  intros.
  unfold subset_add.
  apply functional_extensionality.
  intros.
  destruct (eq x x0) eqn:?.
  - apply H in Heqb. subst. rewrite H0. reflexivity.
  - apply computable_eq_false in Heqb; try exact H. reflexivity.
Qed.

Fixpoint all_subsets {X : Type} (eq: X -> X -> bool) (l : list X) : list (subset X) :=
  match l with
  | nil => [empty_set X]
  | h::t => (map (subset_add eq h) (all_subsets eq t))
         ++ all_subsets eq t
  end.

Definition intersect {X : Type} (s1 s2 : subset X) : subset X :=
  fun x => s1 x && s2 x.

Definition set_add {X : Type} (s : subset X) (eq : X -> X -> bool) (x : X) : subset X :=
match s x with
| false => fun x' => (eq x x) || (s x)
| true => s
end.
 
Definition union {X : Type} (s1 s2 : subset X) : subset X :=
  fun x => s1 x || s2 x.

Definition is_nonempty {X : Type}
                       (universe : list X)
                       (s : subset X) : bool :=
  anyb (map s universe).

Lemma subset_true_implies_in :
  forall {X : Type} (eq : X -> X -> bool) (l : list X) (f : X -> bool) (x : X),
    is_eq eq -> no_duplicates l -> In f (all_subsets eq l) -> f x = true -> In x l.
  intros.
  generalize dependent f.
  induction l.
  - intros. simpl in *. destruct H1. subst. discriminate. contradiction.
  - intros.
    simpl in *.
    rewrite in_app in H1.
    destruct H1.
    + apply in_map in H1.
      destruct H1, H1.
      inversion H0. subst.
      specialize (IHl Hl x0 H3).
      destruct (eq a x) eqn:?.
      * apply H in Heqb. subst. left. reflexivity.
      * apply computable_eq_false in Heqb; try exact H.
        unfold subset_add in H2. assert (eq a x = false). {
          destruct (eq a x) eqn:?.
          - apply H in Heqb0. subst. contradiction.
          - reflexivity.
        }
        rewrite H1 in H2. apply IHl in H2. right. assumption.
    + right. inversion H0. subst. exact (IHl Hl f H1 H2).
Qed.

Theorem all_subsets_is_universe : forall {X : Type} (universe : list X) (eq : X -> X -> bool)
                                    (Hdup : no_duplicates universe)
                                    (Huniverse : is_universe universe)
                                    (Heq : is_eq eq),
                                      is_universe (all_subsets eq universe).
  intros.
  assert (forall (l : list X) (f : subset X) (Hdup : no_duplicates l),
            exists f' : subset X,
              ((In f' (all_subsets eq l)) /\ (forall x : X, In x l -> f x = f' x))
  ). {
    intros.
    induction l.
    - simpl.
      exists (empty_set X).
      split.
      + left. reflexivity.
      + intros. contradiction.
    - destruct (f a) eqn:?.
      + inversion Hdup0. subst.
        destruct (IHl Hl) as [f'].
        destruct H.
        exists (fun x => if eq a x then true else f' x).
        split.
        * simpl. apply in_split in H. destruct H, H.
          rewrite H.
          rewrite map_distr_app.
          simpl.
          apply in_prefix.
          apply in_suffix.
          simpl. left. reflexivity.
        * simpl. intros. destruct H1.
          -- subst. rewrite Heqb. rewrite computable_eq_refl. reflexivity. exact Heq.
          -- apply H0 in H1. rewrite H1. destruct (eq a x) eqn:?.
             ++ apply Heq in Heqb0. subst. rewrite <- H1. exact Heqb.
             ++ reflexivity.
      + inversion Hdup0. subst.
        destruct (IHl Hl) as [f'].
        destruct H.
        exists f'.
        split.
        * simpl. apply in_split in H. destruct H, H.
          rewrite H.
          simpl.
          apply in_suffix.
          apply in_suffix.
          simpl.
          left.
          reflexivity.
        * simpl. intros. destruct H1.
          -- subst. destruct (f' x) eqn:?.
             ++ rewrite Heqb. pose proof (subset_true_implies_in eq l f' x Heq Hl H Heqb0).
                contradiction.
             ++ exact Heqb.
          -- apply H0 in H1. rewrite H1. reflexivity.
  }
  unfold is_universe.
  intros.
  specialize (H universe x Hdup).
  destruct H, H.
  assert (x = x0). {
    apply functional_extensionality.
    intros.
    specialize (H0 x1 (Huniverse x1)).
    exact H0.
  }
  subst.
  exact H.
Qed.

Lemma all_subsets_has_no_duplicates :
  forall {X : Type} (l : list X) (eq : X -> X -> bool),
    is_eq eq -> no_duplicates l -> no_duplicates (all_subsets eq l).
  intros.
  induction l.
  - simpl. constructor.
    + constructor.
    + unfold not.
      intros.
      contradiction.
  - simpl. inversion H0. subst.
    pose proof Hl.
    apply IHl in Hl.
    clear IHl H0.
    apply no_duplicates_app.
    + apply no_duplicates_map; try assumption.
      intros.
      unfold not. intros.
      apply H3.
      destruct (x1 a) eqn:?, (x2 a) eqn:?.
      * pose proof ( subset_add_id x1 a eq H Heqb).
        pose proof (subset_add_id x2 a eq H Heqb0).
        rewrite H5 in H4.
        rewrite H6 in H4.
        contradiction.
      * pose proof (subset_true_implies_in eq l x1 a H H1 H0 Heqb). contradiction.
      * pose proof (subset_true_implies_in eq l x2 a H H1 H2 Heqb0). contradiction.
      * apply functional_extensionality. intros.
        destruct (eq a x) eqn:?.
        -- apply H in Heqb1. subst. rewrite Heqb. rewrite Heqb0. reflexivity.
        -- assert (subset_add eq a x1 x = subset_add eq a x2 x). {
             rewrite H4.
             reflexivity.
           }
           unfold subset_add in H5.
           rewrite Heqb1 in H5.
           exact H5.
    + assumption.
    + unfold not. intros.
      apply in_map in H0.
      destruct H0, H0.
      assert (x a = true). {
        subst.
        unfold subset_add.
        rewrite computable_eq_refl; try assumption.
        reflexivity.
      }
      pose proof (subset_true_implies_in eq l x a H H1 H2 H4). contradiction.
Qed.

(* ThreeOfEm *)

Inductive ThreeOfEm :=
| Zero
| One
| Two.

Theorem three_of_em_universe : is_universe [Zero;One;Two].
  unfold is_universe.
  intros.
  simpl.
  destruct x.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
Qed.

Definition three_of_em_eq (t1 t2: ThreeOfEm) : bool :=
  match (t1, t2) with
  | (Zero, Zero) | (One, One) | (Two, Two) => true
  | _ => false
  end.

Theorem three_of_em_eq_correct : is_eq three_of_em_eq.
  intros. split; destruct u, v; try reflexivity; try discriminate.
Qed.

(* DFAs *)

Definition DFA (C S : Type) : Type :=
  S (* start state *)
  * (subset S) (* accept states *)
  * (C -> S -> S) (* transition fn *).

Fixpoint run_dfa {C S : Type}
                 (eq : S -> S -> bool)
                 (d : DFA C S)
                 (input : list C)
                 : bool :=
  match d with
  | (start_state, accept_states, transition_fn) =>
    match input with
    | [] => accept_states start_state
    | h::t => run_dfa eq ((transition_fn h start_state), accept_states, transition_fn) t
    end
  end.

(* Example DFA *)

Definition ends_with_zero_one :
    DFA ThreeOfEm ThreeOfEm :=
      (
        Zero,
        three_of_em_eq Two,
        fun (c : ThreeOfEm) (s : ThreeOfEm) =>
          match s with
          | One => match c with
                   | One => Two
                   | _ => Zero
                   end
          | _ => match c with
                 | Zero => One
                 | _ => Zero
                 end
          end
      ).

Compute run_dfa three_of_em_eq ends_with_zero_one [One;Two;Zero;One].
Compute run_dfa three_of_em_eq ends_with_zero_one [One;Two;Zero].

(* NFAs *)

Definition NFA (C S : Type) : Type :=
  (subset S) (* start states *)
  * (subset S) (* accept states *)
  * (C -> S -> subset S) (* transition fn *).

Fixpoint run_nfa {C S : Type}
                 (suniverse : list S)
                 (eq : S -> S -> bool)
                 (n : NFA C S)
                 (input : list C)
                 : bool :=
  match n with
  | (start_states, accept_states, transition_fn) =>
    match input with
    | [] => is_nonempty suniverse (intersect start_states accept_states)
    | h :: t => run_nfa suniverse eq (
                  fun (s : S) => (fold union (empty_set S) (map (transition_fn h) (filter start_states suniverse))) s,
                  accept_states,
                  transition_fn) t
    end
  end.

(* Example NFA *)

Definition contains_one_one : NFA ThreeOfEm ThreeOfEm :=
  (
   fun s => three_of_em_eq s Zero,
   fun s => three_of_em_eq s Two,
   fun (c : ThreeOfEm) (state : ThreeOfEm) =>
     fun s => anyb (map (three_of_em_eq s)
       match state with
       | Zero => match c with
                 | Zero => [Zero]
                 | One  => [Zero;One]
                 | Two  => [Zero]
                 end
       | One =>  match c with
                 | Zero => [Zero]
                 | One  => [Two]
                 | Two  => [Zero]
                 end
       | Two =>  match c with
                 | Zero => [Two]
                 | One  => [Two]
                 | Two  => [Two]
                 end
       end)
  ).

Compute run_nfa [Zero;One;Two] three_of_em_eq contains_one_one [One;Two;Zero;One;Zero;Two;One;One;Two].

(* DFA to NFA conversion *)

Definition convert_to_nfa {C S : Type} (eq : S -> S -> bool) (d : DFA C S) : NFA C S :=
  match d with
  | (start_state, accept_states, transition_fn) =>
    (eq start_state, accept_states, fun c s => eq (transition_fn c s))
  end.

Compute run_nfa [Zero;One;Two] three_of_em_eq (convert_to_nfa three_of_em_eq ends_with_zero_one) [One;Two;Zero;One;Zero;One].
Compute run_nfa [Zero;One;Two] three_of_em_eq (convert_to_nfa three_of_em_eq ends_with_zero_one) [One;Two;Zero;One;Zero].

Theorem dfas_are_nfas : forall {C S : Type} (d : DFA C S) (suniverse : list S) (seq : S -> S -> bool)
                               (Hsuniverse : is_universe suniverse) (Hsdup : no_duplicates suniverse)
                               (Hseq : is_eq seq),
                          run_dfa seq d = run_nfa suniverse seq (convert_to_nfa seq d).
  intros.
  apply functional_extensionality.
  intros.
  destruct d as [tmp dtransition_fn].
  destruct tmp as [dstart daccepts].
  generalize dependent dstart.
  induction x.
  - intros. simpl.
    unfold is_nonempty.
    unfold intersect.
    destruct (daccepts dstart) eqn:?.
    + pose proof (Hsuniverse dstart).
      apply in_split in H. destruct H, H.
      rewrite H.
      rewrite map_distr_app.
      simpl.
      rewrite Heqb.
      rewrite computable_eq_refl; try assumption.
      simpl.
      rewrite anyb_true_middle.
      reflexivity.
    + assert ((fun x : S => seq dstart x && daccepts x) = fun _ => false). {
        apply functional_extensionality.
        intros.
        destruct (seq dstart x) eqn:?.
        - apply Hseq in Heqb0. subst. rewrite Heqb. reflexivity.
        - reflexivity.
      }
      rewrite <- (anyb_repeat_false (length suniverse)).
      f_equal.
      rewrite H.
      rewrite repeat_is_map.
      reflexivity.
  - intros. simpl. rewrite IHx.
    rewrite filter_eq; try assumption; try apply Hsuniverse.
    reflexivity.
Qed.

(* NFA to DFA conversion *)

Definition convert_to_dfa {C S : Type}
                          (suniverse : list S)
                          (n : NFA C S) : DFA C (subset S) :=
  match n with
  | (start_states, accept_states, transition_fn) =>
    (
      start_states,
      fun subset_s => is_nonempty suniverse (intersect subset_s accept_states),
      fun c subset_s => fold union (empty_set S) (map (transition_fn c) (filter subset_s suniverse))
    )
  end.

Compute run_dfa (subset_eq [Zero;One;Two])
                (convert_to_dfa [Zero;One;Two] contains_one_one)
                [Zero;One;One].
Compute run_dfa (subset_eq [Zero;One;Two])
                (convert_to_dfa [Zero;One;Two] contains_one_one)
                [Zero;One].

Theorem nfas_are_dfas : forall {C NS : Type} (n : NFA C NS) (nsuniverse : list NS) (nseq : NS -> NS -> bool),
                          run_nfa nsuniverse nseq n = run_dfa (subset_eq nsuniverse) (convert_to_dfa nsuniverse n).
  intros.
  destruct n as [tmp ntransition_fn].
  destruct tmp as [nstarts naccepts].
  apply functional_extensionality.
  intros.
  generalize dependent nstarts.
  induction x.
  - reflexivity.
  - intros.
    apply IHx.
Qed.
