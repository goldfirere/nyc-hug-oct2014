
Require Import List.

Section ord.

Inductive Ordering := LT | EQ | GT.

Parameter A : Set.
Parameter compare : A -> A -> Ordering.
Parameter compare_eq : forall (a b : A), compare a b = EQ -> a = b.
Parameter compare_trans_lt : forall {a b c : A}, compare a b = LT -> compare b c = LT -> compare a c = LT.
Parameter compare_trans_gt : forall {a b c : A}, compare a b = GT -> compare b c = GT -> compare a c = GT.
Parameter compare_anti_gt : forall {a b : A}, compare a b = GT -> compare b a = LT.
Parameter compare_anti_lt : forall {a b : A}, compare a b = LT -> compare b a = GT.

Definition min (a b : A) :=
  match compare a b with
    | LT => a
    | _  => b
  end.

Fixpoint minimum (a : A) (l : list A) :=
  match l with
    | nil => a
    | b :: bs => min a (minimum b bs)
  end.

Inductive WithTop := 
| Value : A -> WithTop
| Top   : WithTop.

Definition minWT (a b : WithTop) :=
  match a, b with
    | Value a, Value b => Value (min a b)
    | Value a, Top     => Value a
    | Top,     Value b => Value b
    | Top,     Top     => Top
  end.

Definition minimumWithTop (l : list A) : WithTop :=
  match l with
    | nil => Top
    | x :: xs => Value (minimum x xs)
  end.

Fixpoint split (l : list A) : (list A * list A) :=
  match l with
    | nil => (nil, nil)
    | a :: nil => (a :: nil, nil)
    | a :: b :: rest =>
      let (xs, ys) := split rest in
      (a :: xs, b :: ys)
  end.

Fixpoint ind_2_levels {A : Type} (P : list A -> Prop)
  (HPnil : P nil) (HPa : forall (a : A), P (a :: nil))
  (Hind : forall (a b : A) (l : list A), P l -> P (a :: b :: l))
  (l : list A) {struct l} : P l :=
  list_ind P HPnil (fun a l0 hpl => match l0 with
                                      | nil => HPa a
                                      | b :: rest =>
                                        Hind a b rest
                                             (ind_2_levels P HPnil HPa Hind rest)
                                    end) l.



Ltac compare_eq :=
  match goal with
    | [ H : compare ?a ?b = EQ |- _ ] => apply compare_eq in H
    | _ => idtac
  end; try congruence.

Lemma min_assoc : forall a b c, min (min a b) c = min a (min b c).
Proof.
  intros. unfold min.
  destruct (compare a b) eqn:?;
  destruct (compare a c) eqn:?;
  destruct (compare b c) eqn:?;
  match goal with
    | [ H : ?x = _ |- context[match ?x with | LT => _ | EQ => _ | GT => _ end] ] => 
      rewrite H
  end; try reflexivity;
  compare_eq.
  pose proof (compare_trans_lt Heqo Heqo1). congruence.
  pose proof (compare_trans_gt Heqo Heqo1). congruence.
Qed.

Lemma min_comm : forall a b, min a b = min b a.
Proof.
  intros. unfold min.
  destruct (compare a b) eqn:?; destruct (compare b a) eqn:?; simpl;
  try reflexivity; compare_eq.
  apply compare_anti_lt in Heqo. congruence.
  apply compare_anti_gt in Heqo. congruence.
Qed.  

Lemma split_min : forall (elts : list A),
  minWT (minimumWithTop (fst (split elts))) (minimumWithTop (snd (split elts)))
    = minimumWithTop elts.
Proof.
  intro elts.
  induction elts using ind_2_levels; try reflexivity.
  simpl. destruct (split elts). unfold fst. unfold snd. unfold minimumWithTop.
 simpl in *. f_equal. unfold minWT in *.
  destruct l; simpl in *.
    destruct l0; simpl in *.
      destruct elts; simpl in *.
        reflexivity.
        congruence.
      destruct elts; simpl in *.
        congruence.
        inversion IHelts. rewrite H0. reflexivity.
    destruct l0; simpl in *.
      destruct elts; simpl in *.
        congruence.
        inversion IHelts. rewrite H0. rewrite min_assoc.
        replace (min (minimum a1 elts) b) with (min b (minimum a1 elts))
          by apply min_comm. reflexivity.
      destruct elts eqn:?.
        simpl in *. congruence. simpl.
        inversion IHelts. simpl in *. rewrite <- H0.
        rewrite min_assoc. f_equal. rewrite <- min_assoc.
        replace (min (minimum a0 l) b) with (min b (minimum a0 l))
          by apply min_comm. rewrite min_assoc. reflexivity.
Qed.

    
      
