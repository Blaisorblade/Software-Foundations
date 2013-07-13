(** * Logic: Logic in Coq *)

(* $Date: 2011-06-22 10:06:32 -0400 (Wed, 22 Jun 2011) $ *)

Require Export "Prop". 
Require Import LibTactics.
(** Coq's built-in logic is extremely small: [Inductive] definitions,
    universal quantification ([forall]), and implication ([->]) are
    primitive, but all the other familiar logical connectives --
    conjunction, disjunction, negation, existential quantification,
    even equality -- can be defined using just these. *)

(* ########################################################### *)
(** * Quantification and Implication *)

(** In fact, [->] and [forall] are the _same_ primitive!  Coq's [->]
    notation is actually just a shorthand for [forall].  The [forall]
    notation is more general, because it allows us to _name_ the
    hypothesis. *)

(** For example, consider this proposition: *)

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

(** If we had a proof term inhabiting this proposition, it would be a
    function with two arguments: a number [n] and some evidence that
    [n] is even.  But the name [E] for this evidence is not used in
    the rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name.  We could write it like this instead: *)

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

(** Or we can write it in more familiar notation: *)

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

(** This illustrates that "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] is
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  (* Case "left". *) apply ev_0.
  (* Case "right". *) apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ===>  conj (ev 0) (ev 4) ev_0 (ev_SS 2 (ev_SS 0 ev_0))
            : ev 0 /\ ev 4 *)

(** Note that the proof is of the form
[[
    conj (ev 0) (ev 4) (...pf of ev 0...) (...pf of ev 4...)
]]
    which is what you'd expect, given the type of [conj]. *)

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and put this evidence into the
    proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  introv H.
  inversion H as [HP HQ].
  apply HQ. Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  introv H. inversion H as [HP HQ]. split; assumption.
Qed.
(*
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right".*) apply HP.  Qed. *)
  
(** Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easy to understand.  Examining it
    shows that all that is really happening is taking apart a record
    containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)

Print and_commut.
(* ===>
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks [H : P /\ (Q /\ R)] down into [HP: P], [HQ :
    Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split; [split | ]; assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, recommended (even_ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in the last chapter.  Notice that
   the left-hand conjunct here is the statement we are actually
   interested in; the right-hand conjunct is needed in order to make
   the induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even_ev_fails : forall n : nat,
  even n -> ev n.
Proof.
  induction n.
  intros. apply ev_0.
Admitted.
Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  induction n as [|n']; [| inversion IHn' as [H0 H1]]; split; intros.
    apply ev_0.
    inversion H.
    apply H1. assumption.
    apply ev_SS. apply H0. unfold even. unfold even in H. simpl in H. assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun _ _ _ pq qr =>
    match pq with
      | conj p q =>
        match qr with
          | conj q2 r => conj _ _ p r
        end
    end.
(** [] *)

(* ###################################################### *)
(** ** Iff *)

(** The familiar logical "if and only if" is just the
    conjunction of two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  intros. split; intros; assumption.
Qed.
Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  introv pqEq qrEq. inversion pqEq as [pq qp]. inversion qrEq as [qr rq].
  dup.
    split; intros; tauto.

    split.
    Case "P -> R". introv p. apply qr. apply pq. apply p.
    Case "R -> P". introv r. apply qp. apply rq. apply r.
    Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** **** Exercise: 2 stars (MyProp_iff_ev) *)
(** We have seen that the families of propositions [MyProp] and [ev]
    actually characterize the same set of numbers (the even ones).
    Prove that [MyProp n <-> ev n] for all [n].  Just for fun, write
    your proof as an explicit proof object, rather than using
    tactics. (_Hint_: if you make use of previously defined thoerems,
    you should only need a single line!) *)
Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun n => conj _ _ (ev_MyProp _) (MyProp_ev _).
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P],[Q] and
    evidence of [P], and returns as output, the evidence of [P /\ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for! -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". right. apply HP.
    Case "left". left. apply HQ.  Qed.

(** **** Exercise: 2 stars, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

Check or_commut'.
Definition or_commut'' P Q (pq: P \/ Q): Q \/ P :=
  match pq with
    | or_introl p => or_intror _ _ p
    | or_intror q => or_introl _ _ q
  end.
(** [] *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars, recommended (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  introv H. inversion H as [[HP | HQ] [HP' | HR]].
  Case "PP".
  left. apply HP.
  Case "PR".
  left. apply HP.
  Case "QP".
  left. apply HP'.
  Case "QR".
  right. split; assumption.
Qed.
(** [] *)

(** **** Exercise: 1 star (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split; [apply or_distributes_over_and_1 | apply or_distributes_over_and_2].
Qed.
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are obviously analogs, in some sense, of the logical connectives
    [/\] and [\/].  This analogy can be made more precise by the
    following theorems, which show how to translate knowledge about
    [andb] and [orb]'s behaviors on certain inputs into propositional
    facts about those inputs. *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  introv H. unfold andb in H. split.
  Case "b = true".
    destruct b; [reflexivity | inversion H].
  Case "c = true".
    destruct c; [reflexivity | destruct b; inversion H].
Qed.
(*
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.
*)

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  introv H.
  inversion H. subst. reflexivity.
Qed.
(*
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.*)

(** **** Exercise: 1 star (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  introv H.
  destruct b; destruct c; inversion H.
  Case "c = false". right. reflexivity.
  Case "b = false". left. reflexivity.
  Case "b = c = false". left. reflexivity.
Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  introv H.
  destruct b; destruct c; inversion H.
  Case "c = false". right. reflexivity.
  Case "b = false". left. reflexivity.
  Case "b = c = false". right. reflexivity.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  introv H. destruct b; destruct c; inversion H; split; reflexivity.
Qed.
(** [] *)

(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)

(** **** Exercise: 1 star (False_ind_principle) *)
(** Can you predict the induction principle for falsehood? *)

Check False_ind.
(* False_ind *)
(*      : forall P : Prop, False -> P *)

(** [] *)

(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)

(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, we might wonder whether it
    is possible to define truth in the same way.  Naturally, the
    answer is yes. *)

(** **** Exercise: 2 stars (True_induction) *)
(** Define [True] as another inductively defined proposition.  What
    induction principle will Coq generate for your definition?  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.  Alternatively, you may find it easiest
    to start with the induction principle and work backwards to the
    inductive definition.) *)

Inductive True :=
| tt : True.
Check True_ind.
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  introv contra. inversion contra as [HP HNP]. apply HNP in HP. inversion HP.

  Restart.
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  introv HP. unfold not. introv HNP. apply HNP. apply HP.
  Restart.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, recommended (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_: Suppose that [P] is true. We need then to prove that
   [~~P], that is that [(P -> False) -> False]. Let us introduce (HNP:
   P -> False) in the context; we need now to prove False. Since we
   know that P is true and that HNP is true, by modus ponens we can
   conclude that P's conclusion, False, is true.
 [] *)

(** **** Exercise: 2 stars, recommended (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  introv HPQ HNQ HP. apply HNQ in HPQ. assumption. assumption.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  unfold not. introv HPNP. inversion HPNP as [HP HNP]. apply (HNP HP).
Qed.
(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  unfold not. introv H. inverts H as H. inverts H as H. inverts H as H.

  Restart.

  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star ev_not_ev_S *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
    Case "n = 0". introv H. inversion H.
    Case "n = S n'". introv H1. inverts H1 as. apply IHev.
Qed.
(** [] *)

(** **** Exercise: 1 star (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)

(** Note that some theorems that are true in classical logic
    are _not_ provable in Coq's "built in" constructive logic... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* But now what? There is no way to "invent" evidence for [P]. *) 
  Admitted.

(** **** Exercise: 5 stars, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* FILL IN HERE *)
Theorem excluded_middle_to_peirce : excluded_middle -> peirce.
Proof.
  unfold peirce. unfold excluded_middle. unfold not.
  introv no_middle. introv H.
  assert (PorNP := no_middle P).
  inversion PorNP as [| HNP].
  Case "P". assumption.
  Case "NP". apply H. intro HP. apply ex_falso_quodlibet. apply HNP. apply HP.
Qed.

(*
Theorem classic_to_peirce : classic -> peirce.
Proof.
  unfold peirce. unfold classic. unfold not.
  introv classic.
  apply classic.
  introv H. apply H.
  introv Hpeirce. apply Hpeirce.
*)

Theorem excluded_middle_to_classic : excluded_middle -> classic.
Proof.
  unfold classic. unfold excluded_middle. unfold not.
  introv H HNNP.
  assert (PorNP := H P).
  inversion PorNP as [HP | HNP].
  Case "P". apply HP.
  Case "~P". apply HNNP in HNP. inversion HNP.
Qed.

(*
Theorem classic_to_excluded_middle : classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle. unfold not.
  introv classic. introv.
  assert (classicP := classic P).
  (* cases ((P -> False) -> False). *)
Admitted.
Theorem classic_to_de_morgan_not_and_not : classic -> de_morgan_not_and_not.
Proof.
  unfold classic. unfold de_morgan_not_and_not. unfold not.
  intros.
  assert (H2 := H P).
*)

Theorem excluded_middle_to_de_morgan_not_and_not :
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  introv no_middle. introv no_conj.
  assert (PorNP := no_middle P).
  assert (QorNQ := no_middle Q).
  inversion PorNP as [| NP].
    Case "P". left. assumption.
    Case "NQ". 
      inversion QorNQ as [| NQ].
      SCase "Q". right. assumption.
      SCase "NQ".
        unfold not in no_conj, NP, NQ.
        apply ex_falso_quodlibet.
        apply (no_conj (conj _ _ NP NQ)).
Qed.

Theorem excluded_middle_to_implies_to_or : excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle. unfold implies_to_or.
  introv no_middle. introv PtoQ.
  assert (PorNP := no_middle P).
  inversion PorNP.
  Case "P". right. apply PtoQ. assumption.
  Case "NP". left. assumption.
Qed.

(*
Theorem implies_to_or_to_excluded_middle : implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. unfold excluded_middle. unfold not.
  introv impl_to_or. introv
  assert (H := impl_to_or P (~P)).

Theorem implies_to_or_to_classic : implies_to_or -> classic.
Proof.
  unfold implies_to_or. unfold classic.
  introv impl_to_or. introv NNP.
  unfold not in NNP.  
  (* assert (H1 := impl_to_or P (~P)).
  assert (H2 := impl_to_or (not P) False).
  assert (H3 := impl_to_or P False). *)
  unfold not in *.
  apply H2 in NNP.
*)
(** [] *)

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

SearchAbout beq_nat.
Check beq_nat_eq.
(* beq_nat_eq *)
(*      : forall n m : nat, true = beq_nat n m -> n = m *)

(** **** Exercise: 2 stars, recommended (not_eq_beq_false) *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  unfold not.
  introv neq.
  cases (beq_nat n n'); [| reflexivity].
  apply ex_falso_quodlibet.
  apply neq.
  apply beq_nat_eq. symmetry. assumption.
Qed.
  (* unfold not.
  introv neq.
  induction n as [|n0].
  Case "n = 0".
    induction n'.
    apply ex_falso_quodlibet. apply neq. reflexivity.
    reflexivity.
  Case "n = S n0".
    induction n'.
    reflexivity.

    simpl.
    destruct (beq_nat n0 n'). apply ex_falso_quodlibet.
  Restart.
  
  unfold not.
  introv neq.
  cases (beq_nat n n'); [| reflexivity].
  apply ex_falso_quodlibet.
  apply neq.
  destruct n; destruct n'; try reflexivity; inverts H. *)

(** [] *)

(** **** Exercise: 2 stars, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  unfold not.
  introv beq_False nEqm. subst.
  Check beq_nat_refl.
(* beq_nat_refl *)
(*      : forall n : nat, true = beq_nat n n *)
  rewrite <- beq_nat_refl in beq_False.
  inversion beq_False.
Qed.
(** [] *)

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can capture what this means with the
    following definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

    For example, consider this existentially quantified proposition: *)

Definition some_nat_is_even : Prop := 
  ex nat ev.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** Coq's notation definition facility can be used to introduce
    more familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the same set of tactics as always for
    manipulating existentials.  For example, if to prove an
    existential, we [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note, again, that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, 
     n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
     (exists m, n = 4 + m) ->
     (exists o, n = 2 + o).
Proof.
  intros n H. 
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 

(** **** Exercise: 1 star (english_exists) *)
(** In English, what does the proposition 
[[
      ex nat (fun n => ev (S n))
]] 
    mean? *)

(* FILL IN HERE *)

(** Complete the definition of the following proof object: *)
Check ex_intro.
(* ex_intro *)
(*      : forall (X : Type) (P : X -> Prop) (witness : X), *)
(*        P witness -> exists x, P x *)

Definition p : ex nat (fun n => ev (S n)) := ex_intro _ (fun n => ev (S n)) 1 (ev_SS _ ev_0).
Check p.
(* p *)
(*      : exists n : nat, ev (S n) *)

(** [] *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  unfold not. introv forAll nExists.
  inversion nExists as [x px].
  apply px. apply forAll.
Qed.

(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** The other direction requires the classical "law of the excluded
    middle": *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. unfold not.
  introv no_middle nnExists. introv.
  assert (H := no_middle (P x)).
  inversion H.
  Case "P x". assumption.
  Case "~ (P x)".
    apply ex_falso_quodlibet.
    apply nnExists.
    exists x. assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  Case "->".
    introv exOr.
    inversion exOr as [x [Px | Qx]]; [left | right]; exists x; assumption.
  Case "<-".
    introv orEx.
    inversion orEx as [[x Px] | [x Qx]]; exists x; [left | right]; assumption.
Qed.
(** [] *)

Print dist_exists_or.



(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (We enclose the definition in a
    module to avoid confusion with the standard library equality,
    which we have used extensively already.) *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.
Check eq_ind.
(* eq_ind *)
(*      : forall (X : Type) (P : X -> X -> Prop), *)
(*        (forall x : X, P x x) -> forall y y0 : X, eq X y y0 -> P y y0 *)

(** Standard infix notation (using Coq's type argument synthesis): *)

Notation "x = y" := (eq _ x y) 
                    (at level 70, no associativity) : type_scope.

(** This is a bit subtle.  The way to think about it is that, given a
    set [X], it defines a _family_ of propositions "[x] is equal to
    [y]," indexed by pairs of values ([x] and [y]) from [X].  There is
    just one way of constructing evidence for members of this family:
    applying the constructor [refl_equal] to a type [X] and a value [x
    : X] yields evidence that [x] is equal to [x]. *)

(** Here is a slightly different definition -- the one that actually
    appears in the Coq standard library. *)

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.
Check eq'_ind.
(* eq'_ind *)
(*      : forall (X : Type) (x : X) (P : X -> Prop), *)
(*        P x -> forall y : X, eq' X x y -> P y *)
Notation "x =' y" := (eq' _ x y) 
                     (at level 70, no associativity) : type_scope.

(** **** Exercise: 3 stars, optional (two_defs_of_eq_coincide) *)
(** Verify that the two definitions of equality are equivalent. *)

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  split; introv eq; inverts eq; [apply refl_equal' | apply refl_equal].
Qed.
(** [] *)

(** The advantage of the second definition is that the induction
    principle that Coq derives for it is precisely the familiar
    principle of _Leibniz equality_: what we mean when we say "[x] and
    [y] are equal" is that every property on [P] that is true of [x]
    is also true of [y]. *)

Check eq'_ind.
(* ===>  forall (X : Type) (x : X) (P : X -> Prop),
             P x -> forall y : X, x =' y -> P y *)

(** One important consideration remains.  Clearly, we can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes.
    Indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval simpl], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
    
    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)

Definition four : 2 + 2 = 1 + 3 :=  
  refl_equal nat 4. 
Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x]. 

End MyEquality.

(* ####################################################### *)
(** ** Inversion, Again *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context of the subgoal, and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal.

   _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)

(* ####################################################### *)
(** * Relations as Propositions *)

(** A proposition parameterized numbers (such as [ev]) can be
    thought of as a _property_ -- i.e., it defines a subset of [nat],
    namely those numbers for which the proposition is provable.  In
    the same way, a two-argument proposition can be thought of as a
    _relation_ -- i.e., it defines a set of pairs for which the
    proposition is provable. *)

Module LeFirstTry.  

(** We've already seen an inductive definition of one
    fundamental relation: equality.  Another useful one is the "less
    than or equal to" relation on numbers: *)

(** This definition should be fairly intuitive.  It says that
    there are two ways to give evidence that one number is less than
    or equal to another: either observe that they are the same number,
    or give evidence that the first is less than or equal to the
    predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).
Check le_ind.
(* le_ind *)
(*      : forall P : nat -> nat -> Prop, *)
(*        (forall n : nat, P n n) -> *)
(*        (forall n m : nat, le n m -> P n m -> P n (S m)) -> *)
(*        forall n n0 : nat, le n n0 -> P n n0 *)

End LeFirstTry.

(** This is a reasonable definition of the [<=] relation, but we
    can streamline it a little by observing that the left-hand
    argument [n] is the same everywhere in the definition, so we can
    actually make it a "general parameter" to the whole definition,
    rather than an argument to each constructor.  This is similar to
    what we did in our second definition of the [eq] relation,
    above. *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle. 
    (The same was true of our second version of [eq].) *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(** By contrast, the induction principle that Coq calculates for the
    first definition has a lot of extra quantifiers, which makes it
    messier to work with when proving things by induction.  Here is
    the induction principle for the first [le]: *)

(* le_ind : 
     forall P : nat -> nat -> Prop,
     (forall n : nat, P n n) ->
     (forall n m : nat, le n m -> P n m -> P n (S m)) ->
     forall n n0 : nat, le n n0 -> P n n0 *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in the previous chapter.  We can [apply] the constructors to
    prove [<=] goals (e.g., to show that [3<=3] or [3<=6]), and we can
    use tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations. *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H1.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, recommended (total_relation) *)
(** Define an inductive relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  r' : forall n m : nat, total_relation n m.
(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat -> nat -> Prop := .
(** [] *)

(** **** Exercise: 3 stars, recommended (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

- Yes; No.
- No; c5 only guarantees commutativity in the first two components, but the other constructors are already symmetric or dualizable.
- No.
*)
Definition R1 : R 1 1 2 := c3 _ _ _ (c2 _ _ _ c1).
Definition R1' : R 1 1 2 := c2 _ _ _ (c3 _ _ _ c1).
Print R1.
Print R1'.
(*
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
Theorem R_fact : forall m n o, R m n o <-> m + n = o.
Proof.
  split; introv H.
  Case "->".
    induction H.
    SCase "c1". reflexivity.
    SCase "c2". simpl. congruence.
    SCase "c3". rewrite <- plus_n_Sm; congruence.
    SCase "c4".
      inverts IHR as IHR. rewrite <- plus_n_Sm in IHR. inverts IHR. reflexivity.
    SCase "c5".
      subst. apply plus_comm.
  Case "<-".
    subst.
    induction m as [|m']; simpl.
    SCase "m = 0".
      induction n as [|n'].
      SSCase "n = 0". apply c1.
      SSCase "n = S n'". apply c3. assumption.
    SCase "m = S m'". apply c2. assumption.
Qed.
(** [] *)

End R.

(** **** Exercise: 3 stars, recommended (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P []
  | all_cons : forall x l, P x -> all X P l -> all X P (x :: l).

(** Recall the function [forallb], from the exercise
[forall_exists_challenge] in [Poly.v]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

(* Complete specification of forallb. *)
Lemma forallb_all :
  forall X test l, all X (fun x => test x = true) l <-> forallb test l = true.
Proof.
  split; introv H.
  Case "->".
    induction H.
    SCase "H = all_nil". reflexivity.
    SCase "H = all_cons".
      simpl. rewrite H. rewrite IHall. reflexivity.
  Case "<-".
    induction l as [| x l']. 
    SCase "l = []". apply all_nil.
    SCase "l = x :: l'".
      simpl in H.
      assert (H2 : forallb test l' = true).

      SSCase "proof of assertion".
        apply andb_true_elim2 in H. apply H.
      apply IHl' in H2.
      assert (H3 : test x = true).
      SSCase "proof of assertion".
        apply andb_true_elim1 in H. apply H.
      apply all_cons; assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
[[
    [1,4,6,2,3]
]]
    is an in-order merge of
[[
    [1,6,2]
]]
    and
[[
    [4,3].
]]
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive merge_of {X} : list X -> list X -> list X -> Prop :=
  | merge_of_nil : merge_of [] [] []
  | merge_of_l : forall {x l1 l2 l3},
                   merge_of l1 l2 l3 ->
                   merge_of (x :: l1) l2 (x :: l3)
  | merge_of_r : forall {x l1 l2 l3},
                   merge_of l1 l2 l3 ->
                   merge_of l1 (x :: l2) (x :: l3).

Example merge_of_1 : merge_of [1,6,2] [4,3] [1,4,6,2,3].
Proof.
  apply merge_of_l.
  apply merge_of_r.
  repeat (apply merge_of_l).
  apply merge_of_r.
  apply merge_of_nil.
Qed.
Example merge_of_1' : merge_of [1,6,2] [4,3] [1,4,6,2,3] :=
  merge_of_l (merge_of_r (merge_of_l (merge_of_l (merge_of_r merge_of_nil)))).
Print merge_of_1'.
Check filter.

Lemma merge_of_nil_any : forall X (l1 l2 : list X), merge_of [] l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|x1 l1']; introv H.
  Case "l1 = []". inverts H. reflexivity.
  Case "l1 = x1 :: l1'".
    destruct l2 as [|x2 l2'].
    SCase "l2 = []". inverts H.
    SCase "l2 = x2 :: l2'".
      inverts H as H.
      apply IHl1' in H.
      congruence.
Qed.

Theorem filter_spec_challenge :
  forall X (l1 l2 l : list X) test,
    all _ (fun x => test x = true) l1 ->
    all _ (fun x => test x = false) l2 ->
    merge_of l1 l2 l ->
    filter test l = l1.
Proof.
  introv all_l1_t all_l2_f.
  induction all_l1_t; introv merge.

  Case "all_nil".
    inverts merge.
    SCase "merge_of_nil". reflexivity.
    SCase "merge_of_l".
      apply merge_of_nil_any in H. subst.
      induction (x :: l4) as [|x' l'].
      SSCase "x :: l4 = []". reflexivity.
      SSCase "x :: l4 = x' :: l'".
        simpl.
        inverts all_l2_f.
        replace (test x') with false by assumption.
        apply IHl', H2.
      (*
      inverts H.
      SSCase "H = merge_of_nil".
        inverts all_l2_f. simpl.
        replace (test x) with false by assumption. reflexivity.
      SSCase "H = ?".
        (* inverts H0.
        SCase "merge_of_r". *)
        apply merge_of_nil_any in H0. subst. simpl.
        inversion all_l2_f.
        inversion H2. subst.
        replace (test x) with false by assumption.
        replace (test x0) with false by assumption.
*)
  Case "all_cons".

  Restart.

  introv all_l1_t all_l2_f.
  induction l as [|x l']; introv merge.
  Case "l = []". inversion merge. reflexivity.
  Case "l = cons".

  Restart.
  introv all_l1_t all_l2_f.
  induction all_l2_f; introv merge.
  Restart.
  introv.
  generalize dependent l2.
  generalize dependent l1.
  induction l as [|x l']; introv all_l1_t all_l2_f merge.
  Case "l = []". inversion merge. reflexivity.
  Case "l = x :: l'".
    inverts merge.
    SCase "merge_of_l".
      inverts all_l1_t.
      simpl. replace (test x) with true by assumption.
      replace l0 with (filter test l'). reflexivity.
      apply IHl' with (l2 := l2); assumption.
    SCase "merge_of_r".
      inverts all_l2_f.
      simpl.
      replace (test x) with false by assumption.
      apply IHl' with (l2 := l3); assumption.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (*
  introv H.
  inversion H.
  Case "ai_here".
    destruct xs as [|x' xs'].
    SCase "xs = []".
      simpl in H1. subst. right. constructor.
    SCase "xs = x' :: xs'".
      inverts H1. simpl in H. left. constructor.
  Case "ai_later".
    destruct xs as [|x' xs'].
    SCase "xs = []".
      simpl in H. subst. right. assumption.
    SCase "xs = x' :: xs'".
    simpl in H0. inverts H0.
      inverts H1. simpl in H. left. constructor.
   *)
  introv. generalize dependent ys.
  induction xs as [|x' xs']; simpl; introv H.
  Case "xs = []".
    right. assumption.
  Case "xs = x' :: xs'".
    inverts H.
    SCase "left". left. constructor.
    SCase "right".
      apply IHxs' in H1.
      destruct H1.
      SSCase "left".
        left. constructor. assumption.
      SSCase "right".
        right. assumption.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  introv H. destruct H.
  Case "appears_in x xs".
    induction xs as [|x' xs']; simpl.
    SCase "xs = []". inversion H.
    SCase "xs = x' :: xs'".
      inverts H; constructor.
      SSCase "x <> x'".
        apply IHxs', H1.
  Case "appears_in x ys".
    induction xs; simpl; [| constructor]; assumption.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)
Check all.
Definition disjoint {X} (l1 l2 : list X) := all _ (fun x => ~(appears_in x l2)) l1.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {X} : list X -> Prop :=
  | nr_nil : no_repeats []
  | nr_cons : forall x l, ~(appears_in x l) -> no_repeats l -> no_repeats (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Lemma disjoint_distr :
  forall X x (l1 l2 : list X),
    disjoint (x :: l1) l2 -> disjoint l1 l2.
Proof.
  unfold disjoint. introv H. inverts H. assumption.
Qed.

Lemma foo : forall X x (l1 l2 : list X), appears_in x (l1 ++ l2) -> no_repeats (x :: l1) -> appears_in x l2.
Proof.
  introv Happ Hnr.
  induction l1; simpl in Happ.
  assumption.
  apply IHl1; clear IHl1.
  Case "1".
    inverts Happ.
    SCase "1".
      inverts Hnr. apply ex_falso_quodlibet, H1. constructor.
    SCase "2".
      assumption.
  Case "2".
    inverts Hnr. constructor.
    SCase "1".
      unfold not in *. intro H. apply H1. constructor. assumption.
    SCase "2". inverts H2. assumption.
Qed.
  (*
  inverts Happ as Happ.
  Case "1".
    destruct l1 as [|x' l1'].
    SCase "l1 = []".
      simpl in Happ. subst. constructor.
    SCase "l1 = x' :: l1'".
      simpl in Happ. inverts Happ. inverts Hnr.
      apply ex_falso_quodlibet.
      apply H1. constructor.
  Case "2".
    destruct l1 as [|x' l1'].
    SCase "l1 = []".
      simpl in H0. subst. constructor. assumption.
    SCase "l1 = x' :: l1'".
      simpl in H0. inverts H0.*)

Theorem no_r_distr :
  forall X (l1 l2 : list X), disjoint l1 l2 -> no_repeats l1 -> no_repeats l2 ->
                             no_repeats (l1 ++ l2).
Proof.
  introv disj nr_l1 nr_l2.
  induction l1; simpl. assumption.
  constructor.
  Case "1st hp".
    inverts disj.
    intro H. apply foo in H. 2: apply nr_l1. apply H1 in H. assumption.
    (* inversion H.
    unfold not in H1. *)
  Case "2nd hp".
    apply IHl1.
    apply disjoint_distr in disj. apply disj.
    inverts nr_l1. assumption.
Qed.

(** [] *)

(* ######################################################### *)
(** ** Digression: More Facts about [<=] and [<] *)

(** Let's pause briefly to record several facts about the [<=]
    and [<] relations that we are going to need later in the
    course.  The proofs make good practice exercises. *)

Print le.
(* Inductive le (n : nat) : nat -> Prop := *)
(*     le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n; constructor. assumption.
Qed.

Check le_ind.
(* le_ind *)
(*      : forall (n : nat) (P : nat -> Prop), *)
(*        P n -> *)
(*        (forall m : nat, n <= m -> P m -> P (S m)) -> *)
(*        forall n0 : nat, n <= n0 -> P n0 *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  introv H. induction H as [|m' H].
  constructor.
  constructor. assumption.
Restart.
  intro n. apply le_ind.
  constructor.
  intros. constructor. assumption.
  (*
  generalize dependent n.
  induction m as [|m']. intros. inversion H. constructor.
  intros.
   *)
  (*
  generalize dependent m.
  induction n as [|n'].

  induction m. constructor. constructor. apply IHm. apply O_le_n.

  induction m as [|m']; introv H. inversion H.
  constructor.
  apply IHm'. 
   *)
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m. 
    introv H. inversion H.
      constructor.

      inversion H1.

    introv H. inverts H.
      constructor.

      inverts H1.
        repeat constructor.

        constructor. apply IHm. constructor. assumption.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  induction a as [|a'].
  apply O_le_n.
  simpl.
  introv.

Restart.
  induction b as [|b'].
  rewrite plus_0_r. constructor.

  rewrite <- plus_n_Sm. constructor.
  assumption.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  split.

  Case "n1 < m".
    unfold lt in *.
    induction m as [|m'].
    SCase "m = 0". inversion H.

    SCase "m = S m'".
      inverts H.
      SSCase "1".
        clear IHm'.
        induction n2 as [|n2'].
        SSSCase "n2 = 0".
          rewrite plus_0_r. constructor.
        SSSCase "n2 = S n2'".
          rewrite <- plus_n_Sm. constructor. apply IHn2'.
      SSCase "2".
        constructor. apply IHm', H1.
  Case "n2 < m".
    unfold lt in *.
    induction m as [|m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'".
      inverts H.
      SSCase "1".
        clear IHm'.
        induction n1 as [|n1']; simpl; constructor; assumption.
      SSCase "2".
        constructor. apply IHm'. assumption. Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. constructor. assumption. Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  induction n.
    intros. apply O_le_n.

    intros. destruct m.
      inversion H.

      simpl in H.
      apply n_le_m__Sn_le_Sm. apply IHn. assumption. Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  induction n as [|n']; introv H.
  Case "n = 0".
    inversion H.
  Case "n = S n'".
    inverts H. rewrite H1.
    destruct m; simpl. reflexivity.
    apply IHn'. assumption.
Qed.

SearchAbout ble_nat.
(* test_ble_nat1: ble_nat 2 2 = true *)
(* test_ble_nat2: ble_nat 2 4 = true *)
(* test_ble_nat3: ble_nat 4 2 = false *)
(* ble_nat_refl: forall n : nat, true = ble_nat n n *)
(* plus_ble_compat_l: *)
(*   forall n m p : nat, ble_nat n m = true -> ble_nat (p + n) (p + m) = true *)
(* NatList.count_member_nonzero: *)
(*   forall s : NatList.bag, *)
(*   ble_nat 1 (NatList.count 1 (NatList.cons 1 s)) = true *)
(* NatList.ble_n_Sn: forall n : nat, ble_nat n (S n) = true *)
(* NatList.remove_decreases_count: *)
(*   forall s : NatList.bag, *)
(*   ble_nat (NatList.count 0 (NatList.remove_one 0 s)) (NatList.count 0 s) = *)
(*   true *)
(* ble_nat_n_Sn_false: *)
(*   forall n m : nat, ble_nat n (S m) = false -> ble_nat n m = false *)
(* ble_nat_true: forall n m : nat, ble_nat n m = true -> n <= m *)

SearchAbout le.
(* ble_nat_true: forall n m : nat, ble_nat n m = true -> n <= m *)
(* le_plus_l: forall a b : nat, a <= a + b *)
(* Sn_le_Sm__n_le_m: forall n m : nat, S n <= S m -> n <= m *)
(* n_le_m__Sn_le_Sm: forall n m : nat, n <= m -> S n <= S m *)
(* O_le_n: forall n : nat, 0 <= n *)
(* test_le3: ~ 2 <= 1 *)
(* test_le2: 3 <= 6 *)
(* test_le1: 3 <= 3 *)
(* le_ind: *)
(*   forall (n : nat) (P : nat -> Prop), *)
(*   P n -> *)
(*   (forall m : nat, n <= m -> P m -> P (S m)) -> *)
(*   forall n0 : nat, n <= n0 -> P n0 *)
(* le_n: forall n : nat, n <= n *)
(* le_S: forall n m : nat, n <= m -> n <= S m *)

Lemma le_Sn_m_remove_S : forall n m, S n <= m -> n <= m.
Proof.
  introv H.
  induction H. repeat constructor.
  constructor; assumption.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)
  unfold not.
  introv H nm.
  induction m as [|m'].
  Case "m = 0".
    inverts nm. inverts H.
  Case "m = S m'".
    destruct n as [|n']; inverts H.
    SCase "n = S n'".
      inverts nm.
        rewrite <- ble_nat_refl in H1. inverts H1.

        apply IHm', H0.
Restart.
  unfold not.
  introv H nm.
  generalize dependent m.
  induction n as [|n'].
  Case "m = 0". intros. inverts H.
  Case "m = S m'".
    intros.
    destruct m.
      inverts nm.

      inverts nm.
        rewrite <- ble_nat_refl in H. inverts H.

        inverts H as H.

        (* inverts H1. apply ble_nat_n_Sn_false in H.
        rewrite <- ble_nat_refl in H. inverts H. *)
        apply IHn' with (m := m). assumption.
        SearchAbout le.
        clear H IHn'.

        simpl.
        apply le_Sn_m_remove_S, H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (nostutter) *)
(** Formulating inductive definitions of predicates is an important skill
    you'll need in this course.

    Try to solve this exercise without any help at all.   If you do receive 
    assistance from anyone, please say so specifically in a comment.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.)
*)

Inductive nostutter:  list nat -> Prop :=
  | ns_nil : nostutter nil
  | ns_single : forall x, nostutter [x]
  | ns_cons : forall x1 x2 l, x1 <> x2 -> nostutter (x2 :: l) -> nostutter (x1 :: x2 :: l).

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
Proof. repeat constructor; apply beq_false_not_eq; reflexivity. Qed.
(* 
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; reflexivity. Qed.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, optional (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas... (we already proved this for lists
    of naturals, but not for arbitrary lists.) *)

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof.
  induction l1; simpl; try reflexivity.
  intros.
  rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction l; inverts H.
  exists (@nil X). exists l. reflexivity.
  apply IHl in H1. clear IHl.
  destruct H1 as [l1' [l2' H2]].
  subst.
  exists (x0 :: l1'). exists l2'.
  reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rp_base : forall x l, appears_in x l -> repeats (x :: l)
  | rp_cons : forall x l, repeats l -> repeats (x :: l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.
  intros X l1. induction l1; simpl.

  introv H0 H1 H2. inversion H2.

  introv excl H1 H2.
  assert (Hcases := excl (repeats (x :: l1))).
  inverts Hcases.
    assumption.
    
    (* unfold not in *.
    apply ex_falso_quodlibet. *)
    assert (Happ : appears_in x (x :: l1)). constructor.
    apply (H1 x) in Happ.
    assert (Hlemma: (forall x : X, appears_in x l1 -> appears_in x l2)).
    introv Happears.
    assert (Hcases := excl (x = x0)).
    inverts Hcases.
      assumption.

      Print appears_in.
(* Inductive appears_in (X : Type) (a : X) : list X -> Prop := *)
(*     ai_here : forall l : list X, appears_in a (a :: l) *)
(*   | ai_later : forall (b : X) (l : list X), *)
(*                appears_in a l -> appears_in a (b :: l) *)

(* For appears_in: Argument X is implicit and maximally inserted *)
(* For ai_here: Argument X is implicit and maximally inserted *)
(* For ai_later: Argument X is implicit and maximally inserted *)
(* For appears_in: Argument scopes are [type_scope _ _] *)
(* For ai_here: Argument scopes are [type_scope _ _] *)
(* For ai_later: Argument scopes are [type_scope _ _ _ _] *)
      apply (ai_later x0 x l1) in Happears. apply H1, Happears.

      induction l2.
      inversion Happ. simpl in *. inversion H2.

        apply Sn_le_Sm__n_le_m in H2.
        apply IHl2. 
        (* introv x1inl1.
        inverts x1inl1.
          admit. 
        apply Hlemma. *)
          admit.
          rewrite <- H3.
          constructor. constructor.
          admit.

          assert (Hcases2 := excl (x = x0)).
          inverts Hcases2.
          introv xInL1.
      (* inverts H2.
        SSCase "length l2 = length l1".
        assert (Hlemma2: appears_in x l1).
Lemma Hlemma2: forall {X} (x : X) l1 l2, length l1 = length l2 -> 
    (forall x : X, appears_in x l1 -> appears_in x l2) -> appears_in x l2 ->
    appears_in x l1. Admitted.


        admit.
        constructor. apply Hlemma2.
        SSCase "length l2 < length l1".
        apply rp_cons. apply IHl1 with (l2 := l2); assumption. *)
Qed.
(** [] *)

(* ##################################################### *)
(** * Optional Material *)

(* ################################################### *)
(** ** Induction Principles for [/\] and [\/] *)

(** The induction principles for conjunction and disjunction are a
    good illustration of Coq's way of generating simplified induction
    principles for [Inductive]ly defined propositions, which we
    discussed in the last chapter.  You try first: *)

(** **** Exercise: 1 star (and_ind_principle) *)
(** See if you can predict the induction principle for conjunction. *)

(* Check and_ind. *)
(** [] *)

(** **** Exercise: 1 star (or_ind_principle) *)
(** See if you can predict the induction principle for disjunction. *)

(* Check or_ind. *)
(** [] *)

Check and_ind.

(** From the inductive definition of the proposition [and P Q]
[[
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
    we might expect Coq to generate this induction principle
[[
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
]]
    but actually it generates this simpler and more useful one:
[[
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
]]
    In the same way, when given the inductive definition of [or P Q]
[[
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
]]
    instead of the "maximal induction principle"
[[
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
]]
    what Coq actually generates is this:
[[
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]] 
*)

(* ######################################################### *)
(** ** Explicit Proof Objects for Induction *)


(** Although tactic-based proofs are normally much easier to
    work with, the ability to write a proof term directly is sometimes
    very handy, particularly when we want Coq to do something slightly
    non-standard.  *)
    
(** Recall the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)

(* Check nat_ind. *)
(* ===> 
   nat_ind : forall P : nat -> Prop,
      P 0%nat -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n  *)

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)
 
Print nat_ind.  Print nat_rect.
(* ===> (after some manual inlining)
   nat_ind =
    fun (P : nat -> Type) 
        (f : P 0%nat) 
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n as n0 return (P n0) with
            | 0%nat => f
            | S n0 => f0 n0 (F n0)
            end.
*)

(** We can read this as follows: 
     Suppose we have evidence [f] that [P] holds on 0,  and 
     evidence [f0] that [forall n:nat, P n -> P (S n)].  
     Then we can prove that [P] holds of an arbitrary nat [n] via 
     a recursive function [F] (here defined using the expression 
     form [Fix] rather than by a top-level [Fixpoint] 
     declaration).  [F] pattern matches on [n]: 
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0] 
         to obtain evidence that [P n0] holds; then it applies [f0] 
         on that evidence to show that [P (S n)] holds. 
    [F] is just an ordinary recursive function that happens to 
    operate on evidence in [Prop] rather than on terms in [Set].
 
    Aside to those interested in functional programming: You may
    notice that the [match] in [F] requires an annotation [as n0
    return (P n0)] to help Coq's typechecker realize that the two arms
    of the [match] actually return the same type (namely [P n]).  This
    is essentially like matching over a GADT (generalized algebraic
    datatype) in Haskell.  In fact, [F] has a _dependent_ type: its
    result type depends on its argument; GADT's can be used to
    describe simple dependent types like this.
 
    We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too.  Recall our desire to
    prove that

    [forall n : nat, even n -> ev n].
 
    Attempts to do this by standard induction on [n] fail, because the
    induction principle only lets us proceed when we can prove that
    [even n -> even (S n)] -- which is of course never provable.  What
    we did earlier in this chapter was a bit of a hack:
 
    [Theorem even_ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].
 
    We can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 
 *)
 
 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n return P n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                          end.
 
 (** Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive (try
     it!).

     The [induction ... using] tactic gives a convenient way to
     specify a non-standard induction principle like this. *)
 
Lemma even_ev' : forall n, even n -> ev n.
Proof. 
 intros.  
 induction n as [ | |n'] using nat_ind2. 
  Case "even 0". 
    apply ev_0.  
  Case "even 1". 
    inversion H.
  Case "even (S(S n'))". 
    apply ev_SS. 
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H. 
Qed. 

(* ######################################################### *)
(** ** The Coq Trusted Computing Base *)

(** One issue that arises with any automated proof assistant is "why
    trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard Correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on.

    There are a few additional wrinkles:

    - Since Coq types can themselves be expressions, the checker must
      normalize these (by using the conversion rules) before
      comparing them.

    - The checker must make sure that [match] expressions are
      _exhaustive_.  That is, there must be an arm for every possible
      constructor.  To see why, consider the following alleged proof
      object:
[[
      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end. 
]]
      All the types here match correctly, but the [match] only
      considers one of the possible constructors for [or].  Coq's
      exhaustiveness check will reject this definition.

    - The checker must make sure that each [fix] expression
      terminates.  It does this using a syntactic check to make sure
      that each recursive call is on a subexpression of the original
      argument.  To see why this is essential, consider this alleged
      proof:
[[
          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n. 
]]
      Again, this is perfectly well-typed, but (fortunately) Coq will
      reject it. *)

(** Note that the soundness of Coq depends only on the correctness of
    this typechecking engine, not on the tactic machinery.  If there
    is a bug in a tactic implementation (and this certainly does
    happen!), that tactic might construct an invalid proof term.  But
    when you type [Qed], Coq checks the term for validity from
    scratch.  Only lemmas whose proofs pass the type-checker can be
    used in further proof developments.  *)


