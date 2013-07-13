(** * Prop: Propositions and Evidence *)

(* $Date: 2011-06-27 09:22:51 -0400 (Mon, 27 Jun 2011) $ *)

(** "_Algorithms are the computational content of proofs_." (Robert
    Harper) *)

Require Export Poly.

(* ##################################################### *)
(* ##################################################### *)
(** * Programming with Propositions *)

(** _Note to readers_: Some of the concepts in this chapter may
    seem quite abstract on a first encounter.  We've included a _lot_
    of exercises, most of which should be quite approachable even if
    you're still working on understanding the details of the text.
    Try to work as many of them as you can, especially the one-starred
    exercises. *)

(** So far, the only statements we have been able to state and
    prove have been in the form of _equalities_.  However, the
    language of mathematical statements and proofs is much richer than
    this!  In this chapter we will take a much closer and more
    fundamental look at the sorts of mathematical statements
    (_propositions_) we can make in Coq, and how we go about proving
    them by providing logical _evidence_. *)

(** A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't mentioned it
    explicitly, we have already seen numerous examples. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** We've seen one way that propositions can be used in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts (numbers,
    functions, types, type functions, ...). *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** Now we can use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem]
    declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** So far, all the propositions we have seen are equality
    propositions.  We can also form new propositions out of old
    ones.  For example, given propositions [P] and [Q], we can form
    the proposition "[P] implies [Q]." *)

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

(** Also, given a proposition [P] with a free variable [n], we can
    form the proposition [forall n, P]. *)

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

(** Finally, we can define _parameterized propositions_.  For
    example, what does it mean to claim that "a number n is even"?  We
    have written a function that tests evenness, so one possible
    definition of what it means to be even is "[n] is even iff [evenb
    n = true]." *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** This defines [even] as a _function_ that, when applied to a number
    [n], _yields a proposition_ asserting that [n] is even.  *)

Check even. 
(* ===> even : nat -> Prop *)
Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)

(** The type of [even], [nat->Prop], can be pronounced in three
    ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  We can use them in other
    definitions: *)

Definition even_n__even_SSn (n:nat) : Prop := 
  (even n) -> (even (S (S n))).

(** We can define them to take multiple arguments... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P:nat->Prop) (n:nat) : Prop :=
  P n -> P (S n).

(** (Names of the form [x__y], with two underscores in a row, can be
    read "[x] implies [y].") *)

(** Here are two more examples of passing parameterized
    propositions as arguments to a function.  The first makes the
    claim that a whenever a proposition [P] is true for some natural
    number [n'], it is also true by the successor of [n']: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** And this one simply claims that a proposition is true for
    all natural numbers: *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** We can put these pieces together to manually restate the
    principle of induction for natural numbers.  Given a parameterized
    proposition [P], if [P] is true for [0], and [P (S n')] is true
    whenever [P n'] is, then [P] is true for all natural numbers. *)

Definition our_nat_induction (P:nat->Prop) : Prop :=
     (true_for_zero P) ->
     (preserved_by_S P) ->
     (true_for_all_numbers P).

(* ##################################################### *)
(** * Evidence *)

(** We've seen that well-formed expressions of type [Prop] can
    embody both provable and unprovable propositions.  Naturally,
    we're particularly interested in the provable ones.  When [P] is a
    proposition and [e] is a proof of [P] -- i.e., [e] is evidence
    that [P] is true -- we'll write "[e : P]."  This overloading of
    the "has type" or "inhabits" notation is not accidental: we'll see
    that there is a fundamental and fruitful analogy between data
    values inhabiting types and evidence "inhabiting" propositions. *)

(** The next question is "what are proofs?" -- i.e., what sorts of
    things would we be willing to accept as evidence that particular
    propositions are true? *)

(* ##################################################### *)
(** ** Inductively Defined Propositions *)

(** The answer, of course, depends on the form of the
    proposition -- evidence for implication propositions ([P->Q]) is
    different from evidence for conjunctions ([P/\Q]), etc.  In this
    chapter and the next, we'll address a number of specific cases.

    To begin with, consider _atomic_ propositions -- ones that aren't
    built into the logic we're using, but are rather introduced to
    model useful concepts in a particular domain.  For example, having
    defined a type [day] as we did in Basics.v, we might have some
    concept in our minds about certain days, say the fact that
    [saturday] and [sunday] are "good" ones.  If we want to use Coq to
    state and prove theorems involving good days, we need to begin by
    telling it what we mean by "good" -- that is, we need to specify
    what counts as as evidence that some day [d] is good (namely, that
    [d] is either [saturday] or [sunday].  The following declaration
    achieves this: *)

Inductive good_day : day -> Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.

(** The [Inductive] keyword means exactly the same thing whether
    we are using it to define sets of data values (in the [Type]
    world) or sets of evidence (in the [Prop] world).  Consider the
    parts of the definition above:

    - The first line declares that [good_day] is a proposition indexed
      by a day.

    - The second line declares that the constructor [gd_sat] can be
      taken as evidence for the assertion [good_day saturday].

    - The third line declares that the constructor [gd_sun] can be
      taken as evidence for the assertion [good_day sunday]. *)

(** That is, we're _defining_ what we mean by days being good by
    saying "Saturday is good, sunday is good, and that's all."  Then
    someone can _prove_ that Sunday is good simply by observing that
    we said it was when we defined what [good_day] meant. *)

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

(** The constructor [gd_sun] is "primitive evidence" -- an _axiom_ --
    justifying the claim that Sunday is good. *)

(** Similarly, we can define a proposition [day_before]
    parameterized by _two_ days, together with axioms stating that
    Monday comes before Tuesday, Tuesday before Wednesday, and so
    on. *)

Inductive day_before : day -> day -> Prop := 
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

(** The axioms that we introduce along with an inductively
    defined proposition can also involve universal quantifiers.  For
    example, it is well known that _every_ day is a fine day for
    singing a song: *)

Inductive fine_day_for_singing : day -> Prop := 
  | fdfs_any : forall d:day, fine_day_for_singing d.

(** The line above declares that, if [d] is a day, then [fdfs_any d]
    can be taken as evidence for [fine_day_for_singing d].  That is,
    we can construct evidence that [d] is a [fine_day_for_singing]
    by applying the constructor [fdfs_any] to [d].

    In particular, Wednesday is a fine day for singing. *)

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

(** As always, the first line here can be read "I'm about to
    show you some evidence for the proposition [fine_day_for_singing
    wednesday], and I want to introduce the name [fdfs_wed] to refer
    to that evidence later on."  The second line then instructs Coq
    how to assemble the evidence. *)

(* ##################################################### *)
(** ** Proof Objects *)

(** There's another -- more primitive -- way to accomplish the
    same thing: we can use a [Definition] whose left-hand side is the
    name we're introducing and whose right-hand side is the evidence
    _itself_, rather than a script for how to build it.  *)

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

(** The expression [fdfs_any wednesday] can be thought of as
    instantiating the parameterized axiom [fdfs_any] with the specific
    argument [wednesday].  Alternatively, we can think of [fdfs_any]
    as a primitive "evidence constructor" that, when applied to a
    particular day, stands as evidence that that day is a fine day for
    singing; its type, [forall d:day, fine_day_for_singing d],
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] in the previous chapter expressed the fact
    that the constructor [nil] can be thought of as a function from
    types to empty lists with elements of that type. *)

(** Let's take a slightly more interesting example.  Let's say
    that a day of the week is "ok" if either (1) it is a good day or
    else (2) it falls the day before an ok day. *)

Inductive ok_day : day -> Prop := 
  | okd_gd : forall d, 
      good_day d -> 
      ok_day d 
  | okd_before : forall d1 d2, 
      ok_day d2 -> 
      day_before d2 d1 -> 
      ok_day d1.

(** The first constructor can be read "One way to show that [d]
    is an ok day is to present evidence that [d] is good."  The second
    can be read, "Another way to show that a day [d1] is ok is to
    present evidence that it is the day before some other day [d2]
    together with evidence that [d2] is ok." *)

(** Now suppose that we want to prove that [wednesday] is ok.
    There are two ways to do it.  First, we have the primitive way,
    where we simply write down an expression that has the right
    type -- a big nested application of constructors: *)

Definition okdw : ok_day wednesday := 
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday 
         (okd_gd saturday gd_sat) 
         db_sat) 
       db_fri)
    db_thu.

(** Second, we have the machine-assisted way, where we go into [Proof]
    mode and Coq guides us through a series of goals and subgoals
    until it is finally satisfied: *)

Theorem okdw' : ok_day wednesday.
Proof. 
  (* wednesday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=thursday). 
  (* "subgoal: show that thursday is ok". *)
    (* thursday is OK because it's the day before an OK day *)
    apply okd_before with (d2:=friday).
    (* "subgoal: show that friday is ok". *)
      (* friday is OK because it's the day before an OK day *)
      apply okd_before with (d2:=saturday).
        (* "subgoal: show that saturday is ok". *)
          (* saturday is OK because it's good! *)
          apply okd_gd. apply gd_sat.
        (* "subgoal: show that the day before saturday is friday". *)
          apply db_sat.
    (* "subgoal: show that the day before friday is thursday". *)
      apply db_fri.
  (* "subgoal: show that the day before thursday is wednesday". *)
  apply db_thu. Qed.

(** Fundamentally, though, these two ways of making proofs are the
    same, in the sense that what Coq is actually doing when it's
    following the commands in a [Proof] script is _literally_
    attempting to construct an expression with the desired type. *)

Print okdw'.
(* ===> okdw' = okd_before wednesday thursday
                  (okd_before thursday friday
                    (okd_before friday saturday 
                      (okd_gd saturday gd_sat) db_sat) 
                    db_fri)
                  db_thu
              : ok_day wednesday *)

(** These expressions are often called _proof objects_. *)

(** Proof objects are the bedrock of Coq.  Tactic proofs are
    essentially _programs_ that instruct Coq how to construct proof
    objects for us instead of our writing them out explicitly.  Here,
    of course, the proof object is actually shorter than the tactic
    proof.  But the proof objects for more interesting proofs can
    become quite large and complex -- building them by hand would be
    painful.  Moreover, we'll see later on in the course that Coq has
    a number of automation tactics that can construct quite complex
    proof objects without our needing to specify every step. *)

(* ##################################################### *)
(** ** The Curry-Howard Correspondence *)

(** The analogy 
<<
                 propositions  ~  sets / types
                 proofs        ~  data values 
>>
    is called the _Curry-Howard correspondence_ (or _Curry-Howard
    isomorphism_).  Many wonderful things follow from it. *)

(** Just as a set can be empty, a singleton, finite, or infinite -- it
    can have zero, one, or many inhabitants -- a proposition may be
    inhabited by zero, one, many, or infinitely many proofs.  Each
    inhabitant of a proposition [P] is a different way of giving
    evidence for [P].  If there are none, then [P] is not provable.
    If there are many, then [P] has many different proofs. *)

(* ##################################################### *)
(** ** Implication *)

(** We've seen that the [->] operator (implication) builds bigger
    propositions from smaller ones.  What constitutes evidence for
    propositions built in this way?  Consider this statement: *)

Definition okd_before2 := forall d1 d2 d3, 
  ok_day d3 -> 
  day_before d2 d1 -> 
  day_before d3 d2 -> 
  ok_day d1.  

(** In English: if we have three days, [d1] which is before [d2]
    which is before [d3], and if we know [d3] is ok, then so is
    [d1]. 

    It should be easy to see how we'd construct a tactic proof of
    [okd_before2]... *)
Require Import LibTactics.
(** **** Exercise: 1 star, optional (okd_before2_valid) *)
Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
(* okd_before *)
(*      : forall d1 d2 : day, ok_day d2 -> day_before d2 d1 -> ok_day d1 *)
  introv H H0 H1.
  generalize dependent H0.
  apply okd_before.
  generalize dependent H1.
  generalize dependent H.
  apply okd_before.
  Restart.
  unfold okd_before2. introv H H0 H1.
  apply okd_before with (d2 := d2);
    [ apply okd_before with (d1 := d2) (d2 := d3) | ]; assumption.
Qed.
(** [] *)

(** But what should the corresponding proof object look like? 

    Answer: We've made a notational pun between [->] as implication
    and [->] as the type of functions.  If we take this pun seriously,
    then what we're looking for is an expression with _type_ [forall
    d1 d2 d3, ok_day d3 -> day_before d2 d1 -> day_before d3 d2 ->
    ok_day d1], and so what we want is a _function_ that takes six
    arguments (three days and three pieces of evidence) and returns a
    piece of evidence!  Here it is: *)

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) => 
  fun (H : ok_day d3) => 
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

(** **** Exercise: 1 star, optional (okd_before2_valid_defn) *)
(** Predict what Coq will print in response to this: *)

Print okd_before2_valid.

(* ##################################################### *)
(** ** Induction Principles for Inductively Defined Types *)

(** Every time we declare a new [Inductive] datatype, Coq
    automatically generates an axiom that embodies an _induction
    principle_ for this type.

    The induction principle for a type [t] is called [t_ind].  Here is
    the one for natural numbers: *)

Check nat_ind.
(*  ===> nat_ind : forall P : nat -> Prop,
                      P 0  ->
                      (forall n : nat, P n -> P (S n))  ->
                      forall n : nat, P n  *)

(** Note that this is exactly the [our_nat_induction] property from
    above. *)

(** The [induction] tactic is a straightforward wrapper that, at
    its core, simply performs [apply t_ind].  To see this more
    clearly, let's experiment a little with using [apply nat_ind]
    directly, instead of the [induction] tactic, to carry out some
    proofs.  Here, for example, is an alternate proof of a theorem
    that we saw in the [Basics] chapter. *)

Theorem mult_0_r' : forall n:nat, 
  n * 0 = 0.
Proof.
  apply nat_ind. 
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn. 
    reflexivity.  Qed.

(** This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.  First, in the induction
    step of the proof (the ["S"] case), we have to do a little
    bookkeeping manually (the [intros]) that [induction] does
    automatically.

    Second, we do not introduce [n] into the context before applying
    [nat_ind] -- the conclusion of [nat_ind] is a quantified formula,
    and [apply] needs this conclusion to exactly match the shape of
    the goal state, including the quantifier.  The [induction] tactic
    works either with a variable in the context or a quantified
    variable in the goal.

    Third, the [apply] tactic automatically chooses variable names for
    us (in the second subgoal, here), whereas [induction] lets us
    specify (with the [as...]  clause) what names should be used.  The
    automatic choice is actually a little unfortunate, since it
    re-uses the name [n] for a variable that is different from the [n]
    in the original theorem.  This is why the [Case] annotation is
    just [S] -- if we tried to write it out in the more explicit form
    that we've been using for most proofs, we'd have to write [n = S
    n], which doesn't make a lot of sense!  All of these conveniences
    make [induction] nicer to use in practice than applying induction
    principles like [nat_ind] directly.  But it is important to
    realize that, modulo this little bit of bookkeeping, applying
    [nat_ind] is what we are really doing. *)

(** **** Exercise: 2 stars (plus_one_r') *)
(** Complete this proof without using the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat, 
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. introv H. rewrite H. reflexivity.
Qed.
(** [] *)

(** The induction principles that Coq generates for other
    datatypes defined with [Inductive] follow a similar pattern. If we
    define a type [t] with constructors [c1] ... [cn], Coq generates a
    theorem with this shape:
[[
    t_ind :
       forall P : t -> Prop,
            ... case for c1 ... ->
            ... case for c2 ... ->
            ...                 ->
            ... case for cn ... ->
            forall n : t, P n
]]
    The specific shape of each case depends on the arguments to the
    corresponding constructor.  Before trying to write down a general
    rule, let's look at some more examples. First, an example where
    the constructors take no arguments: *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind. 
(* ===> yesno_ind : forall P : yesno -> Prop, 
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** Exercise: 1 star (rgb) *)
(** Write out the induction principle that Coq will generate for
    the following datatype.  Write down your answer on paper, and
    then compare it with what Coq prints. *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
(* rgb_ind : forall P : rgb -> Prob, P red -> P green -> P blue ->
forall r : rgb, P r *)
Check rgb_ind.

(** [] *)

(** Here's another example, this time with one of the constructors
    taking some arguments. *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (modulo a little tidying)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist), P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** Exercise: 1 star (natlist1) *)
(** Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? *)
(* ===> (modulo a little tidying)
   natlist1_ind :
      forall P : natlist1 -> Prop,
         P nnil1  ->
         (forall (l : natlist1) (n : nat), P l -> P (nsnoc1 l n)) ->
         forall n : natlist1, P n *)
Check natlist1_ind.
(* natlist1_ind *)
(*      : forall P : natlist1 -> Prop, *)
(*        P nnil1 -> *)
(*        (forall l : natlist1, P l -> forall n : nat, P (nsnoc1 l n)) -> *)
(*        forall n : natlist1, P n *)

(** [] *)

(** From these examples, we can extract this general rule:

    - The type declaration gives several constructors; each
      corresponds to one clause of the induction principle.
    - Each constructor [c] takes argument types [a1]...[an].
    - Each [ai] can be either [t] (the datatype we are defining) or
      some other type [s].
    - The corresponding case of the induction principle
      says (in English):
        - "for all values [x1]...[xn] of types [a1]...[an], if
           [P] holds for each of the [x]s of type [t], then [P]
           holds for [c x1 ... xn]". *)

(** **** Exercise: 1 star (ExSet) *)
(** Here is an induction principle for an inductively defined
    set.
[[
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
]]
    Give an [Inductive] definition of [ExSet]: *)

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

(** [] *)

(** What about polymorphic datatypes?

    The inductive definition of polymorphic lists
[[
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
]]
    is very similar to that of [natlist].  The main difference is
    that, here, the whole definition is _parameterized_ on a set [X]:
    that is, we are defining a _family_ of inductive types [list X],
    one for each [X].  (Note that, wherever [list] appears in the body
    of the declaration, it is always applied to the parameter [X].)
    The induction principle is likewise parameterized on [X]:
[[
     list_ind :
       forall (X : Type) (P : list X -> Prop),
          P [] ->
          (forall (x : X) (l : list X), P l -> P (x :: l)) ->
          forall l : list X, P l
]]
   Note the wording here (and, accordingly, the form of [list_ind]):
   The _whole_ induction principle is parameterized on [X].  That is,
   [list_ind] can be thought of as a polymorphic function that, when
   applied to a type [X], gives us back an induction principle
   specialized to the type [list X]. *)

(** **** Exercise: 1 star (tree) *)
(** Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
(* tree_ind :
  forall X (P : tree X -> Prop),
    (forall x : X, P (leaf X x)) ->
    (forall t1 : tree X, P t1 -> forall t2 : tree X, P t2 -> P (node X t1 t2)) ->
    forall t : tree X, P t. *)
Check tree_ind.
(* tree_ind *)
(*      : forall (X : Type) (P : tree X -> Prop), *)
(*        (forall x : X, P (leaf X x)) -> *)
(*        (forall t : tree X, P t -> forall t0 : tree X, P t0 -> P (node X t t0)) -> *)
(*        forall t : tree X, P t *)
(** [] *)

(** **** Exercise: 1 star (mytype) *)
(** Find an inductive definition that gives rise to the
    following induction principle:
[[
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m -> 
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m                   
]]
*)
Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.
Check mytype_ind.
(* mytype_ind *)
(*      : forall (X : Type) (P : mytype X -> Prop), *)
(*        (forall x : X, P (constr1 X x)) -> *)
(*        (forall n : nat, P (constr2 X n)) -> *)
(*        (forall m : mytype X, P m -> forall n : nat, P (constr3 X m n)) -> *)
(*        forall m : mytype X, P m *)
(** [] *)

(** **** Exercise: 1 star, optional (foo) *)
(** Find an inductive definition that gives rise to the
    following induction principle:
[[
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2       
]]
*)
Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.
(** [] *)

(** **** Exercise: 1 star, optional (foo') *)
(** Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)
[[
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ -> //P f 
                    _______________________   ) -> //P (C1 X l f)
             ___________________________________________ -> P (C2 X)
             forall f : foo' X, ________________________ // P f
]]
*)
Check foo'_ind.
(* foo'_ind *)
(*      : forall (X : Type) (P : foo' X -> Prop), *)
(*        (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) -> *)
(*        P (C2 X) -> forall f1 : foo' X, P f1 *)

(** [] *)

(* ##################################################### *)
(** ** Induction Hypotheses *)

(** Where does the phrase "induction hypothesis" fit into this
    picture?  

    The induction principle for numbers
[[
       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n
]]
   is a generic statement that holds for all propositions
   [P] (strictly speaking, for all families of propositions [P]
   indexed by a number [n]).  Each time we use this principle, we
   are choosing [P] to be a particular expression of type
   [nat->Prop].

   We can make the proof more explicit by giving this expression a
   name.  For example, instead of stating the theorem [mult_0_r] as
   "[forall n, n * 0 = 0]," we can write it as "[forall n, P_m0r
   n]", where [P_m0r] is defined as... *)

Definition P_m0r (n:nat) : Prop := 
  n * 0 = 0.

(** ... or equivalently... *)

Definition P_m0r' : nat->Prop := 
  fun n => n * 0 = 0.

(** Now when we do the proof it is easier to see where [P_m0r]
    appears. *)

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* Note the proof state at this point! *)
    unfold P_m0r. simpl. intros n' IHn'. 
    apply IHn'.  Qed.

(** This extra naming step isn't something that we'll do in
    normal proofs, but it is useful to do it explicitly for an example
    or two, because it allows us to see exactly what the induction
    hypothesis is.  If we prove [forall n, P_m0r n] by induction on
    [n] (using either [induction] or [apply nat_ind]), we see that the
    first subgoal requires us to prove [P_m0r 0] ("[P] holds for
    zero"), while the second subgoal requires us to prove [forall n',
    P_m0r n' -> P_m0r n' (S n')] (that is "[P] holds of [S n'] if it
    holds of [n']" or, more elegantly, "[P] is preserved by [S]").
    The _induction hypothesis_ is the premise of this latter
    implication -- the assumption that [P] holds of [n'], which we are
    allowed to use in proving that [P] holds for [S n']. *)

(* ####################################################### *)
(** ** Evenness Again *)

(** Some of the examples in the opening discussion of
    propositions involved the concept of _evenness_.  We began with a
    computation [evenb n] that _checks_ evenness, yielding a boolean.
    From this, we built a proposition [even n] (defined in terms of
    [evenb]) that _asserts_ that [n] is even.  That is, we defined
    "[n] is even" to mean "[evenb] returns [true] when applied to
    [n]."

    Another alternative is to define the concept of evenness directly.
    Instead of going indirectly via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say directly
    what the concept of evenness means in terms of evidence. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)

(** **** Exercise: 1 star, optional (four_ev) *)
(** Give a tactic proof and a proof object showing that four is even. *)

Theorem four_ev' :
  ev 4.
Proof.
  repeat (apply ev_SS); apply ev_0.
Qed.

Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
(** [] *)

(** **** Exercise: 2 stars (ev_plus4) *)
(** Give a tactic proof and a proof object showing that, if [n] is
    even, then so is [4+n]. *)

Require Import LibTactics.

Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  fun n Heven => ev_SS (2 + n) (ev_SS n Heven).

Theorem ev_plus4' : forall n,
  ev n -> ev (4 + n).
Proof.
  introv Heven.
  repeat (apply ev_SS). apply Heven.
Qed.
(** [] *)

(** **** Exercise: 2 stars (double_even) *)
(** Construct a tactic proof of the following proposition. *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n as [| n']; simpl; [apply ev_0 | apply ev_SS; apply IHn'].
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (double_even_pfobj) *)
(** Try to predict what proof object is constructed by the above
    tactic proof.  (Before checking your answer, you'll want to
    strip out any uses of [Case], as these will make the proof
    object look a bit cluttered.) *)
Check nat_ind.
(* nat_ind *)
(*      : forall P : nat -> Prop, *)
(*        P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Definition double_even' : forall n, ev (double n) :=
  fun n =>
    nat_ind (fun n' => ev (double n'))
            ev_0
            (fun n' IHn' => ev_SS (double n') IHn') n.
Print double_even.
(* double_even =  *)
(* fun n : nat => *)
(* nat_ind (fun n0 : nat => ev (double n0)) ev_0 *)
(*   (fun (n' : nat) (IHn' : ev (double n')) => ev_SS (double n') IHn') n *)
(*      : forall n : nat, ev (double n) *)

(* Argument scope is [nat_scope] *)
(** [] *)

(* ####################################################### *)
(** ** Reasoning by Induction Over Evidence *)

(** The highly "orthogonal" organization of Coq's design might
    suggest that, since we use the keyword [Induction] to define
    primitive propositions together with their evidence, there must be
    some sort of induction principles associated with these
    definitions.  Indeed there are, and in this section we'll take a
    look at how they can be used.  To get warmed up, let's look at how
    the simpler [destruct] tactic works with inductively defined
    evidence. *)

(** Besides _constructing_ evidence of evenness, we can also _reason
    about_ evidence of evenness.  The fact that we introduced [ev]
    with an [Inductive] declaration tells us not only that the
    constructors [ev_0] and [ev_SS] are ways to build evidence of
    evenness, but also that these two constructors are the _only_ ways
    that evidence of evenness can be built.

    In other words, if someone gives us evidence [E] justifying the
    assertion [ev n], then we know that [E] can only have one of two
    forms: either [E] is [ev_0] (and [n] is [O]), or [E] is [ev_SS n'
    E'] (and [n] is [S (S n')]) and [E'] is evidence that [n'] is
    even.

    Thus, it makes sense to use the tactics that we have already seen
    for inductively defined _data_ to reason instead about inductively
    defined _evidence_.

    For example, here we use a [destruct] on evidence that [n] is even
    in order to show that [ev n] implies [ev (n-2)]. *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star (ev_minus2_n) *)
(** What happens if we try to [destruct] on [n] instead of [E]? *)
(** [] *)

Theorem ev_minus2_n: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct n as [|n']; simpl.
    apply ev_0.
    destruct n' as [|n'']; simpl. apply ev_0.
    inversion E. assumption.
Qed.
(** We can also perform _induction_ on evidence that [n] is
    even. Here we use it to show that the old [evenb] function
    returns [true] on [n] when [n] is even according to [ev]. *)

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  Qed.

(** (Of course, we'd expect that [even n -> ev n] also holds.  We'll
    see how to prove it in the next chapter.) *)

(** **** Exercise: 1 star (ev_even_n) *)
(** Could this proof be carried out by induction on [n] instead
    of [E]? *)
Theorem ev_even_n : forall n,
  ev n -> even n.
Proof.
  introv E. induction n as [| n']; unfold even.
  Case "n = 0". reflexivity.
  Case "n = S n'".
    destruct n' as [| n''].
    SCase "n' = 0".
      inversion E.
    SCase "n' = S n''".
      simpl. inversion E.
Admitted.
(** [] *)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
[[
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
]]
   Briefly explain why.

Because the thesis is wrong and the logic is consistent. More specifically, given evidence that n is even, you can only prove that S (S n) is even.
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  introv Hn Hm.
  induction Hn as [| n' Hn'].
  Case "Hn = ev0". assumption.
  Case "Hn = ev_S n' Hn'". simpl.
  apply ev_SS. apply IHHn'.
Qed.
(** [] *)

(** Here's another situation where we want to analyze evidence for
    evenness: proving that if [n+2] is even, then [n] is.  Our first
    idea might be to use [destruct] for this kind of case analysis: *)

Theorem SSev_ev_firsttry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  destruct E as [| n' E'].
  (* Stuck: [destruct] gives us un-provable subgoals! *)
Admitted.

(** But this doesn't work.  For example, in the first sub-goal, we've
    lost the information that [n] is [0].  The right thing to use
    here, it turns out, is [inversion]: *)

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'.  Qed.

(* Print SSev_even. *)

(** This use of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)

(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  introv E. inversion E as [| n' E']. inversion E' as [|n'' E'']. apply E''.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  introv E. inversion E as [| n' E']. inversion E' as [| n'' E'']. inversion E''.
Qed.
(** [] *)

(** We can generally use [inversion] instead of [destruct] on
    inductive propositions.  This illustrates that in general, we
    get one case for each possible constructor.  Again, we also
    get some auxiliary equalities that are rewritten in the goal
    but not in the other hypotheses. *)

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E. inversion E as [| n' E']. 
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 3 stars (ev_ev_even) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  introv Hnm Hn.
  induction Hn as [|n' Hn'].
  Case "Hn = ev_0".
    simpl in Hnm; assumption.
  Case "Hn = ev_SS n' Hn'". simpl in Hnm. inversion Hnm as [|nm' Hnm'].
  apply IHHn'. apply Hnm'.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious.  You'll want the [replace] tactic used for [plus_swap']
    in Basics.v *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  introv Hm Hnp.
  apply ev_ev_even with (n := double n).
  Case "ev (double n + (m + p)".
    replace (double n + (m + p)) with ((n + m) + (n + p)).
    SCase "ev ((n + m) + (n + p))".
      apply ev_sum; assumption.
    dup.
    SCase "proof of replacement v1".
      remember (n + m) as nm eqn:Heqnm.
      remember (n + p) as np eqn:Heqnp.
      rewrite plus_assoc.
      rewrite (plus_comm (double n) m).
      rewrite double_plus.
      rewrite plus_assoc.
      rewrite (plus_comm m n).
      rewrite Heqnm.
      rewrite Heqnp.
      rewrite plus_assoc.
      reflexivity.

    SCase "proof of replacement v2".
      replace (double n + (m + p)) with (double n + m + p)
        by (symmetry; apply plus_assoc).
      replace (double n + m) with (m + double n) by apply plus_comm.
      rewrite double_plus.
      replace (m + (n + n)) with (m + n + n) by (symmetry; apply plus_assoc).
      replace (m + n) with (n + m) by apply plus_comm.
      rewrite plus_assoc.
      reflexivity.

  Case "ev (double n)".
    apply double_even.
Qed.
(** [] *)

(* ##################################################### *)
(** ** Why Define Propositions Inductively? *)

(** We have seen that the proposition "some number is even" can
    be phrased in two different ways -- indirectly, via a testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of
    defining evenness are about equally easy to state and work
    with.  Which we choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  For example, consider
    the property [MyProp] defined as follows:

       - the number [4] has property [MyProp]
       - if [n] has property [MyProp], then so does [4+n]
       - if [2+n] has property [MyProp], then so does [n]
       - no other numbers have property [MyProp]

    This is a perfectly sensible definition of a set of numbers, but
    we cannot translate this definition directly as a Coq Fixpoint (or
    translate it directly into a recursive function in any other
    programming language).  We might be able to find a clever way of
    testing this property using a [Fixpoint] (indeed, it is not too
    hard to find one in this case), but in general this could require
    arbitrarily much thinking.  In fact, if the property we are
    interested in is uncomputable, then we cannot define it as a
    [Fixpoint] no matter how hard we try, because Coq requires that
    all [Fixpoint]s correspond to terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [MyProp] is
    straightforward: *)

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

(** The first three clauses in the informal definition of [MyProp]
    above are reflected in the first three clauses of the inductive
    definition.  The fourth clause is the precise force of the keyword
    [Inductive]. *)

(** As we did with evenness, we can now construct evidence that
    certain numbers satisfy [MyProp]. *)

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl. 
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12. 
  apply MyProp2. 
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1.   Qed.

Theorem MyProp_ten_mine : MyProp 10.
Proof.
  apply MyProp3. simpl.
  replace 12 with (4 + 8) by reflexivity.
  apply MyProp2. 
  replace 8 with (4 + 4) by reflexivity.
  apply MyProp2.
  apply MyProp1.   Qed.

(** **** Exercise: 2 stars (MyProp) *)
(** Here are two useful facts about MyProp.  The proofs are left
    to you. *)

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3. apply MyProp3. apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  introv H. apply MyProp3. apply MyProp2. assumption.
Qed.
(** [] *)

(** With these, we can show that [MyProp] holds of all even numbers,
    and vice versa. *)

Theorem MyProp_ev : forall n:nat, 
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].  
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'.  Qed.

(** Here's an informal proof of this theorem:

    _Theorem_: For any nat [n], if [ev n] then [MyProp n].

    _Proof_: Suppose [n] is a [nat] and [E] is a derivation of [ev n].
    We must exhibit a derivation of [MyProp n].  The proof is by
    induction on [E].  There are two cases to consider:

    - If the last step in [E] is a use of [ev_0], then [n] is [0].
      Then we must show that [MyProp 0] holds; this is true by
      lemma [MyProp_0].

    - If the last step in [E] is a use of [ev_SS], then [n = S (S n')]
      for some [n'], and there is a derivation of [ev n'].  We must
      show [MyProp (S (S n'))], with the induction hypothesis that
      [MyProp n'] holds.  But by lemma [MyProp_plustwo], it's enough
      to show [MyProp n'], which is exactly the induction
      hypothesis. [] *)

(** **** Exercise: 3 stars (ev_MyProp) *)
Theorem ev_MyProp : forall n:nat, 
  MyProp n -> ev n.
Proof.
  introv E.
  induction E as [| n' E' | n' E']; [apply (ev_SS _ (ev_SS _ ev_0)) | apply (ev_SS _ (ev_SS _ IHE')) | inversion IHE'; assumption ].
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_MyProp_informal) *)
(** Write an informal proof corresponding to your
    formal proof of [ev_MyProp]:
 
    Theorem: For any nat [n], if [MyProp n] then [n] is even.
 
    Proof: Suppose we are given [n : nat]. We show that if [MyProp n]
    then [n] is even, by induction on a derivation of [MyProp n].

    - Suppose the final rule used to show [MyProp n] is
      [MyProp1]. Then [n = 4], which is even.

    - Suppose the final rule used to show [MyProp n] is
      [MyProp2]. Then [n = 4 + n'] for some [n'] with [MyProp n']. By
      the induction hypothesis, we have that [n'] is even - but then,
      (* since 4 is even and the sum of even numbers is even, also [n]
      is even. *)
      [To follow the formal proof: ]
      also [n' + 2] is even, and then also [n' + 4 = n] is even.

    - Suppose the final rule used to show [MyProp n] is
      [MyProp3]. Then we have [MyProp (2 + n)], and by the induction
      hypothesis it follows that [2 + n] is even. We can only prove
      that [2 + n] is even with a proof that [n] is even, so [n] is
      even as desired.

[] *)


(* ##################################################### *)
(** * The Big Picture: Coq's Two Universes *)

(** Now that we've touched on several of Coq's basic structures,
    it may be useful to take a step back and talk a little about how
    it all fits together. *)

(** Expressions in Coq live in two distinct universes:
      - [Type] is the universe of _computations_ and _data_.  
      - [Prop] is the universe of _logical assertions_ and _evidence_.

   The two universes have some deep similarities -- in each, we can
   talk about values, inductive definitions, quantification, etc. --
   but they play quite different roles in defining and reasoning about
   mathematical structures. *)

(** ** Values *)

(** Both universes start with an infinite set of _constructors_.
    Constructors have no internal structure: they are just atomic
    symbols.  For example, [true], [false], [O], [S], [nil], [cons],
    [ev_0], [ev_SS], ...

    The simplest values are expressions consisting entirely of
    constructor applications.  Examples include:
     - [true]
     - [O] 
     - [S (S (S O))]
     - [ev_0]
     - [ev_SS (S (S O)) ev_0]
     - [ev_SS (S (S (S (S O)))) (ev_SS (S (S O)) ev_0)]

    Such expressions can be thought of as trees. Their leaves are
    nullary constructors (applied to no arguments), and their internal
    nodes are applications of constructors to one or more values.  In
    the universe [Type], we think of values as _data_.  In [Prop], we
    think of values as _evidence_.  Values in [Prop] are sometimes
    called _derivation trees_. 

    Functions are also values -- for example:
     - [fun x => true] 
     - [fun b => negb b]
     - [fun n => S (S (S n))]
     - [fun n => fun (P : ev n) => ev_SS (S (S n)) P]

    Functions that return values in the universe [Type] represent
    _computations_: they take some input values and return an output
    value computed from the inputs.  Functions returning values in
    [Prop] are _universally quantified evidence_: that is, they use
    their inputs to build evidence for some proposition (whose
    statement may also involve these inputs). *)

(** ** Inductive Definitions *)

(** [Inductive] declarations give names to subsets of the set of all
    values.  For example, the declaration of the inductive type [nat]
    defines a _set_ whose _elements_ are values representing natural
    numbers.  That is, it picks out a subset [nat] of the set of all
    values that satisfies the following properties:
      - the value [O] is in this set;
      - the set is _closed_ under applications of [S] (i.e., if a
        value [n] is in the set, then [S n] is too);
      - it is the smallest set satisfying these conditions (i.e., the
        only values in [nat] are the ones that _must_ be, according to
        the previous two conditions; there is no other "junk").

    Inductively defined sets can themselves appear as arguments to
    constructors in compound values.  Examples:
      - [nat]
      - [nil nat]
      - [cons nat O (cons nat (S O) (nil nat))]

    Also, we can write functions that take sets as arguments and
    return sets as results.  For example, [list] is a function that
    takes a set [X] as argument and returns as result the set [list
    X] (whose members are lists with elements drawn from [X]).

    Similarly, the declaration of the inductive type [ev] defines a
    _family of propositions_ whose _elements_ are values representing
    evidence that numbers are even.  That is, for each [n], the
    definition picks out a subset [ev n] of the set of all values,
    satisfying the following properties:
      - the value [ev_0] is in the set [ev O];
      - the sets are _closed_ under well-typed applications of
        [ev_SS] -- i.e., if [e] is in the set [ev n], then
        [ev_SS n e] is in the set [ev (S (S n))];
      - it is the smallest family of sets satisfying these
        conditions (i.e., the only values in any set [ev n] are the
        ones that _must_ be, according to the previous two conditions;
        there is no other junk). *)

(** ** Types and Kinds *)

(** Informally, a _type_ in Coq is an expression that is used to
    classify other expressions.  For example, [bool], [nat], [list
    bool], [list nat], [nat->nat], and so on are all types.  The type
    [bool] classifies [true] and [false]; the type [nat] classifies
    [O], [S O], [S (S O)], etc.; the type [nat->nat] classifies
    function values (like [fun n => S n]) that yield a number when
    given a number as input.

    [Type], [Prop], and compound expressions built from them (like
    [Type->Type]) play a similar classifying role "one level up" --
    that is, they can be thought of as the _types of type (and
    proposition) expressions_.  Technically, they are called _kinds_,
    to avoid too many uses of the word "type."  For example, the
    expressions [nat], [nat->nat] and [list nat] all have kind [Type],
    while [list] itself has kind [Type->Type] and [ev] has kind
    [nat->Prop].  *)

(** ** Propositions vs. Booleans *)

(** Propositions and booleans are superficially similar, but they are
    really quite different things!

    - Booleans are _values_ in the _computational_ world.  Every
      expression of type [bool] (with no free variables) can be
      simplified to either [true] or [false].

    - Propositions are _types_ in the _logical_ world.  They are
      either _provable_ (i.e., there is some expression that has this
      type) or not (there is no such expression).  It doesn't make
      sense to say that a proposition is "equivalent to [true]." 

      We sometimes use the words "true" and "false" informally when
      referring to propositions.  Strictly speaking, this is wrong: a
      proposition is either provable or it is not. *)

(** ** Functions vs. Quantifiers *)

(** The types [A->B] and [forall x:A, B] both describe functions from
    [A] to [B].  The only difference is that, in the second case, the
    expression [B] -- the type of the result -- can mention the
    argument [x] by name.  For example:

       - The function [fun x:nat => x + x] has type [nat->nat] --
         that is, it maps each number [n] to a number.

       - The function [fun X:Type => nil (list X)] has type [forall
         X:Type, list (list X)] -- that is, it maps each set [X] to a
         particular list of lists of [X]s.  (Of course, [nil] is
         usually written as [[]] instead of [nil X].)

    In fact, the two ways of writing function types are really the
    same: In Coq, [A->B] is actually just an abbreviation for [forall
    x:A, B], where [x] is some variable name not occurring in [B].  For
    example, the type of [fun x:nat => x + x] can be written, if we
    like, as [forall x:nat, nat]. *)

(** ** Functions vs. Implications *)

(** In both [Type] and [Prop], we can write functions that transform
    values into other values.  Also, functions themselves are values;
    this means we can
      - write higher-order functions that take functions as arguments
        or return functions as results, and
      - apply constructors to functions to build complex values
        containing functions.

    A function of type [P->Q] in [Prop] is something that takes
    evidence for [P] as an argument and yields evidence for [Q] as its
    result.  Such a function can be regarded as _evidence_ that [P]
    implies [Q], since, whenever we have evidence that [P] is true, we
    can apply the function and get back evidence that [Q] is true:
    evidence for an implication is a function on evidence.  This is why
    we use the same notation for functions and logical implications in
    Coq: they are exactly the same thing! *)

(* ####################################################### *)
(** * Informal Proofs *)

(** Q: What is the relation between a formal proof of a proposition
       [P] and an informal proof of the same proposition [P]?

    A: The latter should _teach_ the reader how to produce the
       former.

    Q: How much detail is needed?

    A: There is no single right answer; rather, there is a range
       of choices.  

      At one end of the spectrum, we can essentially give the
      reader the whole formal proof (i.e., the informal proof
      amounts to just transcribing the formal one into words).
      This gives the reader the _ability_ to reproduce the formal
      one for themselves, but it doesn't _teach_ them anything.

      At the other end of the spectrum, we can say "The theorem
      is true and you can figure out why for yourself if you
      think about it hard enough."  This is also not a good
      teaching strategy, because usually writing the proof
      requires some deep insights into the thing we're proving,
      and most readers will give up before they rediscover all
      the same insights as we did.

      In the middle is the golden mean -- a proof that includes
      all of the essential insights (saving the reader the hard
      part of work that we went through to find the proof in the
      first place) and clear high-level suggestions for the more
      routine parts to save the reader from spending too much
      time reconstructing these parts (e.g., what the IH says and
      what must be shown in each case of an inductive proof), but
      not so much detail that the main ideas are obscured. 

   Another key point: if we're talking about a formal proof of a
   proposition P and an informal proof of P, the proposition P doesn't
   change.  That is, formal and informal proofs are _talking about the
   same world_ and they must _play by the same rules_. *)

(* ####################################################### *)
(** ** Informal Proofs by Induction *)

(** Since we've spent much of this chapter looking "under the hood" at
    formal proofs by induction, now is a good moment to talk a little
    about _informal_ proofs by induction.

    In the real world of mathematical communication, written proofs
    range from extremely longwinded and pedantic to extremely brief
    and telegraphic.  The ideal is somewhere in between, of course,
    but while you are getting used to the style it is better to start
    out at the pedantic end.  Also, during the learning phase, it is
    probably helpful to have a clear standard to compare against.
    With this in mind, we offer two templates below -- one for proofs
    by induction over _data_ (i.e., where the thing we're doing
    induction on lives in [Type]) and one for proofs by induction over
    _evidence_ (i.e., where the inductively defined thing lives in
    [Prop]).  In the rest of this course, please follow one of the two
    for _all_ of your inductive proofs. *)

(** *** Induction Over an Inductively Defined Set *)
 
(** _Template_: 

       - _Theorem_: <Universally quantified proposition of the form
         "For all [n:S], [P(n)]," where [S] is some inductively defined
         set.>

         _Proof_: By induction on [n].

           <one case for each constructor [c] of [S]...>

           - Suppose [n = c a1 ... ak], where <...and here we state
             the IH for each of the [a]'s that has type [S], if any>.
             We must show <...and here we restate [P(c a1 ... ak)]>.

             <go on and prove [P(n)] to finish the case...>

           - <other cases similarly...>                        []
 
    _Example_:
 
      - _Theorem_: For all sets [X], lists [l : list X], and numbers
        [n], if [length l = n] then [index (S n) l = None].

        _Proof_: By induction on [l].

        - Suppose [l = []].  We must show, for all numbers [n],
          that, if length [[] = n], then [index (S n) [] =
          None].

          This follows immediately from the definition of index.

        - Suppose [l = x :: l'] for some [x] and [l'], where
          [length l' = n'] implies [index (S n') l' = None], for
          any number [n'].  We must show, for all [n], that, if
          [length (x::l') = n] then [index (S n) (x::l') =
          None].

          Let [n] be a number with [length l = n].  Since
[[
            length l = length (x::l') = S (length l'),
]]
          it suffices to show that 
[[
            index (S (length l')) l' = None.
]]  
          But this follows directly from the induction hypothesis,
          picking [n'] to be length [l'].  [] *)
 
(** *** Induction Over an Inductively Defined Proposition *)

(** Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as _induction
    on derivations_. 

    _Template_:
 
       - _Theorem_: <Proposition of the form "[Q -> P]," where [Q] is
         some inductively defined proposition (more generally,
         "For all [x] [y] [z], [Q x y z -> P x y z]")>

         _Proof_: By induction on a derivation of [Q].  <Or, more
         generally, "Suppose we are given [x], [y], and [z].  We
         show that [Q x y z] implies [P x y z], by induction on a
         derivation of [Q x y z]"...>

           <one case for each constructor [c] of [Q]...>

           - Suppose the final rule used to show [Q] is [c].  Then
             <...and here we state the types of all of the [a]'s
             together with any equalities that follow from the
             definition of the constructor and the IH for each of
             the [a]'s that has type [Q], if there are any>.  We must
             show <...and here we restate [P]>.

             <go on and prove [P] to finish the case...>

           - <other cases similarly...>                        []

    _Example_
 
       - _Theorem_: The [<=] relation is transitive -- i.e., for all
         numbers [n], [m], and [o], if [n <= m] and [m <= o], then
         [n <= o].

         _Proof_: By induction on a derivation of [m <= o].

           - Suppose the final rule used to show [m <= o] is
             [le_n].  Then [m = o] and the result is immediate.

           - Suppose the final rule used to show [m <= o] is
             [le_S].  Then [o = S o'] for some [o'] with [m <= o'].
             By induction hypothesis, [n <= o'].

             But then, by [le_S], [n <= o].  [] *)

(* ##################################################### *)
(** * Optional Material *)

(** This section offers some additional details on how induction works
    in Coq.  It can safely be skimmed on a first reading.  (We
    recommend skimming rather than skipping over it outright: it
    answers some questions that occur to many Coq users at some point,
    so it is useful to have a rough idea of what's here.) *)

(* ##################################################### *)
(** ** More on the [induction] Tactic *)

(** The [induction] tactic actually does even more low-level
    bookkeeping for us than we discussed above.

    Recall the informal statement of the induction principle for
    natural numbers:
      - If [P n] is some proposition involving a natural number n, and
        we want to show that P holds for _all_ numbers n, we can
        reason like this:
          - show that [P O] holds
          - show that, if [P n'] holds, then so does [P (S n')]
          - conclude that [P n] holds for all n.
    So, when we begin a proof with [intros n] and then [induction n],
    we are first telling Coq to consider a _particular_ [n] (by
    introducing it into the context) and then telling it to prove
    something about _all_ numbers (by using induction).

    What Coq actually does in this situation, internally, is to
    "re-generalize" the variable we perform induction on.  For
    example, in the proof above that [plus] is associative...
*)

Theorem plus_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.   
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary [n], [m], and
     [p]..." *)
  intros n m p. 
  (* ...We now use the [induction] tactic to prove [P n] (that
     is, [n + (m + p) = (n + m) + p]) for _all_ [n],
     and hence also for the particular [n] that is in the context
     at the moment. *)
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* In the second subgoal generated by [induction] -- the
       "inductive step" -- we must prove that [P n'] implies 
       [P (S n')] for all [n'].  The [induction] tactic 
       automatically introduces [n'] and [P n'] into the context
       for us, leaving just [P (S n')] as the goal. *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** It also works to apply [induction] to a variable that is
   quantified in the goal. *)

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n']. 
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** Note that [induction n] leaves [m] still bound in the goal --
    i.e., what we are proving inductively is a statement beginning
    with [forall m].

    If we do [induction] on a variable that is quantified in the goal
    _after_ some other quantifiers, the [induction] tactic will
    automatically introduce the variables bound by these quantifiers
    into the context. *)

Theorem plus_comm'' : forall n m : nat, 
  n + m = m + n.
Proof.
  (* Let's do induction on [m] this time, instead of [n]... *)
  induction m as [| m']. 
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (plus_explicit_prop) *)
(** Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)

Definition plus_is_assoc (n : nat) := forall m p : nat, 
  n + (m + p) = (n + m) + p.
Theorem plus_assoc'': forall n : nat, plus_is_assoc n.
  induction n as [| n'].
    Case "n = 0". unfold plus_is_assoc. reflexivity.
    Case "n = S n'". unfold plus_is_assoc in *. introv.
    simpl. rewrite IHn'. reflexivity.
Qed.
(* FILL IN HERE *)
(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define 
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

Fixpoint true_upto_n__true_everywhere (n : nat) (P : nat -> Prop) :=
  match n with
    | 0 => forall m : nat, P m
    | S n' => P n -> (true_upto_n__true_everywhere n' P)
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.

(** [] *)

(* ##################################################### *)
(** ** Induction Principles in [Prop] *)

(** Earlier, we looked in detail at the induction principles that Coq
    generates for inductively defined _sets_.  The induction principles
    for inductively defined _propositions_ like [ev] are a tiny bit
    more complicated.  As with all induction principles, we want to use
    the induction principle on [ev] to prove things by inductively
    considering the possible shapes that something in [ev] can have --
    either it is evidence that [0] is even, or it is evidence that,
    for some [n], [S (S n)] is even, and it includes evidence that [n]
    itself is.  Intuitively speaking, however, what we want to prove
    are not statements about _evidence_ but statements about _numbers_.
    So we want an induction principle that lets us prove properties of
    numbers by induction on evidence.

    For example, from what we've said so far, you might expect the
    inductive definition of [ev]...
[[
    Inductive ev : nat -> Prop :=
       | ev_0 : ev O
       | ev_SS : forall n:nat, ev n -> ev (S (S n)).
]]
    ...to give rise to an induction principle that looks like this...
[[
    ev_ind_max :
       forall P : (forall n : nat, ev n -> Prop),
            P O ev_0 ->
            (forall (n : nat) (e : ev n), 
              P n e -> P (S (S n)) (ev_SS n e)) ->
            forall (n : nat) (e : ev n), P n e
]]
    ... because:

     - Since [ev] is indexed by a number [n] (every [ev] object
       [e] is a piece of evidence that some particular number [n]
       is even), the proposition [P] is parameterized by both [n]
       and [e] -- that is, the induction principle can be used to
       prove assertions involving both an even number and the
       evidence that it is even.

     - Since there are two ways of giving evidence of evenness
       ([ev] has two constructors), applying the induction
       principle generates two subgoals:

         - We must prove that [P] holds for [O] and [ev_0].

         - We must prove that, whenever [n] is an even number and
           [e] is evidence of its evenness, if [P] holds of [n]
           and [e], then it also holds of [S (S n)] and [ev_SS n
           e].

     - If these subgoals can be proved, then the induction
       principle tells us that [P] is true for _all_ even numbers
       [n] and evidence [e] of their evenness.

    But this is a little more flexibility than we actually need or
    want: it is giving us a way to prove logical assertions where the
    assertion involves properties of some piece of _evidence_ of
    evenness, while all we really care about is proving properties of
    _numbers_ that are even -- we are interested in assertions about
    numbers, not about evidence.  It would therefore be more convenient
    to have an induction principle for proving propositions [P] that
    are parameterized just by [n] and whose conclusion establishes [P]
    for all even numbers [n]:
[[
       forall P : nat -> Prop,
          ... ->
             forall n : nat, ev n -> P n
]]
    For this reason, Coq actually generates the following simplified
    induction principle for [ev]: *)

Check ev_ind.
(* ===>  ev_ind
             : forall P : nat -> Prop,
               P 0 ->
               (forall n : nat, ev n -> P n -> P (S (S n))) ->
               forall n : nat, ev n -> P n *)

(** In particular, Coq has dropped the evidence term [e] as a parameter
    of the the proposition [P], and consequently has rewritten the
    assumption [forall (n:nat) (e:ev n), ...] to be [forall (n:nat), ev
    n -> ...]; i.e., we no longer require explicit evidence of the
    provability of [ev n]. *)

(** In English, [ev_ind] says:

    - Suppose, [P] is a property of natural numbers (that is, [P
      n] is a [Prop] for every [n]).  To show that [P n] holds
      whenever [n] is even, it suffices to show:
  
      - [P] holds for [0]
  
      - for any [n], if [n] is even and [P] holds for [n],
        then [P] holds for [S (S n)]. *)

(** We can apply [ev_ind] directly instead of using [induction],
    following pretty much the same pattern as above. *)

Theorem ev_even' : forall n,
  ev n -> even n.
Proof.
  apply ev_ind.
  Case "ev_0". unfold even. reflexivity.
  Case "ev_SS". intros n' E' IHE'. unfold even. apply IHE'.  Qed.

(** **** Exercise: 3 stars, optional (prop_ind) *)
(** Write out the induction principles that Coq will generate for the
    inductive declarations [list] and [MyProp].  Compare your answers
    against the results Coq prints for the following queries. *)
(* Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X. *)

Definition list_ind' :=
  forall (X : Type) (P : list X -> Prop),
    P nil ->
    (forall (x : X) (l : list X), P l -> P (x :: l)) ->
    forall l : list X, P l.

Check list_ind.

Definition MyProp_ind' :=
  forall (P : nat -> Prop),
    P 4 ->
    (forall n : nat, MyProp n -> P n -> P (4 + n)) ->
    (forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) ->
    forall n : nat, MyProp n -> P n.
  
Check MyProp_ind.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_MyProp') *)
(** Prove [ev_MyProp] again, using [apply MyProp_ind] instead
    of the [induction] tactic. *)

Theorem ev_MyProp' : forall n:nat, 
  MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  Case "n = 4". repeat apply ev_SS. apply ev_0.
  Case "n = 4 + n'". intro n'. intros.
  repeat apply ev_SS. assumption.
  Case "2 + n = n'". intro n. introv M2n ev2n.
  inversion ev2n. assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (MyProp_pfobj) *)
(** Prove [MyProp_ev] and [ev_MyProp] again by constructing
    explicit proof objects by hand (as you did above in
    [ev_plus4], for example). *)

Fixpoint MyProp_ev_fix (n:nat) (evN : ev n) : MyProp n :=
  match evN with
    | ev_0 => MyProp_0
    | ev_SS n' evN' => MyProp_plustwo _ (MyProp_ev_fix _ evN')
  end.
Check ev_ind.
Definition MyProp_ev' (n:nat) (evN : ev n) : MyProp n :=
  ev_ind _ MyProp_0 (fun n' ev_n' M_n' => MyProp_plustwo n' M_n') n evN.

(* http://www.lix.polytechnique.fr/coq/bugs/show_bug.cgi?id=2830
Definition MyProp_ev'' (n:nat) (evN : ev n) : MyProp n :=
  ev_ind _ MyProp_0 (fun n' ev_n' M_n' => MyProp_plustwo _ M_n').
Definition ev_MyProp' (n : nat) (m : MyProp n) : ev n :=
  MyProp_ind _ (ev_SS _ (ev_SS _ ev_0))
             (fun n' M_n' ev_n' => ev_SS _ (ev_SS _ ev_n')) _ n m.
*)

Check ev_MyProp.
(* ev_MyProp *)
(*      : forall n : nat, MyProp n -> ev n *)
Check MyProp_ind.
(* MyProp_ind *)
(*      : forall P : nat -> Prop, *)
(*        P 4 -> *)
(*        (forall n : nat, MyProp n -> P n -> P (4 + n)) -> *)
(*        (forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) -> *)
(*        forall n : nat, MyProp n -> P n *)
Check ev_minus2'.
Print ev_minus2'.
Print ev_MyProp.
Definition ev_MyProp'' (n : nat) (m : MyProp n) : ev n :=
  MyProp_ind _ (ev_SS _ (ev_SS _ ev_0))
             (fun n' M_n' ev_n' => ev_SS _ (ev_SS n' ev_n'))
             (fun n' M2n' ev2n' =>
                match ev2n' return (ev n') with
                  | ev_0 => admit
                  | ev_SS n0 b => admit
                end)
             n m.

(** [] *)

Module P.

(** **** Exercise: 3 stars, optional (p_provability) *)
(** Consider the following inductively defined proposition: *)

Inductive p : (tree nat) -> nat -> Prop :=
   | c1 : forall n, p (leaf _ n) 1
   | c2 : forall t1 t2 n1 n2,
            p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
   | c3 : forall t n, p t n -> p t (S n).

(** Describe, in English, the conditions under which the
   proposition [p t n] is provable. 

   (* FILL IN HERE *)
*)
(** [] *)

End P.

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
[[
    c : forall l, l = rev l -> pal l
]]
      may seem obvious, but will not work very well.)
 
    - Prove that 
[[
       forall l, pal (l ++ rev l).
]]
    - Prove that 
[[
       forall l, pal l -> l = rev l.
]]
*)

Inductive pal {X} : list X -> Prop :=
  | pal_0 : pal (@nil X)
  | pal_center : forall (x : X), pal [x]
  | pal_add : forall (x : X) (l : list X), pal l -> pal (snoc (x :: l) x).

Theorem pal_constr : forall X (l : list X),
                       pal (l ++ rev l).
Proof.
  introv. induction l as [| x' l']; simpl.
  Case "l = []". apply pal_0.
  Case "l = x' :: l'".
(* snoc_with_append: *)
(*   forall (X : Type) (l1 l2 : list X) (v : X), *)
(*   snoc (l1 ++ l2) v = l1 ++ snoc l2 v *)
    replace (x' :: l' ++ snoc (rev l') x') with (snoc (x' :: (l' ++ rev l')) x').
    apply pal_add. assumption.
    SCase "proof of replacement".
      simpl. rewrite snoc_with_append. reflexivity.
Qed.

Theorem pal_eq_rev : forall X (l : list X), pal l -> l = rev l.
Proof.
  introv palL.
  induction palL; try reflexivity.
  Case "pal_add".
(* rev_snoc *)
(*      : forall (X : Type) (v : X) (s : list X), rev (snoc s v) = v :: rev s *)
    assert (x :: snoc l x = snoc (rev (snoc l x)) x) as Thesis.

    replace (snoc (rev (snoc l x)) x) with (x :: snoc (rev l) x) by (rewrite rev_snoc; reflexivity).
    congruence.
    (* replace (rev l) with l. (* This applies the assumption automatically. *)
    reflexivity. *)
    apply Thesis.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
[[
     forall l, l = rev l -> pal l.
]]
*)

Theorem eq_rev_pal : forall X (l : list X), l = rev l -> pal l.
Proof.
  introv.
  induction l as [|x l'].
  (*remember l as l0.
  induction l0 as [|x l']. *)
  Case "l = []". intros. apply pal_0.
  Case "l = x :: l'". simpl.
  clear IHl'.
  remember (rev l') as rl.
  induction rl as [| x1 rl'].
  SCase "rl = []". introv eq. inversion eq. apply pal_center.
  SCase "rl = x1 :: rl'".
    introv eq.
    simpl in eq.
    inversion eq as [[Heq H1]]. clear eq.
    rewrite <- Heq in *. clear Heq x1.
    apply pal_add.
    rewrite H1 in Heqrl.
    simpl in Heqrl.
    rewrite rev_snoc in Heqrl.
    inversion Heqrl as [[H0]]. clear Heqrl.
    rewrite <- H0 in *.
    (*
    SearchAbout rev.
Theorem rev_involutive : forall X (l : list X),
  rev (rev l) = l.
Proof.
  induction l as [| n l']; simpl; try reflexivity.
  rewrite rev_snoc.
  rewrite IHl'. reflexivity.
Qed.

    Check rev_snoc.
    rewrite rev_involutive in *.

(* rev_snoc *)
(*      : forall (X : Type) (v : X) (s : list X), rev (snoc s v) = v :: rev s *)
    rewrite rev_snoc in *.
  (* introv eq.
  induction (rev l') as [| x1 rl'].

  SCase "rl = []". (* introv eq. *) inversion eq. apply pal_center.
  SCase "rl = x1 :: rl'".
    (* introv eq. *)
    simpl in eq.
    inversion eq as [[Heq H1]]. clear eq.
    rewrite <- Heq in *. clear Heq x1.
    apply pal_add.
    rewrite H1 in Heqrl.
    simpl in Heqrl.
    rewrite rev_snoc in Heqrl.
    inversion Heqrl as [[H0]]. clear Heqrl.
    rewrite <- H0 in *. *)
*)
  Restart.
  induction l as [|x' l'].
  Case "l = []". intros. apply pal_0.
  Case "l = x' :: l'". simpl.
  induction l' as [|x'' l''].
  SCase "l' = []". introv H. apply pal_center.
  SCase "l' = x'' :: l''".
    simpl in *.
    introv H.
Abort.

(*
  destruct l'.
  SCase "l' = []".
  apply pal_center.
  simpl in eq.
  simpl in IHl'.*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
[[
    [1,2,3]
]]
    is a subsequence of each of the lists
[[
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
]]
    but it is _not_ a subsequence of any of the lists
[[
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]
]]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

Module broken.
Inductive subseq : list nat -> list nat -> Prop :=
  | sub_empty : forall l : list nat, subseq [] l
  | sub_cons : forall (n : nat) (l1 l2 : list nat),
                 subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_cc : forall (n : nat) (l1 l2 : list nat),
                 subseq l1 l2 -> subseq (n :: l1) (n :: l2).
Check list_ind.

Definition subseq_refl' (l : list nat) : subseq l l :=
  list_ind _ _ (sub_empty [])
           (fun n' l' subL => sub_cc n' l' l' subL) l.

Lemma subseq_refl : forall l : list nat, subseq l l.
Proof.
  induction l as [| n l'].
  Case "l = []". apply sub_empty.
  Case "l = n :: l'".
    apply sub_cc. assumption.
Qed.

Theorem subseq_app_easy : forall (l1 l2 l3 : list nat), subseq l1 l3 -> subseq l1 (l2 ++ l3).
Proof.
  introv H.
  induction l2 as [|n l2'].
  Case "l2 = []". assumption.
  Case "l2 = n :: l2'".
    simpl. apply sub_cons. assumption.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat), subseq l1 l2 -> subseq l1 (l2 ++ l3).
  introv H.
  induction l2 as [|n l2'].
  Case "l2 = []". inversion H. apply sub_empty.
  Case "l2 = n :: l2'". inversion H as [| |n1 l1'].
  SCase "sub_empty (l1 = [])". apply sub_empty.
  SCase "sub_cons". simpl. apply sub_cons. apply IHl2'. assumption.
  SCase "sub_cc". simpl. rewrite H0 in *. clear H0 n1.
  apply sub_cc.
  (* rewrite H1.
  apply IHl2'. apply sub_cc.  *)

  Restart.
  introv H.
  induction l1 as [|n1 l1'].
  Case "l1 = []". apply sub_empty.
  Case "l1 = n1 :: l1'".
    inversion H  as [|n2 l1'' l2' |n2 l2'].
    SCase "sub_cons".
    simpl.
    apply sub_cons. 
    (* rewrite H2. *)
  Restart.

  introv H.
  induction H; simpl; [apply sub_empty | apply sub_cons | apply sub_cc]; assumption.
Qed.

Lemma subseq_tail: forall n l1 l2, subseq (n :: l1) l2 -> subseq l1 l2.
Proof.
  introv.
  apply subseq_ind with
    (P := fun l1 l2 => subseq (n :: l1) l2 -> subseq l1 l2) (l := l1) (l0 := l2).
  admit. admit. admit.
  Restart.
  introv H.
  induction H; [admit | apply sub_cons; assumption | apply sub_cons; assumption ].

  (* Restart.

  introv H.
  inversion H as [|n2 l1' l2'|].
  admit.
  apply sub_cons. assumption. *)
Qed.
Print subseq_tail.
Check subseq_ind.

End broken.

Inductive subseq : list nat -> list nat -> Prop :=
  | sub_empty : subseq [] []
  | sub_cons : forall (n : nat) (l1 l2 : list nat),
                 subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_cc : forall (n : nat) (l1 l2 : list nat),
                 subseq l1 l2 -> subseq (n :: l1) (n :: l2).

Definition subseq_refl' (l : list nat) : subseq l l :=
  list_ind _ _ sub_empty
           (fun n' l' subL => sub_cc n' l' l' subL) l.

Lemma subseq_refl : forall l : list nat, subseq l l.
Proof.
  induction l as [| n l'].
  Case "l = []". apply sub_empty.
  Case "l = n :: l'".
    apply sub_cc. assumption.
Qed.

Theorem subseq_app_easy : forall (l1 l2 l3 : list nat), subseq l1 l3 -> subseq l1 (l2 ++ l3).
Proof.
  introv H.
  induction l2 as [|n l2'].
  Case "l2 = []". assumption.
  Case "l2 = n :: l2'".
    simpl. apply sub_cons. assumption.
Qed.

Lemma sub_empty_any : forall l : list nat, subseq [] l.
Proof.
  induction l; [apply sub_empty | apply sub_cons; assumption].
Qed.
Theorem subseq_app : forall (l1 l2 l3 : list nat), subseq l1 l2 -> subseq l1 (l2 ++ l3).
  introv H.
  induction H; simpl; [apply sub_empty_any | apply sub_cons | apply sub_cc]; assumption.
Qed.
Definition tail {X} (l:list X) : list X :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Lemma subseq_tail' n l1 l2 : subseq (n :: l1) l2 -> subseq l1 l2.
Proof.
  (*
  introv H.
  remember (n :: l1).
  cases H as H1; [inversion Heql | |].
  subst.
  apply sub_cons.
  apply subseq_tail' with (n := n). assumption.
  inversion Heql.
  subst.
  apply sub_cons.  assumption.
  Restart. *)
  introv H.
  inverts H.
  apply sub_cons.
  (* apply subseq_tail' with (n := n). assumption. *) admit.
  apply sub_cons. assumption.
Qed.

Print subseq_tail'.
(*
Lemma subseq_tail : forall n l1 l2, subseq (n :: l1) l2 -> subseq l1 l2.
Proof.
  introv H.
  remember (n :: l1).
  cases H as H1; [inversion Heql | |].
  subst.
  apply sub_cons.
  admit.
  apply sub_cons. (* assumption. *)

  Restart.
  introv.
  replace l1 with (tail (n :: l1)) by reflexivity.
  replace (n :: tail (n :: l1)) with (n :: l1) by reflexivity.
  induction (n :: l1).
  Case "n :: l1 = []". simpl. tauto.
  Case "n :: l1 = x :: l".
    generalize dependent l2.
    generalize dependent x.
    induction l.
    SCase "l = []".
      simpl. intros. apply sub_empty_any.
    SCase "l = cons".
      introv H H2.
      simpl in *.
  
  Restart.
  introv H. 
  induction l1 as [| n1 l1']; [introv H; apply sub_empty_any | ].
  introv H.
  inversions H.

  Restart.
  introv H.
  inversion H.
  (* rewrite <- H2 in *. clear H2 l2. *)
  apply sub_cons.
  clear H1 l0.
  admit.
  apply sub_cons. assumption.
  (* apply subseq_ind with
    (P := fun l1 l2 => subseq (n :: l1) l2 -> subseq l1 l2) (l := l1) (l0 := l2).
  admit. admit. admit. *)
  induction H; [admit | apply sub_cons; assumption | apply sub_cons; assumption ].
(* subseq_ind *)
(*      : forall P : list nat -> list nat -> Prop, *)
(*        (forall l : list nat, P [] l) -> *)
(*        (forall (n : nat) (l1 l2 : list nat), *)
(*         subseq l1 l2 -> P l1 l2 -> P l1 (n :: l2)) -> *)
(*        (forall (n : nat) (l1 l2 : list nat), *)
(*         subseq l1 l2 -> P l1 l2 -> P (n :: l1) (n :: l2)) -> *)
(*        forall l l0 : list nat, subseq l l0 -> P l l0 *)

Print subseq_ind.
*)
Theorem subseq_trans : forall (l1 l2 l3 : list nat), subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  introv Hs12 Hs23.
  (*
  dup.

  induction Hs12 as [| n l1' l2'|].
  apply sub_empty.
  admit. admit. *)
  
  induction Hs23 as [|n l2'| n l2' l3'].
  Case "sub_empty".
  inversion Hs12. apply sub_empty.
  Case "sub_cons".
  apply sub_cons. apply IHHs23. apply Hs12.
  Case "sub_cc".
    induction l1 as [|n1 l1'].
    SCase "l1 = []". apply sub_empty_any.
    SCase "l1 = n1 :: l1'".
      inversion Hs12.
      SSCase "sub_cons". clear H2 l2. clear H n0.
        apply sub_cons. apply IHHs23. apply H1.
      SSCase "sub_cc".
        rewrite H2 in *; clear H2 n1.
        clear H n0.
        clear H1 l1. clear H3 l2.
        apply sub_cc.
        inversion Hs23 as [ | n3 l2'' l3'' |].
        SSSCase "sub_empty (l2' = [])".
        rewrite <- H in *. inversion H0. apply sub_empty.
        SSSCase "sub_cons".
        subst.
        apply subseq_tail' with (n := n).
        apply IHHs23.
  Restart.
  introv Hs12 Hs23.
  induction l2 as [| n2 l2'].
  inversion Hs12.
  apply sub_empty_any.
  inversion Hs12.

  apply IHl2'. assumption.
Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (foo_ind_principle) *)
(** Suppose we make the following inductive definition:
[[
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
]]
   Fill in the blanks to complete the induction principle that will be
   generated by Coq. 
[[
   foo_ind
        : forall (X Y : Set) (P : foo X Y -> Prop),   
          (forall x : X, __________________________________) ->
          (forall y : Y, __________________________________) ->
          (________________________________________________) ->
           ________________________________________________
]]

*)
(** [] *)

(** **** Exercise: 2 stars, optional (bar_ind_principle) *)
(** Consider the following induction principle:
[[
   bar_ind
        : forall P : bar -> Prop,
          (forall n : nat, P (bar1 n)) ->
          (forall b : bar, P b -> P (bar2 b)) ->
          (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
          forall b : bar, P b
]]
   Write out the corresponding inductive set definition.
[[
   Inductive bar : Set :=
     | bar1 : ________________________________________
     | bar2 : ________________________________________
     | bar3 : ________________________________________.
]]

*)
(** [] *)

(** **** Exercise: 2 stars, optional (no_longer_than_ind) *)
(** Given the following inductively defined proposition:
[[
  Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil  : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n -> 
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n -> 
                             no_longer_than X l (S n).
]]
  write the induction principle generated by Coq.
[[
  no_longer_than_ind
       : forall (X : Set) (P : list X -> nat -> Prop),
         (forall n : nat, ____________________) ->
         (forall (x : X) (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         (forall (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         forall (l : list X) (n : nat), no_longer_than X l n -> 
           ____________________
]]

*)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
[[
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
]]
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(*
c2 _ _ c1 : R 1 [0]
c2 _ _ (c2 _ _ c1) : R 2 [1 , 0]
*)
Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

Definition c221 : R 2 [1, 0] := c2 _ _ (c2 _ _ c1).
(** [] *)



