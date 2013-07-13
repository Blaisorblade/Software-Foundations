Require Import Poly.

Require Import LibTactics.

Theorem app_ass : forall X (l1 l2 l3 : list X), 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  introv. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(* Distributivity in the collection, easier (?) to
prove. Distributivity in the function requires bag equality. *)

Lemma flat_map_distr :
  forall X Y (f : X -> list Y) l1 l2,
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  induction l1 as [| x1 l1'].
  Case "l1 = []". reflexivity.

  Case "l1 = x1 :: l1'".
  simpl.
  introv.
  rewrite app_ass.
  congruence.
Qed.


Definition bag := list.

(** **** Exercise: 3 stars (bag_functions) *)
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count {X} (eq : X -> X -> bool) (v : X) (s : bag X) : nat := 
  match s with
    | nil => 0
    | h :: t =>
      (if eq v h then 1 else 0) + count eq v t
  end.

Definition count_n := count beq_nat.
Example test_count1:              count_n 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count_n 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum {X} : bag X -> bag X -> bag X := app.

Example test_sum1:              count_n 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add {X} (v : X) (s : bag X) : bag X := cons v s.

Example test_add1:                count_n 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count_n 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Fixpoint remove_one {X} (eq: X -> X -> bool) (v:X) (s:bag X) : bag X :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
    | nil => nil
    | h :: t =>
      if (eq v h) then
        t
      else
        h :: remove_one eq v t
  end.

Example test_remove_one1:         count_n 5 (remove_one beq_nat 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:         count_n 5 (remove_one beq_nat 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:         count_n 4 (remove_one beq_nat 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: 
  count_n 5 (remove_one beq_nat 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.


Fixpoint subset {X} (eq: X -> X -> bool) (s1:bag X) (s2:bag X) : bool :=
  match s1 with
    | nil => true
    | h :: t =>
      if (blt_nat 0 (count eq h s2)) then
        subset eq t (remove_one eq h s2)
      else
        false
  end.

Example test_subset1:              subset beq_nat [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset beq_nat [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.


Definition member {X} (eq: X -> X -> bool) (v : X) (s:bag X) : bool := blt_nat 0 (count eq v s).

Example test_member1:             member beq_nat 1 [1,4,1] = true.
Proof. reflexivity. Qed.
Example test_member2:             member beq_nat 2 [1,4,1] = false.
Proof. reflexivity. Qed.
(** [] *)

Definition bag_eq {X} (eq: X -> X -> bool) (b1 b2 : bag X) : bool :=
  andb (subset eq b1 b2) (subset eq b2 b1).

Lemma flat_map_distr_f :
  forall X Y (eq: Y -> Y -> bool) (f1 f2 : X -> list Y) l,
    bag_eq eq (flat_map (fun x => f1 x ++ f2 x) l) (flat_map f1 l ++ flat_map f2 l) = true.
Proof.
  induction l as [| x l'].
  Case "l1 = []". reflexivity.

  Case "l1 = x1 :: l1'".
  simpl.

  
  rewrite app_ass.

(* 1 subgoals, subgoal 1 (ID 320) *)
  
(*   Case := "l1 = x1 :: l1'" : String.string *)
(*   X : Type *)
(*   Y : Type *)
(*   eq : Y -> Y -> bool *)
(*   f1 : X -> list Y *)
(*   f2 : X -> list Y *)
(*   x : X *)
(*   l' : list X *)
(*   IHl' : bag_eq eq (flat_map (fun x : X => f1 x ++ f2 x) l') *)
(*            (flat_map f1 l' ++ flat_map f2 l') = true *)
(*   ============================ *)
(*    bag_eq eq (f1 x ++ f2 x ++ flat_map (fun x0 : X => f1 x0 ++ f2 x0) l') *)
(*      ((f1 x ++ flat_map f1 l') ++ f2 x ++ flat_map f2 l') = true *)

Admitted.

(* For starters, above we need to start from propositional,
not decidable equality. And it needs to be some user-defined
propositional equality for bags. OK, probably need the standard library for this. *)

(*
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | h :: t =>
      let rest := remove_all v t in
      if (beq_nat v h) then rest else h :: rest
  end.

Example test_remove_all1:          count_n 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:          count_n 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:          count_n 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:          count_n 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.
(** [] *)
*)
