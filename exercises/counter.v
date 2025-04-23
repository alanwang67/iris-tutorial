From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Counter *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us define a simple counter module. Our counter consists of three
  functions:
  - a constructor, [mk_counter], which creates a new counter starting at
    [0].
  - an increment function, [incr], which increments the counter and
    returns the old value of the counter.
  - a read function, [read], which reads the current value of the
    counter.
  Furthermore, we want the counter to be shareable across multiple
  threads, so we will implement [incr] with [CAS] as the synchronisation
  mechanism.
*)

Definition mk_counter : val :=
  λ: <>, ref #0.

Definition incr : val :=
  rec: "incr" "c" :=
  let: "n" := !"c" in
  let: "m" := "n" + #1 in
  if: CAS "c" "n" "m" then "n" else "incr" "c".

Definition read : val :=
  λ: "c", !"c".

(* ================================================================= *)
(** ** Defining a Representation Predicate for the Counter *)

(* Q: What does it mean if we choose a representation predicate that is incorrect? *)

Module spec1.
Section spec1.
Context `{heapGS Σ}.

(**
  We are going to keep the fact that our counter is built on a pointer
  as an implementation detail. Instead, we will define a predicate
  describing when a value is a counter.

  Note that [#n] uses an implicit coercion from [nat] to [Z] called
  [Z.of_nat]. So if you have trouble applying lemmas that should work,
  it is likely because there is a hidden coercion in the way.
*)

Definition is_counter1 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ #n.

(**
  This predicate is, however, not persistent, so our value would not be
  shareable across threads. To fix this, we can put the knowledge into
  an invariant.
*)

Let N := nroot .@ "counter".

Definition is_counter2 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (l ↦ #n).

(**
  However, with this definition, we have locked the value of the pointer
  to always be [n]. To fix this, we could abstract the value and instead
  only specify its lower bound.
*)

Definition is_counter3 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ m : nat, l ↦ #m ∗ ⌜n ≤ m⌝).

(**
  We can now change what the pointer maps to, but we still cannot refine
  the lower bound.

  The final step is to use ghost state. The idea is to link [n] and [m]
  to pieces of ghost state in such a way that the validity of their
  composite is [n ≤ m].

  To achieve this, we will use the _authoritative_ resource algebra,
  [auth]. This resource algebra is parametrised by a CMRA, [A]. There
  are two types of elements in the carrier of the authoritative RA:
  - [● x] called an authoritative element
  - [◯ y] called a fragment
  where [x, y ∈ A].

  The idea of the authoritative RA is as follows. The authoritative
  element represents the whole of the resource, while the fragments act
  as the pieces. To achieve this, the authoritative element acts like
  the exclusive RA, while the fragment inherits all the operations of
  [A]. Furthermore, validity of [● x ⋅ ◯ y] is defined as [✓ x ∧ y ≼ x].

  In our case, we will use the authoritative RA over the [max_nat]
  resource algebra. The carrier of [max_nat] is the natural numbers, and
  the operation is the maximum.
 *)

(* What does it mean that the fragment inherits all the operations of [A]?
   I'm assuming in this case A is the carrier
 *)

(* Intution: Using the authorative RA we can represent both the part that is exclusive
   when you access the shared resource, while each thread can also maintain knowledge that
   will never be invalidated by anyone who acquires the lock. So in a sense we still have
   stable assertions, despite the fact that our state is changing 
 *)

Context `{!inG Σ (authR max_natUR)}.

(**
  As such, [● (MaxNat m)] will represent the _true_ value of the counter
  [m], and [◯ (MaxNat n)] will represent a _fragment_ of the counter – a
  lower bound [n].
*)

Definition is_counter (v : val) (γ : gname) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ MaxNat n) ∗
    inv N (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)).

Global Instance is_counter_persistent v γ n :
  Persistent (is_counter v γ n) := _.

(* ================================================================= *)
(** ** Properties of the Authoritative RA with MaxNat *)

(**
  Before we start proving the specification, let us prove some useful
  lemmas about our ghost state. For starters, we need to know that we
  can allocate the initial state we need.
*)
Lemma alloc_initial_state :
  ⊢ |==> ∃ γ, own γ (● MaxNat 0) ∗ own γ (◯ MaxNat 0).
Proof.
  (**
    Ownership of multiple fragments of state amounts to ownership of
    their composite. So we can simplify the goal a little.
  *)
  setoid_rewrite <- own_op.
  (** Now the goal is on the form expected by [own_alloc]. *)
  apply own_alloc.
  (**
    However, we are only allowed to allocate valid states. So we must
    prove that our desired state is a valid one.

    The validity of [auth] says that the fragment must be included in
    the authoritative element and the authoritative element must be
    valid.
  *)
  apply auth_both_valid_discrete.
  split.
  - (** Inclusion for [max_nat] turns out to be the natural ordering. *)
    apply max_nat_included; simpl.
    reflexivity.
  - (** All elements of [max_nat] are valid. *)
    cbv.
    done.
Qed.

(* Is this directly inherited from the carrier of the RA? *)
Lemma state_valid γ n m :
  own γ (● MaxNat n) -∗
  own γ (◯ MaxNat m) -∗
  ⌜m ≤ n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply max_nat_included in H; cbn in H.
  done.
Qed.

(* This update state does not invalidate any fragments *)
Lemma update_state γ n :
  own γ (● MaxNat n) ==∗
  own γ (● MaxNat (S n)) ∗ own γ (◯ MaxNat (S n)).
Proof.
  iIntros "H".
  rewrite <- own_op.
  (**
    As we saw in the Resource Algebra chapter, to update a resource, we
    must show that we can perform a frame preserving update to the
    updated resource.
  *)
  iApply (own_update with "H").
  (**
    [auth] has its own special version of these called _local updates_,
    as we know what the whole of the state is.
  *)
  apply auth_update_alloc.
  apply max_nat_local_update; cbn.
  by apply le_S.
Qed.

(* ================================================================= *)
(** ** Proving the Counter Specification *)

(**
  We are finally ready to give and prove specifications for the three
  counter functions. We begin with [mk_counter].
*)

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0}}}.
Proof.
  iIntros "%Φ HΦ H". rewrite /mk_counter /is_counter.
  wp_pures. wp_alloc l as "H1".
  iMod (alloc_initial_state) as "(%γ & H2 & H3)".
  iMod (inv_alloc N _ (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)) with "[H1 H2]") as "#H4".
  { iExists 0. iFrame. }
  iApply "H". iModIntro.
  iExists l. iFrame. auto. 
Qed.

Lemma read_spec c γ n :
  {{{ is_counter c γ n }}} read c {{{ (u : nat), RET #u; ⌜n ≤ u⌝ }}}.
Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  iLöb as "IH".
  wp_rec.
  iInv "HI" as "(%m & H & H1)".
  wp_load.
  (* If I put the percent here than my own γ (● MaxNat m) is preserved,
     which makes sense since the ghost state can only be updated in way that are valid 
   *)
  iPoseProof (state_valid γ m n with "H1 Hγ'") as "%H3".
  iFrame. iApply "HΦ". iModIntro. auto. 
Qed.

Lemma incr_spec c γ n :
  {{{ is_counter c γ n }}}
    incr c
  {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) }}}.
Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! #l)%E.
  iInv "HI" as "(%m & H & H1)".
  wp_load.
  iModIntro.
  (* We have to reestablish the invariant now *)
  iSplitL "H H1". { iExists m. iFrame.}
  wp_pures. wp_bind (CmpXchg _ _ _)%E.
  iInv "HI" as "(%m1 & H & H1)".
  destruct (decide (m1 = m)).
  - (* We can update the value bc. CAS is valid, but we also need to update the ghost state *)
    (* I think if we update the ghost state in a way that is valid, but does not match
     up with how the program executes then we just won't be able to complete the proof *)
    subst. wp_cmpxchg_suc.
    iPoseProof (state_valid γ (m) (n) with "H1 Hγ'") as "%H".    
    iMod (update_state γ m with "H1") as "H2".
    iDestruct "H2" as "[H2 #H3]".
    iPoseProof (state_valid γ (S m) (S m) with "H2 H3") as "%H1".
    iModIntro.
    iSplitL "H H2". { iModIntro. iExists (m + 1). admit. }
    wp_pures. iModIntro. iApply "HΦ". iSplitL ""; auto. rewrite /is_counter.
    iExists l. iSplitL ""; auto. iSplitL ""; auto.
    iPoseProof (own_valid with "Hγ'") as "H".
    assert (S m `max` S n = (S m)) by lia.
    assert (MaxNat (S m) ⋅ MaxNat (S n) = MaxNat (S m)). { rewrite max_nat_op. rewrite H0.
                                                             auto. }
    rewrite <- H2. iDestruct "H3" as "[H3 H4]". simpl. iApply "H4".
  - subst. wp_cmpxchg_fail. (* We want to use Lob on this case *)
    { admit. }
    iModIntro.
    iSplitL "H H1". { iExists m1. iFrame. }
    wp_pures. iApply "IH". iApply "HΦ".
Admitted.

(* ================================================================= *)
(** ** A Simple Counter Client *)

(**
  To illustrate how this counter specification works, let us consider a
  simple concurrent client of our counter module, which increments a
  counter twice in parallel. Our specification will simply be that the
  value of the counter will be at least [1] afterwards.
*)

Context `{!spawnG Σ}.

Lemma par_incr :
  {{{ True }}}
    let: "c" := mk_counter #() in
    (incr "c" ||| incr "c");;
    read "c"
  {{{ n, RET #(S n); True }}}.
Proof.
  iIntros "%Φ HΦ H".
  wp_apply (mk_counter_spec); auto.
  iIntros (c γ) "#H1". wp_pures.
  wp_apply (wp_par (λ _, is_counter c γ 1) (λ _, is_counter c γ 1)).
  { wp_apply (incr_spec); auto. iIntros (u) "(H & #H2)". iApply "H2". }
  { wp_apply (incr_spec); auto. iIntros (u) "(H & #H2)". iApply "H2". }
  iIntros (v1 v2) "(#H2 & #H3)". iModIntro. wp_pures. wp_apply (read_spec). { iApply "H2". }
  iIntros (u) "%H4". assert (u ≠ 0) by lia. apply Nat.succ_pred in H. rewrite <- H.
  iApply "H". auto.
Qed.

End spec1.
End spec1.

(* ================================================================= *)
(** ** A Stronger Counter Specification *)

Module spec2.
Section spec2.

(**
  Our first specification only allowed us to find a lower bound for the
  value in [par_incr]. Any solution to this problem has to be
  non-persistent, as we need to aggregate the knowledge to conclude the
  total value.

  To this end, we will use fractions. The [frac] resource algebra is
  similar to [dfrac] but without the capability of discarding fractions.
  As such, [frac] consists of non-negative rationals with addition as
  composition, and a fraction is only valid if it is less than or equal
  to [1]. This means that all the fractions can add up to at most [1].
  Combining [frac] with other resource algebras allows us to keep track
  of how much of the resource we own, meaning we can do the exact kind
  of aggregation we need. So this time, we will use the resource algebra
  [authR (optionUR (prodR fracR natR))]. Here, [natR] is the natural
  numbers with addition.
*)

(* Intuition: I think we use frac because when all the threads are joined back up
   we can determine the actual value
*)
  
Context `{!heapGS Σ, !inG Σ (authR (optionUR (prodR fracR natR)))}.

Let N := nroot .@ "counter".

Definition is_counter (v : val) (γ : gname) (n : nat) (q : Qp) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ Some (q, n)) ∗
    inv N (∃ m : nat, l ↦ #m ∗ own γ (● Some (1%Qp, m))).

(**
  With this definition, we can now decompose access to the counter by
  splitting the fraction, as well as splitting the knowledge of how much
  the counter has been incremented.
*)
Lemma is_counter_add (c : val) (γ : gname) (n m : nat) (p q : Qp) :
  is_counter c γ (n + m) (p + q) ⊣⊢ is_counter c γ n p ∗ is_counter c γ m q.
Proof.
  iSplit.
  - iIntros "(%l & -> & [Hγ1 Hγ2] & #I)".
    iSplitL "Hγ1".
    + iExists l.
      iSplitR; first done.
      by iFrame.
    + iExists l.
      iSplitR; first done.
      by iFrame.
  - iIntros "[(%l & -> & Hγ1 & I) (%l' & %H & Hγ2 & _)]".
    injection H as <-.
    iExists l.
    iSplitR; first done.
    iCombine "Hγ1 Hγ2" as "Hγ".
    iFrame.
Qed.

(**
  When allocating a new state, there will be _one_ fragment, which
  contains the entire fraction. Using the above lemma, we can then split
  up the fragment and supply these fragments to participating threads.
*)
Lemma alloc_initial_state :
  ⊢ |==> ∃ γ, own γ (● Some (1%Qp, 0)) ∗ own γ (◯ Some (1%Qp, 0)).
Proof.
  setoid_rewrite <-own_op.
  iApply own_alloc.
  apply auth_both_valid_discrete.
  split.
  - reflexivity.
  - apply Some_valid.
    apply pair_valid.
    split.
    + apply frac_valid.
      reflexivity.
    + cbv.
      done.
Qed.

(**
  The fragments of natural numbers add up to the full value, meaning
  that, in particular, they must all be less than or equal to the
  authoritative element.
*)
Lemma state_valid γ (n m : nat) (q : Qp) :
  own γ (● Some (1%Qp, n)) -∗
  own γ (◯ Some (q, m)) -∗
  ⌜m ≤ n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_pair_included in H.
  destruct H as [_ H].
  rewrite Some_included_total in H.
  apply nat_included in H.
  done.
Qed.

(**
  However, when a fragment has the entire fraction, there can't be any
  other fragments – intuitively, we have collected all contributions
  from all threads. So the count stored in the fragment must be equal to
  the one in the authoritative element.
*)
Lemma state_valid_full γ (n m : nat) :
  own γ (● Some (1%Qp, n)) -∗
  own γ (◯ Some (1%Qp, m)) -∗
  ⌜m = n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_included_exclusive in H.
  - destruct H as [_ H]; cbn in H.
    apply leibniz_equiv in H.
    done.
  - apply _.
  - done.
Qed.

(**
  Finally, when we have both the authoritative element and a fragment,
  we can increment both.
*)
Lemma update_state γ n m (q : Qp) :
  own γ (● Some (1%Qp, n)) ∗ own γ (◯ Some (q, m)) ==∗
  own γ (● Some (1%Qp, S n)) ∗ own γ (◯ Some (q, S m)).
Proof.
  iIntros "H".
  rewrite -!own_op.
  iApply (own_update with "H").
  apply auth_update.
  apply option_local_update.
  apply prod_local_update_2.
  apply (op_local_update_discrete _ _ 1).
  done.
Qed.

(**
  Let us prove the specifications for the counter functions again. This
  time, however, we will have two specifications for [read] – one with
  an arbitrary fraction and one with the whole fraction.
*)

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0 1}}}.
Proof.
  iIntros (Φ) "H1 H2". rewrite /mk_counter. wp_pures. wp_alloc l as "H3".
  iMod (alloc_initial_state) as "(%γ & H4 & H5)".
  iMod (inv_alloc N _ (∃ m : nat, l ↦ #m ∗ own γ (● Some (1%Qp, m))) with "[H3 H4]") as "#inv".
  { iExists 0. iFrame. }
  iModIntro. iApply "H2".
  iExists l. iFrame. auto.
Qed.
  
Lemma read_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}}
    read c
  {{{ (u : nat), RET #u; is_counter c γ n q ∗ ⌜n ≤ u⌝ }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  rewrite /read. wp_pures.
  iInv "I" as "(%m & H & H1)".
  wp_load.
  iPoseProof (state_valid γ m n with "H1 Hγ'") as "%H2".
  iFrame. iApply "HΦ". iFrame. iModIntro. iSplitL "". iExists l; auto.
  auto.
Qed.

Lemma read_spec_full (c : val) (γ : gname) (n : nat) :
  {{{ is_counter c γ n 1 }}} read c {{{ RET #n; is_counter c γ n 1 }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  rewrite /read. wp_pures.
  iInv "I" as "(%m & H & H1)".
  wp_load.
  iPoseProof (state_valid_full γ m n with "H1 Hγ'") as "%H2".
  iFrame. subst. iApply "HΦ". iFrame. iModIntro. iExists l. iSplitL; auto.
Qed.

Lemma incr_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}}
    incr c
  {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) q }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%m' & Hl & Hγ)".
  destruct (decide (# m = # m')).
  - injection e as e.
    apply (inj Z.of_nat) in e.
    subst m'.
    wp_cmpxchg_suc.
    (* This follows through in a similiar way as the previoius proofs *)
    iSplitL.
    + iModIntro. iExists (m + 1). 
    (* exercise *)
Admitted.

End spec2.
End spec2.
