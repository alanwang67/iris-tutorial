From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants token.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Structured Concurrency *)

(* ================================================================= *)
(** ** Introduction *)

(**
  As the reader might recall from the HeapLang chapter, the only
  construct for concurrency supported natively by HeapLang is [Fork].
  The [Fork] construction is an example of _unstructured_ concurrency.
  When we use [Fork] to create a new thread, there are no control flow
  constructs to reason about the termination of the forked thread – it
  just runs until it is done and, upon completion, disappears.

  When such control flow constructs are available, we call it
  _structured_ concurrency. It turns out that we can implement
  structured concurrency from unstructured concurrency, and we have
  already seen two such examples: [spawn] and [par]. Both of these
  constructs are part of HeapLang's library, but under the hood, they
  are simply HeapLang programs defined in terms of the [Fork] primitive.

  The library definitions additionally give and prove specifications for
  the constructs, which we have used in previous chapters. In this
  chapter, we will define the constructs from scratch and write our own
  specifications for them.
*)

(* ================================================================= *)
(** ** The Fork Construct *)

(**
  Let us begin by revisiting the [Fork] construct. The operation takes
  an expression [e] as an argument and spawns a new thread that executes
  [e] concurrently. The operation itself returns the unit value on the
  spawning thread.

  [Fork] does not have dedicated tactical support. Instead, we simply
  apply the lemma [wp_fork] – the specification for [Fork]. The lemma is
  as follows.
*)

About wp_fork.

(**
  For convenience, we include it here as well in `simplified' form.

    [WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}]

  That is, to show a weakest precondition of [Fork e], we have to show
  the weakest precondition of [e] for a trivial postcondition. The key
  point is that we only require the forked-off thread to be safe – we do
  not care about its return value, hence the trivial postcondition.
*)

(* ================================================================= *)
(** ** The Spawn Construct *)

(**
  The first structured concurrency construct we study is [spawn]. This
  consists of two functions: [spawn], which spawns a thread and returns
  a `handle', and [join], which uses the handle to wait for a thread to
  finish.

  We define the functions as follows.
*)

Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #()));;
    "c".

(* The ref should be atomic right?
   Yes writing into the ref seems to be atomic. Maybe since we are
   assuming sequential consistency this is okay? 
 *)
Definition join: val :=
  rec: "join" "c" :=
    match: !"c" with
      NONE => "join" "c"
    | SOME "x" => "x"
    end.

(**
  The idea with [spawn] is to create a `shared channel' which can be
  used to signal when the forked-off thread has terminated. In this
  case, the shared channel is simply a location containing an optional
  value. When forking off the function ["f"], we wrap it around a store
  operation, which writes the result of ["f"] into the location. The
  location is then returned to the spawning thread, which can use this
  so-called `handle' in the [join] function. The [join] function
  continuously checks if the location has been updated to contain a
  value. If this happens, the spawning thread knows that the forked-off
  thread has finished, so it can extract the return value from the
  location.

  Considering this behaviour, we give [spawn] the specification:

  [[
    {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
    {{{ P }}} spawn f {{{ h, RET h; join_handle h Ψ }}}
  ]]

  This states that to get a specification for [spawn f], we first must
  prove a specification for [f] which captures which resources [f]
  needs, [P], and what the value [f] terminates at satisfies, [Ψ]. If we
  can prove such a specification for [f], then, given [P], we can also
  run [spawn f], which will return a value [h] which satisfies a
  `join-handle' predicate. This predicate is a promise that if we
  invoke [join] with [h], then the value we get back satisfies [Ψ]. This
  is reflected in the specification for [join]:

  [[
    {{{ join_handle h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
  ]]

  Let us now prove these specifications.
*)

Section spawn.

Context `{!heapGS Σ}.
Let N := nroot .@ "handle".

(**
  Since we are using a shared channel, we will use an invariant to allow
  the two (concurrently running) threads to access it. An initial
  attempt at stating this invariant looks as follows.
*)
Definition handle_inv1 (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v : val, l ↦ v ∗ (⌜v = NONEV⌝ ∨ ∃ w : val, ⌜v = SOMEV w⌝ ∗ Ψ w).

(**
  The stated invariant governs the shared channel (some location [l])
  and states that either no value has been sent yet or some value has
  been sent that satisfies the predicate [Ψ].

  We can then use the invariant to define the [join_handle] predicate.
*)
Definition join_handle1 (h : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜h = #l⌝ ∗ inv N (handle_inv1 l Ψ).

(** Let us now attempt to prove the specification for [join]. *)
Lemma join_spec (h : val) (Ψ : val → iProp Σ) :
  {{{ join_handle1 h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "(%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%v & Hl & [>-> | (%w & >-> & HΨ)])".
  - wp_load.
    iModIntro.
    iSplitL "Hl".
    {
      iNext.
      iExists NONEV.
      iFrame.
      by iLeft.
    }
    wp_pures.
    by iApply "IH".
  - wp_load.
    iModIntro.
    iSplitR "HΦ".
    { rewrite /handle_inv1. iModIntro. iExists (InjRV w). iFrame. iRight. iExists w. iFrame.
      auto. }
    wp_pures. iApply "HΦ". iModIntro.
    (** 
      Now we need [HΨ] to reestablish the invariant, but we also need it
      for the postcondition. We are stuck... 
    *)
Abort.

(* The intution behind what we want to do is that if join is called then we don't need to
 actually reestablish the invariant, also we want to rule out the behavior of join
 being called twice *)

(**
  We need a way to keep track of whether [Ψ w] has been `taken out' of
  the invariant or not. However, we do not have any program state to
  link it to. Instead, we will use _ghost state_ to track this
  information. In particular, we will use _tokens_, which we introduced
  in the Resource Algebra chapter. We here use the token implementation
  from the Iris library, but it is similar to the version we
  implemented.
*)
Context `{!tokenG Σ}.

(* How can we make sure we initially satisify the invariant *)
(* and when we exit we also satisfy it as well *)
(* Definition handle_inv γ (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v : val, l ↦ v ∗ (⌜v = NONEV⌝ ∨ (∃ w : val, ⌜v = SOMEV w⌝ ∗ Ψ w) ∨ token γ). *)

(* We forgot to provide the token in the join handle 
   We need this because this is basically the protocol that is occuring 
   We get to replace the resource Ψ v with token, and this right is transfered to us
   by using the join_handle *)
(* Definition join_handle γ (h : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ l : loc, ⌜h = #l⌝ ∗ inv N (handle_inv γ l Ψ). *)

(* Lemma join_spec γ (h : val) (Ψ : val → iProp Σ) :
  {{{ join_handle γ h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "(%l & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  rewrite /handle_inv.
  iInv "I" as (v) "[H [> %H1 | H2]]". 
  - wp_load.
    iModIntro.
    iSplitL "H".
    {
      iNext.
      iExists NONEV. subst. iFrame. auto. 
    }
    subst. wp_pures.
    by iApply "IH".
  - wp_load. iDestruct "H2" as "[(%w & %H3 & H4) | H5]".
    + iModIntro. iSplitR "HΦ".
      * iFrame. iRight. iLeft. iExists w. iModIntro. iFrame. auto.
      * rewrite H3. wp_pures. iApply "HΦ".  admit.
    + iModIntro. 
Admitted. *)

(**
  The trick is to have an additional state in the invariant which
  represents the case where [Ψ w] has been taken out of the invariant.
  This state simply mentions the token.
*)

Definition handle_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∨ (∃ w, ⌜v = SOMEV w⌝ ∗ Ψ w) ∨ token γ).

(**
  This enables the owner of the token to open the invariant, extract
  [Ψ w], and close the invariant in the case that mentions the token. As
  such, we include the token in the join handle so that [join] gets
  access to the token.
*)

Definition join_handle (h : val) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ (l : loc), ⌜h = #l⌝ ∗ token γ ∗ inv N (handle_inv γ l Ψ).

(**
  Let us now try to prove the specifications again. We start with
  [spawn].
*)

(* Q: how can there be a token in our join_handle as well as in our invariant
   this seems like a contradiction
   A: It's not a contradicition since the conditions for the invariant are chained together
   by or's 
   everytime we have opened the invariant we have never used the token we have created to
   close it 
 *)
Lemma spawn_spec (P : iProp Σ) (Ψ : val → iProp Σ) (f : val) :
  {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
  {{{ P }}} spawn f {{{ h, RET h; join_handle h Ψ }}}.
Proof.
  iIntros "#H %Φ". iModIntro. iIntros "H1 H2". rewrite /spawn.
  iMod (token_alloc) as "(%γ & H4)".
  wp_pures. wp_alloc l as "H3".
  (* When can we allocate our invariant in Iris? *)
  (* why do we need "with []" *)
  iMod (inv_alloc N _ (handle_inv γ l Ψ) with "[H3]") as "#inv".
  { rewrite /handle_inv. iModIntro. iExists (InjLV #()). iFrame. auto. } 
  wp_pures.
  wp_apply (wp_fork with "[H1]").
  - iModIntro. wp_bind (f #()). iApply ("H" with "H1").
    iModIntro. iIntros (v) "H1". wp_pures.
    iInv "inv" as "H2".
    (* So we are opening the invariant here in order to update the value when we fork,
       and we have to consider which case in the invariant we are in 
     *)
    rewrite /handle_inv. iDestruct "H2" as "(%v1 & H2 & H3)".
    iDestruct "H3" as "[H3 | [H4 | H5]]".
    + (* We are in the first case where there is nothing in the ref yet,
         so we can update it
       *) 
      wp_store. iModIntro. iSplitR ""; auto.
      iModIntro. iExists (InjRV v). iFrame. iRight. iLeft. iExists v. iFrame. auto.
    + (* The value is no longer InjLV and has already been updated once before *)
      wp_store. iModIntro. iSplitR ""; auto.
      iModIntro. iExists (InjRV v). iFrame. iRight. iLeft. auto.
    + (* For the case of the token closing the invariant is trivially satisfied *)
      wp_store. iModIntro. iFrame. 
  - (* We are showing after the fork we should give back the location and show that
     the location we give back satisfies the join handle *)
    wp_pures. iModIntro. iApply "H2". rewrite /join_handle. iFrame. iExists l. auto.
Qed.

Lemma join_spec (Ψ : val → iProp Σ) (h : val) :
  {{{ join_handle h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros "%Φ H H1". rewrite /join /join_handle. iLöb as "IH". wp_pures.
  iDestruct "H" as "(%γ & %l & %H & H2 & #inv)". rewrite H.
  wp_bind (! _)%E.
  iInv "inv" as "(%v & H & [> %H3 | [H4 | >H5]])".
  - (* we are in the case of inv where the value hasn't been updated yet so we should
       expect to use Lob here & reestablish the invariant *)
    wp_load. iModIntro. iSplitR "H1 H2".
    + rewrite /handle_inv. iFrame. iLeft. auto.
    + rewrite H3. wp_pure. wp_pure. wp_pure. iApply ("IH" with "[H2]").
      * iExists γ. iExists l. iFrame. auto.
      * iApply "H1".
  - (* We are in the case where the fork has already updated the value *)
    wp_load. iModIntro. iSplitR "H1 H4".
    + rewrite /handle_inv. iFrame.
    + (* We have solved the previous issue and we can show that the value we get from the fork
         satisifies the post condition since we gave the token to the invariant
       *)
      iDestruct "H4" as "(%w & %H2 & H3)". rewrite H2. wp_pures. iApply "H1". auto.
  - (* We are in the case where there are two tokens so we should be able to derive false,
       this happens we the join thread has already transfered us ownership of the token 
     *)
    wp_pures. iExFalso. iApply (token_exclusive with "H2 H5").
Qed.

End spawn.

(* ================================================================= *)
(** ** The Par Construct *)

(**
  With [spawn] and [join] defined and their specifications proved, we
  can move on to study a classical parallel composition operator: [par].
  Its definition is quite straightforward – building on the [spawn]
  construct.
*)
Definition par : val :=
  λ: "f1" "f2",
  let: "h" := spawn "f1" in
  let: "v2" := "f2" #() in
  let: "v1" := join "h" in
  ("v1", "v2").

(** We introduce familiar notation for [par] that hides the thunks. *)
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

(**
  Our desired specification for [par] is going to look as follows:

  [[
    {{{ P1 }}} e1 {{{ v, RET v; Ψ1 v }}} -∗
    {{{ P2 }}} e2 {{{ v, RET v; Ψ2 v }}} -∗
    {{{ P1 ∗ P2 }}} e1 ||| e2 {{{ v1 v2, RET (v1, v2); Ψ1 v1 ∗ Ψ2 v2 }}}
  ]]

  The rule states that we can run [e1] and [e2] in parallel if they have
  _disjoint_ footprints and that we can verify the two components
  separately. For this reason, the rule is sometimes also referred to as
  the _disjoint concurrency rule_.  Note that this specification looks
  slightly different from the specification in the [par] library:
  [wp_par]. However, the differences are mainly notational.
*)

Section par.

(**
  Since [par] is implemented with [spawn], we will use [spawn_spec] and
  [par_spec] to prove the specification for [par]. As such, we will need
  to include the resource algebra that those specifications rely on:
  [token].
*)
Context `{!heapGS Σ, !tokenG Σ}.

(**
  It is actually quite straightforward to prove the [par] specification
  as most of the heavy lifting is done by [spawn_spec] and [join_spec].
*)
Lemma par_spec (P1 P2 : iProp Σ) (e1 e2 : expr) (Q1 Q2 : val → iProp Σ) :
  {{{ P1 }}} e1 {{{ v, RET v; Q1 v }}} -∗
  {{{ P2 }}} e2 {{{ v, RET v; Q2 v }}} -∗
  {{{ P1 ∗ P2 }}} (e1 ||| e2)%V {{{ v1 v2, RET (v1, v2); Q1 v1 ∗ Q2 v2 }}}.
Proof.
  iIntros "#H1 #H2 %Φ !> [HP1 HP2] HΦ".
  rewrite /par.
  wp_pures.
  (**
    We use [spawn_spec] to spawn a thread running [e1]. This requires us
    to prove that if [e1] terminates at value [v1], then [Q1 v1].
    However, this follows by our assumption ["H1"], so we easily prove
    this.
  *)
  wp_apply (spawn_spec P1 Q1 with "[] HP1").
  {
    iIntros "%Φ1 !> HP1  HΦ1".
    wp_pures.
    iApply ("H1" with "HP1 HΦ1").
  }
  (**
    We now get a join handle for the spawned thread, which guarantees us
    that the value we get upon joining with it satisfies [Q1].
  *)
  iIntros "%h Hh".
  wp_pures.
  (**
    Next, we execute [e2] in the current thread using its specification,
    ["H2"], which gives us that if [e2] terminates at some value [v2],
    then [Q2 v2].
  *)
  wp_apply ("H2" with "HP2").
  iIntros "%v2 HQ2".
  wp_pures.
  (**
    Finally, we join with the spawned thread using our join handle and
    [join_spec].
  *)
  wp_apply (join_spec with "Hh").
  iIntros "%v1 HQ1".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End par.

(**
  Let us try to use the [par] specification to prove a specification for a
  simple client. The client performs two `fetch and add' operations on
  the same location in parallel. The expression [FAA "l" #i] atomically
  fetches the value at location [l], adds [i] to it, and stores the
  result back in [l].

  Our specification will state that the resulting value is even.
*)

(* Does the operational semantics allow for !r to run to run before FAA,
   in this case it seems like it doesn't matter?
   A: No I think the parallel operations must finish at least this appears to be what is
   the case when I step through the WP 
 *)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (FAA "r" #2)
  |||
  (FAA "r" #6)
  ;;
  !"r".

Section parallel_add.
(**
  We must again assume the presence of the [token] resource algebra as
  we will be using the [par] specification, which relies on it through
  [spawn].
*)
Context `{!heapGS Σ, !tokenG Σ}.
Let N := nroot .@ "par_add".

(**
  We will have an invariant stating that [r] points to an even integer.
*)
Definition parallel_add_inv (r : loc) : iProp Σ :=
  ∃ n : Z, r ↦ #n ∗ ⌜Zeven n⌝.

Lemma parallel_add_spec :
  {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
Proof.
  iIntros "%Φ _ HΦ".
  rewrite /parallel_add.
  wp_alloc r as "Hr".
  wp_pures.
  iMod (inv_alloc N _ (parallel_add_inv r) with "[Hr]") as "#I".
  {
    iNext.
    iExists 0.
    iFrame.
  }
  (**
    We don't need information back from the threads, so we will simply
    use [λ _, True] as the postconditions. Similarly, we only need the
    invariant to prove the threads, and since this is in the persistent
    context, we let the preconditions be [True].
  *)
  wp_apply (par_spec (True%I) (True%I) _ _ (λ _, True%I) (λ _, True%I)).
  - iIntros (Φ') "!> _ HΦ'".
    iInv "I" as "(%n & Hr & >%Hn)".
    wp_faa.
    iModIntro.
    iSplitL "Hr".
    {
      iModIntro.
      iExists (n + 2)%Z.
      iFrame.
      iPureIntro.
      by apply Zeven_plus_Zeven.
    }
    by iApply "HΦ'".
  - iIntros (Φ') "!> _ HΦ'".
    iInv "I" as "(%n & Hr & >%Hn)".
    wp_faa. iModIntro. iSplitR "HΦ'".
    + iModIntro. rewrite /parallel_add_inv. iExists (n + 6)%Z.
      iFrame. iPureIntro.
      by apply Zeven_plus_Zeven.
    + iApply "HΦ'". auto.
  - auto.
  - (* This is the case where we perform the derference *)
    iIntros (v1 v2) "H". wp_pures.
    iInv "I" as "> H1". rewrite /parallel_add_inv. iDestruct "H1" as "(%n & H1 & %H2)".
    wp_load. iModIntro. iFrame. iSplitR.
    { iModIntro. auto. }
    { iApply "HΦ". auto. }
Qed.

End parallel_add.
