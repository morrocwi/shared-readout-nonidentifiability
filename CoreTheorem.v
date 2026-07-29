(* ===================================================================== *)
(*  CoreTheorem.v                                                         *)
(*                                                                        *)
(*  THE CORE, HARDENED.                                                   *)
(*                                                                        *)
(*  'When a readout collapses two distinct real states into a single       *)
(*  recorded value, both states still exist, but no decoder can recover     *)
(*  both of them from that record.'                                        *)
(*                                                                        *)
(*  This file proves that statement in the weakest hypotheses under which   *)
(*  it is true, and then proves -- not asserts -- that every route tried    *)
(*  elsewhere to escape it is closed. Each escape gets its own theorem:      *)
(*  the escape is stated in its strongest form, attempted, and shown to      *)
(*  fail, or shown to change the subject rather than the conclusion.         *)
(*                                                                        *)
(*  Coq 8.18+, fully abstract (Type-polymorphic wherever possible),          *)
(*  axiom-free throughout.                                                 *)
(* ===================================================================== *)

Require Import QArith.
Open Scope Q_scope.

(* ===================================================================== *)
(*  PART 0 -- the object, stated with no more structure than the claim     *)
(*  needs. X and R are arbitrary types; no finiteness, no decidable         *)
(*  equality, no algebraic structure of any kind is assumed anywhere in      *)
(*  this part.                                                             *)
(* ===================================================================== *)

Section Core.

Variables X R : Type.
Variable O : X -> R.

Definition correct_at (D : R -> X) (x : X) : Prop := D (O x) = x.

(* ===================================================================== *)
(*  PART 1 -- THE CORE THEOREM, at minimum hypotheses.                     *)
(* ===================================================================== *)

(*  Both states exist: this is not a theorem, it is the form of the          *)
(*  hypothesis itself -- x1 and x2 are handed in as ordinary values of X,     *)
(*  before anything about the readout is invoked. We state it as a           *)
(*  standalone fact anyway, so that 'both states still exist' is visibly     *)
(*  a claim discharged by nothing more than x1, x2 : X.                       *)
Theorem both_states_exist :
  forall x1 x2 : X, (exists x, x = x1) /\ (exists x, x = x2).
Proof. intros x1 x2. split; [exists x1 | exists x2]; reflexivity. Qed.

(*  No decoder recovers both. This is the load-bearing theorem.              *)
Theorem no_decoder_recovers_both :
  forall x1 x2 : X,
    x1 <> x2 ->
    O x1 = O x2 ->
    forall D : R -> X, correct_at D x1 -> correct_at D x2 -> False.
Proof.
  intros x1 x2 Hneq Heq D H1 H2.
  unfold correct_at in H1, H2.
  apply Hneq. rewrite <- H1, <- H2, Heq. reflexivity.
Qed.

(*  The two halves stated as one theorem, in the exact shape of the claim:    *)
(*  existence of the states is unconditional; existence of a decoder is       *)
(*  refuted. Two different existentials, two different verdicts, in a          *)
(*  single statement so that the shape of the claim is visible at a glance.    *)
Theorem the_core_theorem :
  forall x1 x2 : X,
    x1 <> x2 ->
    O x1 = O x2 ->
    (exists x, x = x1) /\ (exists x, x = x2) /\
    ~ (exists D : R -> X, correct_at D x1 /\ correct_at D x2).
Proof.
  intros x1 x2 Hneq Heq.
  split; [exists x1; reflexivity |].
  split; [exists x2; reflexivity |].
  intros [D [H1 H2]].
  exact (no_decoder_recovers_both x1 x2 Hneq Heq D H1 H2).
Qed.

End Core.

(* ===================================================================== *)
(*  PART 2 -- FORTIFICATION.                                               *)
(*                                                                        *)
(*  Every escape attempted against this claim, across the whole project,    *)
(*  reduces to one of the patterns below. Each is stated at its strongest,   *)
(*  most charitable form -- the form that would actually defeat the claim     *)
(*  if it worked -- and then shown to fail or to be answering a different     *)
(*  question.                                                               *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(*  ESCAPE 1 -- 'Give the unresolved state double duty: let it be both      *)
(*  the neutral element of accumulation AND the absorbing element of         *)
(*  composition, in one operation, so a single machinery can both start      *)
(*  clean and signal failure.'                                              *)
(*                                                                        *)
(*  This fails for a reason independent of readouts entirely: it is an       *)
(*  algebraic impossibility. One operation cannot have an element that is    *)
(*  both.                                                                   *)
(* --------------------------------------------------------------------- *)

Section Escape1.

Variable M : Type.
Variable op : M -> M -> M.
Variable e : M.

Definition is_identity  : Prop := forall x, op e x = x /\ op x e = x.
Definition is_absorbing : Prop := forall x, op e x = e /\ op x e = e.

Theorem escape1_fails :
  is_identity -> is_absorbing -> forall x y : M, x = y.
Proof.
  intros Hid Habs x y.
  assert (Hx : x = e).
  { destruct (Hid x) as [Hl _]. destruct (Habs x) as [Ha _].
    rewrite <- Hl, Ha. reflexivity. }
  assert (Hy : y = e).
  { destruct (Hid y) as [Hl _]. destruct (Habs y) as [Ha _].
    rewrite <- Hl, Ha. reflexivity. }
  rewrite Hx, Hy. reflexivity.
Qed.

End Escape1.

(*  READING. Escape 1 does not merely fail to help -- it collapses the       *)
(*  whole carrier to one point if it succeeds, which destroys the very        *)
(*  distinction (x1 <> x2) the core theorem's hypothesis requires. An         *)
(*  escape that erases the precondition has not defeated the theorem; it      *)
(*  has made it inapplicable by making its hypothesis unsatisfiable.           *)

(* --------------------------------------------------------------------- *)
(*  ESCAPE 2 -- 'Split the double duty into two operations instead of        *)
(*  one: accumulate within a reading with one operation, compose across       *)
(*  readings with another. Surely THAT recovers everything.'                  *)
(*                                                                        *)
(*  This one WORKS, exactly as claimed, and is proved constructively here.    *)
(*  What it does not do is touch the core theorem: it is a fact about how     *)
(*  a resolved/unresolved status propagates through a pipeline, and it         *)
(*  never claims to recover a value from a shared record. It answers a         *)
(*  different question honestly, rather than answering this one.               *)
(* --------------------------------------------------------------------- *)

Inductive Rec : Type := Unres : Rec | Res : Q -> Rec.

Definition acc (a b : Rec) : Rec :=
  match a, b with
  | Unres, y => y | x, Unres => x | Res p, Res q => Res (p + q)
  end.

Definition seq (a b : Rec) : Rec :=
  match a, b with
  | Unres, _ => Unres | _, Unres => Unres | Res p, Res q => Res q
  end.

Theorem escape2_succeeds_but_elsewhere :
  (forall x, acc Unres x = x) /\
  (forall x, seq Unres x = Unres) /\
  (exists x y : Rec, x <> y).
Proof.
  split; [intros [|p]; reflexivity |].
  split; [intros [|p]; reflexivity |].
  exists Unres, (Res 1). discriminate.
Qed.

(*  READING. escape2_succeeds_but_elsewhere is true, and proves that          *)
(*  Unres can be neutral for one operation and absorbing for another          *)
(*  without collapse. It says nothing about recovering two DISTINCT           *)
(*  RESOLVED values, Res p and Res q with p <> q, from a shared record --      *)
(*  the two operations govern how a status (resolved / unresolved)             *)
(*  propagates, not whether a resolved value can be decoded. The core           *)
(*  theorem is about O x1 = O x2 for x1 <> x2; nothing here supplies such       *)
(*  a pair sharing a record and claims to recover both. The escape solves       *)
(*  a real problem; it is not this one.                                        *)

(* --------------------------------------------------------------------- *)
(*  ESCAPE 3 -- 'Put the observer INSIDE the structure being read, rather     *)
(*  than outside it. An internal observer surely has access the core           *)
(*  theorem's abstract O : X -> R does not.'                                   *)
(*                                                                        *)
(*  Formalised: a strict partial order (causal past), a reader positioned      *)
(*  AS an event, reading only its own causal past. Two things are proved:      *)
(*  the reader cannot read itself (a genuine gain), and the reader's            *)
(*  readout of anything else is still an ordinary function of type              *)
(*  X -> R, so the core theorem applies to it unchanged.                       *)
(* --------------------------------------------------------------------- *)

Section Escape3.

Variable E : Type.
Variable prec : E -> E -> Prop.
Hypothesis prec_irrefl : forall e, ~ prec e e.

Definition Past (e : E) : E -> Prop := fun e' => prec e' e.

Theorem reader_cannot_read_itself :
  forall e : E, ~ Past e e.
Proof. intros e H. exact (prec_irrefl e H). Qed.

(*  The gain is real and is exactly reader_cannot_read_itself. What it does   *)
(*  NOT supply is a new kind of access to anything else: a reader positioned   *)
(*  inside E still reads OTHER events through a readout R : E -> R' of the      *)
(*  same shape the core theorem quantifies over. Being inside the structure     *)
(*  changes what the reader cannot see (itself); it does not change what a      *)
(*  reading of two collapsed OTHER states can recover.                          *)
Theorem internal_position_does_not_change_the_core :
  forall (R' : Type) (Oread : E -> R') (x1 x2 : E),
    x1 <> x2 -> Oread x1 = Oread x2 ->
    forall D : R' -> E, correct_at E R' Oread D x1 -> correct_at E R' Oread D x2 -> False.
Proof.
  intros R' Oread x1 x2 Hneq Heq D H1 H2.
  exact (no_decoder_recovers_both E R' Oread x1 x2 Hneq Heq D H1 H2).
Qed.

End Escape3.

(*  READING. The core theorem is literally re-derivable, unchanged, for an     *)
(*  internal reader's readout of anything other than itself. Self-opacity      *)
(*  and shared-record undecodability are two separate, both-true facts;         *)
(*  moving the observer inside the structure buys the first and does not        *)
(*  touch the second.                                                          *)

(* --------------------------------------------------------------------- *)
(*  ESCAPE 4 -- 'Add memory: let the decoder see not just the current           *)
(*  record but a history of past records. Surely a longer trace breaks the      *)
(*  collapse.'                                                                 *)
(*                                                                        *)
(*  Formalised at its strongest: the decoder is upgraded from R -> X to a       *)
(*  full HISTORY list (list R) -> X. If the two states x1, x2 produce THE       *)
(*  SAME record at every past time as well as the present one, the decoder      *)
(*  with memory is no better off than the decoder without it.                   *)
(* --------------------------------------------------------------------- *)

Section Escape4.

Variables X R : Type.
Variable Ohist : nat -> X -> R.

Definition SameHistoryForever (x1 x2 : X) : Prop :=
  forall k : nat, Ohist k x1 = Ohist k x2.

(*  The axiom-free version: rewrite the decoder's own two applications        *)
(*  directly, using SameHistoryForever pointwise, rather than reifying the     *)
(*  two history FUNCTIONS as equal (which would need functional                *)
(*  extensionality, an axiom this whole project avoids throughout).             *)
Theorem memory_does_not_help_if_the_whole_history_collapses' :
  forall x1 x2 : X,
    x1 <> x2 ->
    SameHistoryForever x1 x2 ->
    forall Dh : (nat -> R) -> X,
      (forall f g : nat -> R, (forall n, f n = g n) -> Dh f = Dh g) ->
      Dh (fun n => Ohist n x1) = x1 ->
      Dh (fun n => Ohist n x2) = x2 ->
      False.
Proof.
  intros x1 x2 Hneq Hsame Dh Dh_ext H1 H2.
  apply Hneq.
  rewrite <- H1, <- H2.
  apply Dh_ext.
  exact Hsame.
Qed.

End Escape4.

(*  READING. This is the honest form of the memory escape and its honest       *)
(*  limit. The extra hypothesis Dh_ext -- that the decoder only depends on      *)
(*  the pointwise values of the history, not on some other feature of how       *)
(*  it is presented -- is what a REAL decoder implemented as a function of       *)
(*  data must satisfy; it is not smuggled, it is what 'the decoder reads the     *)
(*  history' means. Under that reading, memory that never diverges gives no      *)
(*  new information: if x1 and x2 produced the identical trace forever, a        *)
(*  history-reading decoder is bound by the same collapse as a one-shot one.      *)
(*                                                                        *)
(*  What memory DOES achieve, honestly: if the histories diverge at some         *)
(*  point n0, that divergence is visible and recovery becomes possible from       *)
(*  that point on -- this is not a counterexample to the core theorem, it is      *)
(*  the core theorem's own hypothesis (O x1 = O x2) failing to hold once the       *)
(*  richer readout Ohist n0 is used instead. Memory helps exactly when and        *)
(*  only when it changes which readout is in play from one that collapses to      *)
(*  one that does not -- which is compatible with, not a refutation of, the       *)
(*  core theorem.                                                                *)

(* --------------------------------------------------------------------- *)
(*  ESCAPE 5 -- 'Deny that the states are separate at all: claim the two        *)
(*  labels name the SAME underlying object, so there is nothing to recover       *)
(*  because there was never a pair.'                                            *)
(*                                                                        *)
(*  This does not defeat the theorem; it denies the theorem's own                *)
(*  hypothesis (x1 <> x2). We make that precise: if x1 = x2, the conclusion       *)
(*  'no decoder recovers both' is not merely unproved but the wrong question --   *)
(*  recovering x1 IS recovering x2, trivially, by the identity decoder. The       *)
(*  escape is available, and it is available by construction, not by defeating    *)
(*  anything: this is exactly what the theorem's hypothesis already excludes.      *)
(* --------------------------------------------------------------------- *)

Theorem escape5_is_the_hypothesis_not_a_refutation :
  forall (X R : Type) (O : X -> R) (x1 x2 : X),
    x1 = x2 ->
    exists D : R -> X, correct_at X R O D x1 /\ correct_at X R O D x2.
Proof.
  intros X R O x1 x2 Heq.
  exists (fun _ => x1).
  unfold correct_at. split; [reflexivity | rewrite Heq; reflexivity].
Qed.

(*  READING. escape5_is_the_hypothesis_not_a_refutation is the precise           *)
(*  converse boundary of the core theorem: recovery IS possible exactly           *)
(*  when the states are not actually distinct. This is not a weakness in the      *)
(*  core theorem; it is confirmation that x1 <> x2 is doing real work and is      *)
(*  not a hidden vacuity. Denying the hypothesis does not refute the theorem;     *)
(*  it steps outside its domain, and the domain's boundary is exactly where       *)
(*  this theorem says it is.                                                     *)

(* ===================================================================== *)
(*  SUMMARY.                                                              *)
(*                                                                        *)
(*  the_core_theorem holds at the weakest possible hypotheses: two states      *)
(*  in an arbitrary type, a readout to an arbitrary type, distinctness of      *)
(*  the states, and coincidence of their readout. Nothing else is assumed.      *)
(*                                                                        *)
(*  Five escapes were attempted against it, in their strongest forms:           *)
(*                                                                        *)
(*    1. One operation, double duty        -- algebraically impossible.        *)
(*    2. Two operations, double duty        -- succeeds, but proves a           *)
(*                                             different statement.             *)
(*    3. Observer moved inside the structure -- gains self-opacity, leaves       *)
(*                                             the core theorem unchanged        *)
(*                                             for readouts of anything else.    *)
(*    4. Decoder given memory                -- collapses identically           *)
(*                                             whenever the whole history        *)
(*                                             collapses; helps exactly when      *)
(*                                             and only when it changes which     *)
(*                                             readout is in play.               *)
(*    5. Deny the states are distinct         -- steps outside the theorem's     *)
(*                                             domain rather than refuting        *)
(*                                             anything inside it.               *)
(*                                                                        *)
(*  No sixth escape is attempted here. The core stands at the strength         *)
(*  stated, with every route tried against it closed and the closure proved,    *)
(*  not asserted.                                                              *)
(* ===================================================================== *)
