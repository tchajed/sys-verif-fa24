---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
---

# Fractional permissions

Fractional permissions are a feature of separation logic that supports read-only permissions. This is especially important for concurrency.

Going into this document, I assume you have some familiarity with separation logic, enough to understand what `l ↦ v` means as a separation logic proposition (an `iProp` specifically).

## Setup: normal permissions

In GooseLang, the "basic points-to fact" is written with a type (the reasons are explained separately), but this doesn't affect the discussion here. We'll show examples only using the uint64 type. The `l ↦[uint64T] #x` permission allows both reads and writes.

```coq
Lemma read_spec (l: loc) (x: w64) :
  {{{ l ↦[uint64T] #x }}}
    ![uint64T] #l
  {{{ RET #x; l ↦[uint64T] #x }}}.
Proof.
  wp_start as "H". wp_load.
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma write_spec (l: loc) (x x': w64) :
  {{{ l ↦[uint64T] #x }}}
    #l <-[uint64T] #x'
  {{{ RET #(); l ↦[uint64T] #x' }}}.
Proof.
  wp_start as "H". wp_store.
  iModIntro. iApply "HΦ". iFrame.
Qed.

```

## Fractional read-only permissions

Especially with concurrency, we might want to make a location (that is, a variable) read-only, and in exchange it should be safe to read from multiple locations. Fractional permissions are a logical feature that permits such reasoning while remaining _sound_; it won't allow us to prove something false.

## Setup: normal permissions

The idea is to index every points-to fact with a fraction `q ∈ (0, 1]`, written `l ↦[uint64T]{#q} #x` in Iris (we'll get back to the `#q` in bit). This new permission has the following properties:

- A permission can be split into fractional parts, `l ↦[uint64T]{#1} #x ⊣⊢ l ↦[uint64T]{#1/2} #x ∗ l ↦[uint64T]{#1/2} #x` (recall `⊣⊢` is like "if and only if").
- `l ↦[uint64T]{q} #x` is enough to read (note that `q > 0`, which is required for this setup to work!)
- `l ↦[uint64T]{1} #x` is written `l ↦[uint64T] #x` and gives read and write permission.

Let's see these principles in action in Perennial.

This proof shows some features integrated into the IPM related to fractions. Most of the proofs in this file aren't that interesting, but this one has some non-obvious tricks.

```coq
Lemma fraction_split l (x: w64) :
  l ↦[uint64T]{#1} #x ⊣⊢ l ↦[uint64T]{#(1/2)} #x ∗ l ↦[uint64T]{#(1/2)} #x.
Proof.
  iSplit.
  - iIntros "H".
    (* [iDestruct] can split a permission into fractions, by default into halves *)
    iDestruct "H" as "[H1 H2]".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  x : w64
  ============================
  "H" : l ↦[uint64T] #x // [!code --]
  "H1" : l ↦[uint64T]{#1 / 2} #x // [!code ++]
  "H2" : l ↦[uint64T]{#1 / 2} #x // [!code ++]
  --------------------------------------∗
  l ↦[uint64T]{#1 / 2} #x ∗ l ↦[uint64T]{#1 / 2} #x
```

::::

```coq
    iFrame.
  - iIntros "[H1 H2]".
    (* [iCombine] is a tactic that does the opposite of [iDestruct] - not often
    needed, but especially useful when dealing with fractions *)
    iCombine "H1 H2" as "H".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  x : w64
  ============================
  "H1" : l ↦[uint64T]{#1 / 2} #x // [!code --]
  "H2" : l ↦[uint64T]{#1 / 2} #x // [!code --]
  "H" : l ↦[uint64T] #x // [!code ++]
  --------------------------------------∗
  l ↦[uint64T] #x
```

::::

```coq
    iFrame.
Qed.

```

I said a fraction was `q ∈ (0, 1]`. This is realized with a custom type in Coq, `Qp` (the name is supposed to evoke "positive rational").

```coq
Lemma read_frac_spec l (x: w64) (q: Qp) :
  {{{ l ↦[uint64T]{#q} #x }}}
    ![uint64T] #l
  {{{ RET #x; l ↦[uint64T]{#q} #x }}}.
Proof.
  wp_start as "H". wp_load.
  iModIntro. iApply "HΦ". iFrame.
Qed.

```

The left and right hand sides of this equality parse to the same term.

This is a case where we have to put `%I` to parse this using all the Iris notation.

```coq
Lemma frac_1_abbreviation (l: loc) (x: w64) :
  (l ↦[uint64T]{#1} #x)%I = (l ↦[uint64T] #x)%I.
Proof.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  l : loc
  x : w64
  ============================
  (l ↦[uint64T] #x)%I = (l ↦[uint64T] #x)%I
```

::::

```coq
  reflexivity.
Qed.

```

What have we accomplished with this? We can now reason about a program that allocates a reference obtaining a full 1 permission, then "subdivides" that permission in a purely logical way (that is, no code is required to split the permission), uses those permissions in multiple threads, and then even re-combines them to get back to a full 1 permission and does some writes.

Furthermore, we don't have to split just `1` into `1/2 + 1/2`; a thread with a `1/2` permission can subdivide it again, as many times as needed.

## Discardable fractions: fully read-only permission

In some situations a pointer is only ever going to be read-only. It would be nice to take advantage of this fact.

It is possible to work with the permission `ro_ptsto l x := (∃ q, l ↦[uint64T]{#q} #x)`. `ro_ptsto` can be split into as many copies as needed. However, in Iris it is convenient to have a _persistent_ proposition, and unfortunately `ro_ptsto` is not persistent (since we cannot duplicate it infinitely many times, otherwise the combine of `⌜1/q⌝` of them will lead to an overflow of 1).

As recent development in Iris called _discardable fractions_ has enabled persistent, fractional permissions, by changing how fractions are represented.

The intuition is to create a new type `dfrac` that replaces `Qp` (recall that was a positive rational number). Intuitively, a `dfrac` is still like a positive rational, but it can also have a special "ε" value that represents an infinitesimal (but positive) fraction. It will be possible to obtain an "ε" fraction by _discarding_ some fraction, making it permanently impossible to recover the 1 permission, but retaining read-only permissions. A sketchy definition of "ε" is `∀q, ε+q ≜ q<1` or `ε+1 ⊢ False`.

Let's see how this is realized in Iris.

First, the normal permissions are written `DfracOwn q` (with `q : Qp`). Above we're using a notation with `#` that accomplishes the same thing, hence why we wrote `#1` and `#(1/2)`.

Second, the ε permission is actually written `DfracDiscarded`, and more commonly has notations written with `□` (because it's persistent), e.g., `l ↦[uint64T]□ #v`.

Third, discarding the fraction involves an Iris "update", a change in ghost state.

## Discardable fractions in proofs

```coq
Lemma alloc_ro_spec (x: w64) :
  {{{ True }}}
    ref_to uint64T #x
  {{{ (l: loc), RET (#l: val); l ↦[uint64T]□ #x }}}.
Proof.
  (* This proof is a bit odd because it's just a single allocation, so the
  tactics don't quite do the right thing. We'll need to do the work of
  [wp_start] manually, and to use [rewrite -wp_fupd] to be able to use [iMod]
  when needed.  |*)
  iIntros (Φ) "_ HΦ".
  rewrite -wp_fupd.
  wp_alloc l as "H".

```

This is the step where we persist the points-to permission and turn it into a persistent, read-only fact. Also notice that the output (renamed to "Hro" for clarity) is put into the persistent context.

```coq
  iMod (struct_pointsto_persist with "H") as "#Hro".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  x : w64
  Φ : val → iPropI Σ
  l : loc
  ============================
  "Hro" : l ↦[uint64T]□ #x // [!code ++]
  --------------------------------------□ // [!code ++]
  "HΦ" : ∀ l0 : loc, l0 ↦[uint64T]□ #x -∗ Φ #l0
  "H" : l ↦[uint64T] #x // [!code --]
  --------------------------------------∗
  |={⊤}=> Φ #l
```

::::

```coq
  iModIntro.
  iApply "HΦ".
  iFrame "Hro".
Qed.

```

With a persistent permission, it's reasonable (and expected) that the permission need not be returned in the postcondition.

```coq
Lemma read_discarded_spec (l: loc) (x: w64) :
  {{{ l ↦[uint64T]□ #x }}}
    ![uint64T] #l
  {{{ RET #x; True }}}.
Proof.
  wp_start as "#H".
  wp_apply (wp_LoadAt with "H"). iIntros "_".
  iApply "HΦ". auto.
Qed.

```
