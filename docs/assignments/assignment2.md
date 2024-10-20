---
order: 3
shortTitle: "Assignment 2"
icon: pen-fancy
date: 2024-10-04 08:00:00 -5
---

# Assignment 2: Separation logic theory

::: info

This is a theory assignment: you'll submit written responses rather than doing proofs in a computer.

:::

In this assignment, you'll answer some questions about Hoare logic and separation logic on paper rather than submitting mechanized proofs. The goal is to build and exercise your mental model for the specifications, proof rules, and program proofs, without having to work out all the details or translate your argument to something Coq understands. The two downsides are that you have to do all the calculations yourself, and there's no computer patiently checking your work and confirming when you're done; you'll have to think about it and wait for (much slower) feedback from me.

<!-- @include: ../notes/macros.snippet.md -->

**This assignment is due Tuesday, Oct 22, 2024 at 11pm.** Submit solutions to [Canvas](https://canvas.wisc.edu/courses/425519/assignments/2471003). You can submit either handwritten (digital or paper) answers, or typeset your solution with LaTeX using the <a href="./assignment2_template.tex" download>assignment 2 template <HopeIcon icon="download" /></a>.

## Exercise 1

> Rule of consequence (5 points)

[Prove the rule of consequence](../notes/hoare.md#hoare-rules) for Hoare logic, from the [soundness definition](../notes/hoare.md#soundness) for a Hoare triple.

## Exercise 2

> Understanding separation logic propositions (10 points)

For each separation logic proposition below, describe precisely the set of heaps where it is true. If you think the answer is non-trivial or are unsure of your answer, briefly explain so I can see your thought process. Assume a linear separation logic - remember that $\True(h)$ holds for any heap, even in a linear logic.

Note that the overlapping conjunction $(P \land Q)(h)$ is defined to be true when $P(h)$ and $Q(h)$. While not commonly used, this is a perfectly valid separation logic proposition.

If a variable is _free_ (that is, not bound by a $\forall$ or $\exists$ quantifier), assume it to be a constant throughout the problem (but each problem is independent).

Here is a worked example:

$\ell_1 \mapsto v \sep \ell_2 \mapsto v$. If $\ell_1 \neq \ell_2$, holds for only the two-element heap $\{\ell_1 \mapsto v; \ell_2 \mapsto v\}$; if $\ell_1 = \ell_2$, never holds.

- (a) $\exists v.\, \ell \pointsto v$
- (b) $\exists \ell'.\, \ell' \pointsto v$
- (c) $\forall v.\, \ell \pointsto v$
- (d) $(\ell \pointsto v) \sep \True$
- (e) $(\ell \pointsto v) \sep (\True \land \emp)$
- (f) $\ell \pointsto v \land \ell \pointsto v$
- (g) $\ell \pointsto v \sep \ell \pointsto v$
- (h) $(\exists v.\, \ell_1 \pointsto v) \sep (\exists \ell.\, \ell \pointsto \num{3})$
- (i) $(\exists v.\, \ell \pointsto v) \land (\exists \ell'.\, \ell' \pointsto \num{3})$
- (j) $(\exists x. \lift{x > 2}) \sep (\exists x. \lift{x < 2})$

## Exercise 3

> Frame rule vs weakening (10 points)

Compare the separation logic frame rule to the rule for weakening. Explain why the weaken rule does not imply the frame rule. Explain why the frame rule does not imply the weaken rule. These explanations are not meant to be fully formal proofs (which is well beyond the scope of this class for this question), but should aim to be convincing explanations - in this case, convincing me that you've understood what these rules mean.

## Exercise 4

> A bug in separation logic? (15 points)

Your friend Ben Bitdiddle has read the section on [recursion and loops](../notes/sep-logic.md#recursion-loops) and thinks he has found a bug in separation logic. He claims to have proven the following triple:

$$\hoare{\True}{(\rec{f}{x} f \, x) \, ()}{\fun{\_} \False}$$

"This proves False with no hypotheses, which makes separation logic unsound!" he exclaims, a little too excited at having broken what you spent so much time learning.

What do you say to Ben?

## Exercise 5

> Verifying linked list implementation (35 points, total)

We will develop a linked list implementation in our "lecture notes" programming language (which I'll call `expr` here) and give it a specification using a _representation predicate_.

This problem will follow the presentation of linked lists in Robbert Krebbers's program verification course. We will be following the notes from that class on [separation logic](https://gitlab.science.ru.nl/program-verification/course-2023-2024/-/blob/master/lectures/week10.md).

### Exercise 5a

> Reading (0 points)

Read the notes linked above. You should be able to skim the first part, since it's very similar to our own class notes. The new material relevant to this problem starts at [Linked data structures and representation predicates](https://gitlab.science.ru.nl/program-verification/course-2023-2024/-/blob/master/lectures/week10.md#linked-data-structures-and-representation-predicates).

Be careful reading the notation: code in the language is written in Coq syntax, with type annotations to clarify what's going on, but these are not functional programs. The types are mostly straightforward to understand, except that `ref T` is used for a pointer to a `T` (ref stands for "reference"); a value of this type will always be a location, and when dereferenced will return a value of type `T`. The syntax `alloc`, `!x`, and `x ← v` is the same as our programming language.

Our language did not have a way of doing pattern matching, which makes it awkward to implement linked lists. For the purpose of this exercise let's assume it has a way to represent the inductive type for a linked list holding values of type `A`:

```coq title="expr"
llist A :=
| lnil
| lcons (hd: A) (tl: ref (llist A))
```

Notice that this is not like the Coq `list A` type in that the `tl` field is a _pointer_ to the rest of the list.

To use this inductive, we need pattern matching. Assume a `match` construct in `expr` that behaves like Coq's `match`; here's an example, the `sum_list` from the notes linked above:

```coq title="expr"
Fixpoint sum_list (x: ref nat) (l: ilist nat) :=
  match l
  | lnil => ()
  | lcons hd tl =>
    x <- !x + hd
    let k := !tl in
    sum_list x k
  end
```

We use `Fixpoint` for clarity but this function can also be written using the recursive anonymous function $\rec{f}{x}{e}$ in the notes.

The program verification notes linked above include several examples of proof outlines, especially those using pattern matching.

To specify functions over linked lists, we will use the following _representation invariant_ for linked lists (this is a Coq definition for a separation logic proposition, except that `v` would just be a `val`; we give here its type in the expr language for clarity):

```coq
Fixpoint list_rep (v: llist A) (xs: list A): hProp :=
  match xs with
  | [] => v = lnil
  | hd :: x2 => ∃ tl l',
     (v = lcons hd tl) ∗
     (tl ↦ l') ∗
     list_rep l' xs'
   end.
```

This definition says that `v` is the value of a linked list that holds abstract values `xs` in the current heap. It relates a programming value `v`, which has references, to a purely mathematical `list`. Importantly, `list_rep` is a separation logic proposition `hProp`; it only makes sense to have a linked list in some heap, since the code representation involves pointers. However the mathematical part does _not_ involve pointers.

This is the separation logic analog to the ADT specifications we saw earlier for functional programs. The model of a linked list will be a Coq `list`, as expected. We will be using [abstraction relations](./adt_invariants#abstraction-relations) rather than functions. If linked lists were implemented in a functional programming language, we would specify `sum_list` using an abstraction relation `list_absr l xs : Prop` that said `∀ l xs, list_absr l xs → sum_list l = sum xs`. Now, a similar specification is written as a triple `{list_rep l xs} sum_list l {λv. v = sum xs * list_rep l xs}`. Notice that we need to re-state `list_rep l xs` in the postcondition; otherwise, the specification allows `sum_list` to de-allocate `l`, or re-use its memory for something else.

::: info Side note: where does "xs" come from?

The name `xs` is meant to evoke `x`s, the plural of `x`. It's a common variable name for a list of values (similarly you'll see `ys`) in functional languages like OCaml or Haskell.

:::

This shorthand is also useful for a reference to a linked list, since that is how the tail is stored in an `llist A`:

```coq
Definition list_ref_rep (v: ref (llist A)) (xs: list A): hProp :=
  ∃ (p: loc) (l: llist A), (v = p) * (p ↦ l) * list_rep l xs.
```

There is nothing to turn in for this part.

### Exercise 5b

> Specification for append (10 points)

Consider the following function for appending two linked lists. It's your job to figure out exactly how it works (that is, how does it manage the memory of the two lists?).

```coq title="expr"
Fixpoint app_list (l1: ref (llist A)) (l2: ref (llist A)) :=
  match !l1 with
  | lnil => l1 <- !l2; free l2; ()
  | lcons hd tl => app_list tl y
  end
```

Write a specification for `app_list l1 l2`. **You may assume an affine separation logic**, so the postcondition can drop any facts you don't think are relevant.

### Exercise 5c

> Proof of append (15 points)

Write a proof outline that shows `app_list l1 l2` meets your specification. You may assume an affine separation logic.

Remember that if you think something is wrong here, you may need to re-visit your specification. I can check your specification and give feedback before you spend too much time proving it.

## Exercise 5d

> Specification for tail (10 points)

Let us now implement a function to get the tail of a list:

```coq title="expr"
Definition tail (l: llist A) : llist A :=
match x with
| lnil => ()
| lcons hd tl => !tl
```

Consider the following specification for `tail`:

```txt
[ list_rep l (x :: xs) ]
  tail l
[ v. list_rep l (x :: xs) * list_rep v xs ]
```

Is this specification true? If yes, prove this specification. If not, explain why, find another valid specification, and prove it.

## Bonus exercise (optional)

> 5-15 bonus points (depending on importance of contribution)

Find a typo in the lecture notes on Hoare logic or Separation Logic. Submit a GitHub pull request with a fix.
