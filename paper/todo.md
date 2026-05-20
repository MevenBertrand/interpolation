# TODO in the next version

- add comparison to formalisation of linear languages with masks
- fix related work to Férée et al DONE
- fix citation to Abel et al DONE
- reference to Pfenning DONE
- make repo public + links
- acks

# Reviews

> One concern would be that some interpolant types constructed by the algorithm, as mentioned in Remark 24, use product types while Čubrić would have a purely function type instead. This distinction would make the algorithm fail to construct interpolant types and terms in a product-free lambda calculus in some circumstances (e.g. the example provided in Remark 24). I believe it will be helpful to figure out a way to address the issue, making the algorithm more powerful.

WONTDO

> Some typos I found:
> 
> 1. Figure 4, \pi_i (p) -> p.i.
> 2. Lines 335 and 336, Tm_{\Sigma} -> Tm.
> 3. Line 347 \Gamma_t -> \Gamma_s (the dark red one).
> 4. Lines 360 and 362, T -> C.
> 5. Line 360, r_b[y.2] -> r_b[y.2..].

DONE

Review #148B
===========================================================================

> Question:
> - Is it possible to extract from your formalisation a concrete Rocq algorithm that outputs an interpolant? (this is not obvious to me, since your statement use the proof-irrelevant ∃ in Prop).

DONE -> added a note before Thm 22

Detailed comments:
> You could include a short plan of the paper

TODO

> Please check all your citations of [2]. Abel and Sattler are often cited referring to [2], but [2] does not include Sattler as co-author.

DONE

> p3, paragraph substitutions: It is worth mentioning that a substitution is just a function from ℕ to terms. Indeed, I was confused at first reading by looking at what you call the "primitives" in Fig 2: I initially thought they were the constructors of an inductive type describing the substitutions.

DONE -> added a footnote

> l161 Shouldn't the sentence start with "In bidirectional .."?

DONE

> l221 the A in A+B is not the same as the type A from l218, is it?

DONE

> l224 I am not sure how Definition 9 precisely relates to the formalisation. For example, in the formalisation, there is no difference between raw values and values; in the case of bottom, you require that v is covered by neutrals in the formalisation and by raw values in the paper, and there are other differences. 

TODO

> l225 It think 'if' should be omitted and also the close use of both 'or' and 'and' is a bit confusing at first reading

DONE

> l227: 'a a' looks weird. 'b a' as well, but less.

DONE

> l235: this definition of 'reducible' comes after it was used, e.g., l211, l232

DONE

> l251: I think it is worth quickly explaining how "terms covered by F" can be understood as a predicate

DONE

> l400-407: I found this paragraph unclear: what do you mean with proliferation of relations? That you need to deal with many different relations? I do not see why it makes formalisation harder.

DONE

> l426 I wonder if Trocq [1] would be relevant (I heard it is a generalization of setoid rewrite)

WONTFIX (Trocq is not supposed to be useful for this at all!?)

> l460 "Since uniform interpolation does not interpolate a particular proof": I was not able to understand this sentence

DONE

Review #148C
===========================================================================

> While non-experts are unlikely to be able to understand the details of this work, the overall strategy might be comprehensible. This is made more difficult, however, because the paper draws from a range of prior work for pieces of its strategy: e.g., the concept of covering suddenly appears in Section 3.2 as a requirement to define values. If space allows, the paper could be made more widely accessible by laying out the basic chain of reasoning of the proof to begin with, and then justifying each new concept by referring to that chain.

TODO

> Since the "subformula property" is mentioned frequently starting from the introduction, it would be good to have a basic explanation of it before Section 3.

TODO

> For ease of reading by partially or totally color-blind readers, it is best practice to use different fonts or other markers instead of relying on color alone to differentiate concepts.

DONE

> Line edits:

DONE

Meta-Review: Comments for authors
---------------------------------
The reviewers found this to be an interesting and well-presented paper that is likely to be useful for future work on proof-relevant interpolation. Including a short plan at the outset would make the overall flow easier to follow.
