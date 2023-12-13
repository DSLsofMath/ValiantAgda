# ValiantAgda

This repository contains the Agda code underlying the paper

* Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda
* Jean-Philippe Bernardy, Patrik Jansson
* Accepted for LMCS 2015-12-22
* Paper: http://arxiv.org/abs/1601.07724

## Talk

(by Patrik Jansson at the [IFIP WG 2.1 meeting in Zeegse](http://www.cs.uu.nl/wiki/IFIP21/Zeegse))

http://www.cse.chalmers.se/~patrikj/talks/IFIP2.1ZeegseJansson_ParParseAlgebra.org

## Paper

* bibtex entry

```
@article{BernardyJansson2016ValiantAgda,
  author =       {Jean-Philippe Bernardy and Patrik Jansson},
  title =        {Certified Context-Free Parsing: A formalisation of
                  {Valiant}'s Algorithm in {Agda}},
  journal =      {Logical Methods in Computer Science},
  note =         {\HREF{Published 2016-06-14, available
                  at arxiv.org/abs/1601.07724}{http://arxiv.org/abs/1601.07724}},
  doi =          {10.2168/LMCS-12(2:6)2016},
  volume =       12,
  issue =        2,
  year =         2016,
}
```

## Abstract

Valiant (1975) has developed an algorithm for recognition of context free languages. As of today, it remains the algorithm with the best asymptotic complexity for this purpose. In this paper, we present an algebraic specification, implementation, and proof of correctness of a generalisation of Valiant’s algorithm. The generalisation can be used for recognition, parsing or generic calculation of the transitive closure of upper triangular matrices. The proof is certified by the Agda proof assistant. The certification is representative of state-of-the-art methods for specification and proofs in proof assistants based on type-theory. As such, this paper can be read as a tutorial for the Agda system.

## Notes

Some notes which may come in handy.

+ The paper describes how to implement, and prove correct, a parsing
  algorithm based on matrices. It is parameterised on an underlying
  base type which can be though of as the type of sets of parse
  trees. It has to support addition (union), multiplication (parser
  rules), and a bit more.
+ We use a strictly upper triangular (m+1)x(m+1) matrix to represent
  all parses of all substrings of an m-element string. You can start
  from a matrix M with the (sets of parse trees respresenting the)
  elements of the string in the cells just above the diagonal, and
  then use repeated matrix multiplication to compute parses of longer
  and longer substrings: M^m is enough to get all the results.
+ The final result (all parses of the full string) then resides in the
  upper right corner of M^m. This result is correct, but inefficient,
  and Valiant's algorithm is a way of computing the same final matrix
  but with fewer operations.
+ To make the notation less cluttered we only treat the case when
  m=2^n for some natural number n.
+ We use an interesting approach to "build up" the matrix
  datastructure together with the correctness proof starting from a
  trivial base-case for n=0 and using a uniform step to get from n to
  n+1.
+ We build two datatypes mutually recursively: the types U_n for
  "strictly upper triangular matrices of size 2^n by 2^n" and the
  types S_n for "square matrices of size 2^n by 2^n".
+ In each step we assume we have u=U_m and s=S_m and use them to
  construct U=U_{m+1} and S=S_{m+1} by describing how to assemble the
  smaller pieces. Notice that the m+1-matrices are twice as wide and
  high, thus we can fit in two by two smaller blocks as follows:

  U = u s
        u

  S = s s
      s s

+ We also include a simple inclusion u2s : u -> s
  U2S (u11 s12
           u22) = ((u2s u11)  s12
		           0          (u2s u22))

### About the base case(s)

+ In the base case, when n=0 and m=2^0=1 the 1x1 strictly upper
  triangular matrix is "all diagonal" and thus its only element
  represents zero (and the type U_0 can be implement as a unit
  type). This feels a bit like magic, thus I will explain the next
  level as well.

+ In the terminology of the paper, the function

     V : u -> s -> u -> s

  only comes in on the next level, when we "lift" all the operations
  from n to n+1, because a 1x1 matrix does not have any "square upper
  right corner" at all.

+ Now, the full definition of V_{n+1} is in the paper, using four
  recursive calls to V_n, but for understanding it, it is useful to
  expand a bit the case of n=1, thus m=2^1=2.

+ Here the matrix type U_1 has four elements but three of them are
  zero: below and on the diagonal. Only the square matrix corner is
  non-zero and contains just one element (a set of parses for the
  symbol at that position). The whole U_1 matrix stores just the set
  of parse trees for a 2-1=1 element long string.

+ The function V_1 then has type U_0 -> S_0 -> U_0 -> S_0 where U_0 is
  trivial (contains only zero) and S_0 contains just one element of
  the base type (a set of parse trees). Looking at the specification
  of V (C2.2 on page 21) we see that a=b=0, thus x=V(a,y,b) must be
  just the same as y. Thus in the "base case" the function V is
  basically the identity:

  V_1(_,y,_) = y

  Still a bit "magic" but just follows from the types and properties
  required.

+ For any larger n, the three matrices A,Y, B have subcomponents and
  the algorithm proceeds as shown at the start of p21 and in fig. 4.

+ It is instructive to work out the case n=2 (thus m=2^2=4) to get a
  feeling for how the algorithm works, but it is not necessary to do
  this "hand-expansion" to implement the algorithm - the step case
  does "the same" for all n>0.

+ {- If this were to be implemented seriously, I guess it would make
  sense to expand the equations for the lowest few levels (say to n=3
  or so) to give the compiler an easier job of optimising the code. It
  would also make sense to expand not only the definition of V at that
  level but also the data structures. n=3 means m=2^3=8, thus parsing
  of 8-1=7 symbols. -}
