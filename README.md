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
