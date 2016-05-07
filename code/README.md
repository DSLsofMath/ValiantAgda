# ValiantAgda code

Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda

| File                       | Contents                  |
| -------------------------- | ------------------------- |
| ValiantRefinement.agda     | Main file of the development - imports the rest.
| Preliminaries.agda         | Defines `Rel`, `Entire`, `fun`, `correct`, `UniqueSolution`, `LowerBound`, `Least`
| SemiNearRingRecords.agda   | Defines `record SemiNearRing`, `SemiNearRing2` with several fields and operations each
| ZeroLemmas.agda            | Defines `zeroˡLemma`, `zeroʳLemma`, `zeroˡʳLemma`, `zeroLemma01`, `zeroLemma10`, `zeroLemma00`, `zeroLemma11`
| OrderLemmas.agda           | Defines `monoPlusLeft`, `monoTimesLeft`, `_[+]_`, `_[*]_`, `≤s-trans`, `≃sTo≤s`
| CommAssocLemmas.agda       | Defines `SA`, `lemmaCommAssoc00`, `lemmaCommAssoc01`. Imports nothing.

Checked with Agda version 2.4.2.3.

Depends on (and works with) `agda-stdlib-0.9`.
