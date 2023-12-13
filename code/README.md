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

+ Original paper version checked with Agda version 2.4.2.3 and
  depends on (and works with) `agda-stdlib-0.9`.

+ 2023-09-08: updated version check with Agda 2.6.3 and
  `agda-stdlib-1.7.3`. See changes.org for details.

+ 2023-12-13: Added continuous integration (CI) script.

+ 2023-12-13: Checked if the code works with the new agda-stdlib-2.0
  (released yesterday). Yes, locally it works, but the CI script does
  not yet support it.
