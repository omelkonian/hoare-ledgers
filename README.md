# Separation logic for UTXO-based blockchain ledgers

The Agda formalization (under folder `/src/`) depends on [formal-prelude](https://github.com/omelkonian/formal-prelude),
make sure you have it installed (either manually or by simply running `$ make install-prelude`). 

## Design Approaches

Initial tried the following:
- [Ledger-Shallow](https://github.com/omelkonian/hoare-ledgers/tree/shallow): Shallow embedding using HOAS, both for states `S : Part -> Z` and logical formulas `PredS : S -> Set`.
  + cannot express separating conjunction...

- [Ledger-Middle](https://github.com/omelkonian/hoare-ledgers/tree/middle): Between shallow and deep embedding, using "deep" states `S : Map Part Z` and "shallow" formulas `PredS : S -> Set`.
  + here we can prove some inference rules of Separation Logic (e.g. that _∗_ is commutative), but still cannot express `[FRAME]` and `[INTERLEAVE]`

- [Ledger-Deep](https://github.com/omelkonian/hoare-ledgers/tree/deep): Deep embedding, both for states `S : Map Part Z` and logical formulas `data PredS/Assertion : Set where ...`. 
  + currently struggling to prove the `[FRAME]` rule..

Finally decided on another 'middle' with **shallow** embedding for states `S : Map Part N ~ Part -> N` and **deep** embedding for logical formulas `data Assertion : Set where ...`.
