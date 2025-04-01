# Separation logic for UTXO-based blockchain ledgers [![CI](https://github.com/omelkonian/hoare-ledgers/workflows/CI/badge.svg)](https://github.com/omelkonian/hoare-ledgers/actions) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.15097592.svg)](https://doi.org/10.5281/zenodo.15097592)

Browse the Agda code in HTML [here](http://omelkonian.github.io/hoare-ledgers).

This Agda formalization depends on [formal-prelude](https://github.com/omelkonian/formal-prelude),
make sure you have it installed.

## Design Approaches

Various design decisions are modelled in each sub-directory, answering the following dilemmas:

- Shallow or deep embedding of states?
  + i.e. `S : Part → ℕ` or `S : Map⟨ Part → ℕ ⟩`

- Shallow or deep embedding of logic formulas?
  + i.e. `P : S → Set` or `data P : Set where ...`

- Shallow or deep embedding of Hoare triples?
  + i.e. `{P}l{Q} = ∀ s. P(s) → Q(⟦l⟧s)` or `data {P}l{Q} where ...`

- Separate at the level of participants or values?
  + i.e. `s₁ ⊎ s₂ ≈ s` or `s₁ ◇ s₂ ≈ s`

- Can we easily extend everything from simple linear ledgers to UTxO-based ledgers?
