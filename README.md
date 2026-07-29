# Shared-Readout Non-Identifiability

A machine-checked formal artifact about unique exact recovery from a shared readout.

## Core result

Let `O : X -> R` be a readout. If two distinct states produce the same record,

```text
x1 != x2    and    O x1 = O x2,
```

then no deterministic, total, single-valued decoder `D : R -> X` can be correct at both states. Equivalently, a non-injective readout has no left inverse on a fibre containing more than one state.

The core theorem is elementary. The artifact's purpose is to state it at minimal hypotheses, verify it in Coq/Rocq, and examine five proposed changes of model around it.

## Files

- [`CoreTheorem.v`](CoreTheorem.v) - formal development.
- [`paper/main.tex`](paper/main.tex) - preprint source.
- [`paper/main.pdf`](paper/main.pdf) - compiled preprint.
- [`REPRODUCE.md`](REPRODUCE.md) - verification commands and claim boundary.

## Verification

With Coq installed:

```bash
make verify
```

With Rocq 9.2:

```bash
make verify COQC="rocq compile"
```

The GitHub Actions workflow independently checks the formal source and rebuilds the paper.

## Claim boundary

The theorem concerns **unique exact recovery by a deterministic, total, single-valued decoder** from a shared record. It does not deny that a set-valued procedure can return the entire fibre, or that richer data can distinguish the states when the enriched readout is no longer shared.

## Citation

See [`CITATION.cff`](CITATION.cff).

## License

Formal code and build files are released under the MIT License. The paper and documentation are released under CC BY 4.0.
