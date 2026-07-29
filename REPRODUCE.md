# Reproduce and audit

## Formal theorem

The formal source requires `QArith` from the standard Coq/Rocq library.

```bash
coqc -q CoreTheorem.v
```

For Rocq 9.2:

```bash
rocq compile -q CoreTheorem.v
```

The verification target also rejects source declarations beginning with `Axiom`, `Parameter`, `Conjecture`, or `Admitted`.

```bash
make formal
```

## Paper

A TeX Live installation with `newpxtext`, `newpxmath`, `microtype`, and `hyperref` is required.

```bash
make paper
```

The canonical source is `paper/main.tex`; the tracked PDF is a convenience copy.

## Exact formal claim

For arbitrary types `X` and `R`, a readout `O : X -> R`, and distinct states `x1` and `x2`, the development proves:

```text
O x1 = O x2
  -> no D : R -> X is correct at both x1 and x2.
```

This is a theorem about deterministic, total, single-valued decoding. It is not a claim that either state cannot be named independently, that set-valued recovery is impossible, or that additional observations cannot restore identifiability.
