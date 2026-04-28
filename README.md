# bf24-note

Lean 4 / Mathlib formalization of the elementary inequalities used in
the note

> **A note on the parameter $\ell$ in Buchbinder–Feldman's deterministic
> submodular matroid algorithm.**
> Shisheng Li, April 2026. arXiv:TBD.

The note refines the parameter $\ell$ in Algorithm 2 of

> Niv Buchbinder and Moran Feldman.
> *Deterministic algorithm and faster algorithm for submodular
> maximization subject to a matroid constraint.* To appear in
> *SIAM J. Comput.*; preliminary version in *FOCS 2024*.
> [arXiv:2408.03583](https://arxiv.org/abs/2408.03583)

via two purely elementary tightenings of the bound on
$(1+1/\ell)^{-\ell}$.

## Contents

- `BF24.lean` — single self-contained Lean 4 file. No `sorry`; only
  the standard Mathlib axioms (`propext`, `Classical.choice`,
  `Quot.sound`).

  Verified inequalities:

  | Lemma | Statement |
  |---|---|
  | `log_weak`     | $s \ge 0 \Rightarrow s/(1+s) \le \log(1+s)$ |
  | `log_pade`     | $x \ge 0 \Rightarrow 2x/(2+x) \le \log(1+x)$ |
  | `log_tail4`    | $t \ge 0 \Rightarrow t - t^2/2 + t^3/3 - t^4/4 \le \log(1+t)$ |
  | `bf24_lemma1`  | $\ell \ge 1 \Rightarrow (1+1/\ell)^\ell \cdot (1+1/\ell) \ge e$ |
  | `bf24_lemma1pp`| $\ell \ge 1 \Rightarrow (1+1/\ell)^\ell \cdot (1+1/(2\ell)) \ge e$ &nbsp;(Pólya–Szegő) |
  | `bf24_sharp`   | $\ell \ge 1 \Rightarrow (1+1/\ell)^\ell \cdot \exp(1/(2\ell) - 1/(3\ell^2) + 1/(4\ell^3)) \ge e$ &nbsp;(asymptotically sharp) |

  Reciprocal forms `bf24_lemma1_inv`, `bf24_lemma1pp_inv`,
  `bf24_sharp_inv` are also provided.

## Verifying the proofs

The repository is a self-contained Lake project. With a working Lean 4
toolchain ([`elan`](https://github.com/leanprover/elan)) installed:

```
git clone https://github.com/daizisheng/bf24-note.git
cd bf24-note
lake exe cache get   # fetch precompiled Mathlib oleans (recommended; first run only)
lake build           # type-checks BF24.lean against pinned Mathlib
```

The Lean toolchain (`leanprover/lean4:v4.29.0-rc6`) is pinned via
`lean-toolchain`; the Mathlib commit
([`921b8d39`](https://github.com/leanprover-community/mathlib4/commit/921b8d39f71a5c813b526f38e4033417d40b4c3d))
is pinned via `lake-manifest.json`. `lake exe cache get` is optional
but lets you skip rebuilding Mathlib from source (saves ~30 minutes
on a typical machine).

For an axiom audit, run

```
lake env lean BF24Audit.lean
```

where `BF24Audit.lean` is the one-line file

```lean
import BF24
#print axioms BF24.bf24_lemma1pp
#print axioms BF24.bf24_sharp
```

Both should report only `[propext, Classical.choice, Quot.sound]`.

## License

MIT — see `LICENSE`.
