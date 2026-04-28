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

`BF24.lean` is a single file with no project scaffolding. To verify:

1. Have a working Lean 4 toolchain
   ([`elan`](https://github.com/leanprover/elan)) and any local Lean
   project pinned to Mathlib. The verified configuration here is
   Lean toolchain `leanprover/lean4:v4.29.0-rc6` and Mathlib commit
   [`921b8d39`](https://github.com/leanprover-community/mathlib4/commit/921b8d39f71a5c813b526f38e4033417d40b4c3d).

2. Drop `BF24.lean` into that project (any directory that is part of
   a Lean library declared in your `lakefile`).

3. Type-check with
   ```
   lake env lean BF24.lean
   ```
   For an axiom audit, append the following to the file (or to a
   sibling file that imports it) and re-run:
   ```lean
   #print axioms BF24.bf24_lemma1pp
   #print axioms BF24.bf24_sharp
   ```
   Both should report only `[propext, Classical.choice, Quot.sound]`.

## License

MIT — see `LICENSE`.
