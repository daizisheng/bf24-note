# bf24-note

Lean 4 / Mathlib formalization of the elementary inequalities used in
the note

> **A note on the parameter $\ell$ in Buchbinder–Feldman's deterministic
> $(1-1/e-\varepsilon)$-approximation for monotone submodular maximization
> under a matroid constraint.**
> Shisheng Li, April 2026.

The note refines the parameter $\ell$ in Algorithm 2 of

> Niv Buchbinder and Moran Feldman.
> *Deterministic algorithm and faster algorithm for submodular
> maximization subject to a matroid constraint.* SIAM J. Computing
> 2024 (preliminary in FOCS 2024).
> [arXiv:2408.03583](https://arxiv.org/abs/2408.03583)

via two purely elementary tightenings of the bound on $(1+1/\ell)^{-\ell}$.

## Contents

- `BF24.lean` — single self-contained Lean 4 file, builds against
  [Mathlib](https://github.com/leanprover-community/mathlib4).
  No `sorry`, no extra axioms.

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

## License

MIT — see `LICENSE`.
