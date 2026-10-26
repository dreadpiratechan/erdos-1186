# Certificate data for the five `RegionLB` statements (lane excertsdp, branch agent/n3d)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  Starting multipliers: reviewer rev1186c's exact certificates (`data/certs_rev1186c.json`); everything below
(model code, margin, rounding, integer data, verifier) is this lane's own code.

Files (all under `problems/1186/exact/` in the research repository; in this repository `computation/theorem-c/`):

| file | what |
|---|---|
| `data/cert_region{1..5}.json` | the data, one per region (schema below) |
| `verify_certs.py` | exact verifier, a SECOND implementation of `N` (atom Gram formulation) + identity at random points + PSD cert; `py -I verify_certs.py [r..]` |
| `sdpmodel.py` | the model written from `P1186Ex.lean` (`Lval`, `pterm`, `mval`, forms); `load_grid` cross-checks `data/grids.json` against `P1186ExData.lean` and a recount of `A4` |
| `make_certs.py`, `psdcert.py`, `import_rev.py` | generator (rounding, margin, derived multipliers, Cholesky) |

## What is certified

For region `r` with grid `G` (`G24` for r = 1,2,3; `G8` for r = 4,5) and `lo <= m <= hi` (`REGIONS` in `sdpmodel.py`:
r1 `[0, 1/5]`, r2 `[1/5, 3/10]`, r3 `[3/10, 2/5]`, r4 `[2/5, 9/20]`, r5 `[9/20, 1/2]`), for every `y : Fin N -> R` with
`0 <= y_i <= 1` and `lo <= m(y) <= hi`:

    Lval G y  >=  Ltheta(y)  =  v'S v  +  sum_f mu_f f(y)  >=  0,          v = (1, y_0, ..., y_{N-1})

* `Lval` is the interface's (`P1186Ex.lean`): `sum_i (a_i y_i + b_i y_i^2) + sum_{i,j} pterm i j (y_i) (y_j)`, `a_i = G.ai i`, `b_i = G.bi i` EXACTLY as in `P1186ExData.lean` (no truncation, no change).
* `Ltheta`: every `pterm i j` (a `max` of two polynomials) is replaced by the convex combination below with `theta_ij in [0,1]`; `Ltheta <= Lval` pointwise.
* `f` ranges over the FORMS (table below), each `>= 0` on the region, with multiplier `mu_f >= 0`.
* `S` is a symmetric `(N+1) x (N+1)` matrix, PSD, with a margin; **`B' = 0`** (the reviewers' constant `B > 0` has been moved into `S_00`; only `>= 0` is needed).
  The identity `Ltheta(y) - sum_f mu_f f(y) = v'Sv` is an identity of quadratic polynomials in `y`; `S` is DETERMINED by the data (theta, mu): `S` = matrix of `Ltheta - sum mu_f f`.
* Region 1 (the inner region, `m <= 1/5`): the constant row/column of `S` is ZERO (`L(0) = 0`), so only the `N x N` block `P = S[1:,1:]` is stored and certified PSD; `Ltheta - sum mu f = y'Py`.

## Conventions

* Cells `i, j in 0..N-1` (0-based), `N = 130` (G24) or `146` (G8). Pair `(i,j)` is ORDERED (`i` = end side, `j` = middle side, as in `Lval`).
* Pair kind from the grid's `A4`: `full` iff `A4 i j = 4 * len_i * len_j` (`A_out = 0`), `empty` iff `A4 i j = 0` (`A_in = 0`), otherwise `cut`.
  `len_i = pts[i+1] - pts[i]`, `w_i = len_i/1096`, `A_in = A4/(4*1096^2)`, `A_out = w_i w_j - A_in`, `P = w_i w_j y_i y_j`.
* `theta` = weight of the CONSTANT branch of the `max`:
  * `sgn_i sgn_j = +1`:  `pterm = max(0, P - A_out)  >=  (1-theta)(P - A_out) + theta * 0`
  * `sgn_i sgn_j = -1`:  `pterm = max(-A_in, -P)     >=  theta (-A_in) + (1-theta)(-P)`
  Defaults (NOT stored, same rule for all regions): `full -> theta = 0`, `empty -> theta = 1` (then the term is exactly `pterm`: `P` / `-P` resp. `0`).
  Cut pairs carry their `theta` in `cuts`.  Soundness for any `theta in [0,1]` is just `max(x, z) >= (1-t) x + t z`.
* `m = sum_i w_i y_i`.  Atoms (all `>= 0` on the region): `y_i`, `o_i = 1 - y_i`, `ml = m - lo`, `hm = hi - m`, and the constant `1`.

## Forms (`forms` entries are `[kind, indices..., numerator]`, `mu_f = numerator / mu_den`, numerator integer `>= 0`)

| kind | args | polynomial `f` | `f >= 0` because |
|---|---|---|---|
| `y` | `i` | `y_i` | atom |
| `o` | `i` | `1 - y_i` | atom |
| `ml` | | `m - lo` | region |
| `hm` | | `hi - m` | region |
| `yy` | `i j` (`i <= j`) | `y_i y_j` | product of atoms |
| `oo` | `i j` (`i <= j`) | `(1-y_i)(1-y_j)` | " |
| `yo` | `i j` (any, `i = j` allowed) | `y_i (1 - y_j)` | " |
| `yml` | `i` | `y_i (m - lo)` | " |
| `oml` | `i` | `(1-y_i)(m - lo)` | " |
| `yhm` | `i` | `y_i (hi - m)` | " |
| `ohm` | `i` | `(1-y_i)(hi - m)` | " |
| `mhm` | | `(m-lo)(hi-m)` | " |
| `tri` | `i j k s1 s2 s3` (`i<j<k`, `s1 s2 s3 = +1`, `s in {+-1}`) | `1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k`, `z = 1 - 2y` | multilinear in `z`; at the 8 cube vertices it is 0 or 4 (it is 4 when the three products are `+,+,+` and 0 when exactly two are `-`), hence `>= 0` on `[0,1]^3` |

`tri` is a sum of two products of three atoms (so `tri >= 0` needs no case analysis): choose signs `e_i = 1, e_j = s1, e_k = s3` (then `e_j e_k = s2`
because `s1 s2 s3 = 1`), and let `P_x = o_x` if `e_x = +1` else `y_x`, `Q_x = y_x` if `e_x = +1` else `o_x`; then
`tri = 4 (P_i P_j P_k + Q_i Q_j Q_k)` EXACTLY (it is `(1/2)[prod (1 + e_x z_x) + prod (1 - e_x z_x)]` with `1 + z = 2 o`, `1 - z = 2 y`;
checked on 800 random rational points over all four admissible sign patterns).

All product kinds are `l_a * l_b` for two atoms (the kinds `y/o/ml/hm` are an atom times the constant atom `1`).  With the atom
coefficient matrix `A` (row `a` = coefficients of atom `l_a` over `v`) and the entrywise-nonnegative symmetric matrix `MU` over atoms
(`MU[a][b] = MU[b][a] = mu_f` for `f = l_a l_b`, `a != b`; `MU[a][a] = 2 mu_f` for `f = l_a^2`), one has
`sum_{product f} mu_f f(y) = (1/2) (A v)' MU (A v)`, i.e. these forms contribute `A' MU A / 2` to `S` (negatively), as in `verify_certs.py::rebuild_N`.
`tri` forms are separate (explicit expansion `1 + s1+s2+s3 - 2[(s1+s3) y_i + (s1+s2) y_j + (s2+s3) y_k] + 4[s1 y_i y_j + s2 y_j y_k + s3 y_i y_k]`).

### Polynomial expansion of every form (so `S` can be computed without reading the Python)

`m = sum_k w_k y_k`.  A quadratic polynomial `c + sum_i l_i y_i + sum_{i<=j} q_ij y_i y_j` is the quadratic form `v'Mv`, `v = (1, y)`, with
`M_00 = c`, `M_0i = M_i0 = l_i/2`, `M_ii = q_ii`, `M_ij = M_ji = q_ij/2` (`i != j`).  The forms are:

| kind | polynomial |
|---|---|
| `y i` | `y_i` |
| `o i` | `1 - y_i` |
| `ml` | `-lo + sum_k w_k y_k` |
| `hm` | `hi - sum_k w_k y_k` |
| `yy i j` | `y_i y_j` (`y_i^2` if `i = j`) |
| `oo i j` | `1 - y_i - y_j + y_i y_j` (`1 - 2 y_i + y_i^2` if `i = j`) |
| `yo i j` | `y_i - y_i y_j` (`y_i - y_i^2` if `i = j`) |
| `yml i` | `-lo y_i + sum_k w_k y_i y_k` (the `k = i` term is `w_i y_i^2`) |
| `oml i` | `(1 - y_i)(m - lo) = -lo + sum_k w_k y_k + lo y_i - sum_k w_k y_i y_k` |
| `yhm i` | `hi y_i - sum_k w_k y_i y_k` |
| `ohm i` | `(1 - y_i)(hi - m) = hi - sum_k w_k y_k - hi y_i + sum_k w_k y_i y_k` |
| `mhm` | `(m - lo)(hi - m) = -lo hi + (lo + hi) m - m^2`, `m^2 = sum_{j,k} w_j w_k y_j y_k` |
| `tri i j k s1 s2 s3` | `(1 + s1 + s2 + s3) - 2[(s1+s3) y_i + (s1+s2) y_j + (s2+s3) y_k] + 4[s1 y_i y_j + s2 y_j y_k + s3 y_i y_k]` |

`L_theta` is `sum_i (a_i y_i + b_i y_i^2)` plus, for every ordered pair `(i, j)` (including `i = j`), `(1-theta)(w_i w_j y_i y_j - A_out)` if `sgn_i sgn_j = +1`,
resp. `-theta A_in - (1-theta) w_i w_j y_i y_j` if `sgn_i sgn_j = -1`, with `theta` from the defaults/`cuts` above.

## JSON schema (`cert_region{r}.json`)

```
format      "excertsdp-v1"          header: credit line
region      r;  grid "G24"|"G8";  lo, hi  "p/q";  n = N cells
theta_den   Q = 2^K  (K = 40);   mu_den (= Q for regions 2-5; = D for region 1);   bprime "0"
cuts        [[i, j, theta_num], ...]   ALL cut pairs, lexicographic in (i, j);  theta = theta_num / theta_den in [0, 1]
forms       [[kind, idx..., num], ...] sorted, no duplicates, num >= 0 integer
Z0          360364800 = 2^8 * 3 * 5^2 * 137^2 = 300 * 1096^2 : common denominator of all fixed data (a_i, b_i, w_i w_j, A4/(4*1096^2), lo, hi)
D           Q * Z0:  N := D * S is an integer matrix (checked)
const_row_zero  true for region 1 only (then N is the N x N block, otherwise (N+1) x (N+1) with index 0 = constant)
N           the integer matrix D * S  (B' = 0), symmetric
chol        {T2, rows, min_slack}:  rows[i] = [C_i0 .. C_ii] integer lower-triangular;  E := T2*N - C C^T (exact) has every row
            diagonally dominant:  E_ii >= sum_{j != i} |E_ij|  (min_slack = min_i of the difference, > 0)  =>  N is PSD
margin      {lambda_min_float, lambda_max_float, eta_pow2 = k}:  S >= 2^-k * I is certified (dominance for N - ceil(D/2^k) I)
```

`S = N / D`.  Integrality/derivation of `N` from `(cuts, forms)`: `verify_certs.py::rebuild_N` is a complete, short second implementation
(the Lean generator can port it): `L_theta` part (`a_i/2` on the constant row, `b_i` on the diagonal, the pair terms `+- (1-theta) w_i w_j`
split `1/2` onto `(i,j)` and `(j,i)`, constants `-(1-theta) A_out` resp. `-theta A_in`) minus the forms.

Magnitudes (K = 40): `N` entries up to about `2^68`; `Q = 2^40`; Cholesky entries about `2^31`; `T2 = 1` suffices in all five regions.

## Region data (this commit)

| r | grid | n | cut pairs | forms (incl. triangles) | `lambda_min(S)` | certified `S >= 2^-k I` |
|---|---|---|---|---|---|---|
| 1 | G24 | 130 | 318 | 21998 (0 tri) | 1.69e-6 (y-block) | 2^-20 |
| 2 | G24 | 130 | 318 | 9011 (0 tri) | 3.40e-6 | 2^-19 |
| 3 | G24 | 130 | 318 | 9863 (6817 tri) | 3.05e-6 | 2^-19 |
| 4 | G8 | 146 | 294 | 5180 (0 tri) | 3.33e-6 | 2^-19 |
| 5 | G8 | 146 | 294 | 4144 (1200 tri) | 5.57e-6 | 2^-18 |

How the margin was made: the reviewers' `S_rev` (PSD, smallest eigenvalue ~1e-12) plus `B e_0 e_0'` (B ~ 2.7e-4 .. 5.1e-4) is raised by
adding `eps` to the multiplier of each box form `y_i (1 - y_i)` (`yo i i`): that adds `eps * sum_i (e_i - e_0/2)(e_i - e_0/2)'` and subtracts
`eps*n/4` from `S_00`; with `eps*n/4 < B` the result is `S_rev + (PSD with smallest eigenvalue ~ B/n)`.  Region 1 has no constant slack
(its margin is the reviewers' own: `lambda_min(P) = 1.69e-6`); its `y` multipliers `c_i` are DERIVED (so that the constant row of `S` is exactly 0) and
are stored over the denominator `D`.

## Fidelity of the model to the Lean definitions

`fidelity.lean` (run through the gate: `lake env lean ../problems/1186/out/fidelity.lean`, after `lake build Erdos.Proofs.P1186Ex`) uses the REAL
computable definitions `Grid.N/lo/hi/wt/ai/bi/sgn/A4` (hence the real `K4`, `c1`, `sg`) and a line-by-line `R -> Q` copy of `pterm`, `Lval`, `mval`
(the only `noncomputable` ones), evaluates `N`, six values of `A4`, five signs, and `mval`, `Lval` at 6 rational test points per grid (including a
point with all `y = 1`, a 0/1 point and three mixed points, so both branches of the `max` occur); its output is saved in `data/fidelity_lean_out.txt`
and `fidelity_check.py` compares it exactly with `sdpmodel.py` (`py -I fidelity_check.py` -> `FIDELITY OK`).  So `sdpmodel.py` (which the certificates
and `verify_certs.py` use) agrees with the Lean `Lval` / `mval` / `A4` / `sgn` / `N` at those points; it is a check of the model at sample points,
not a proof of equality of the two definitions.

## Size of the Lean-side arithmetic (for the generator)

`N` is dense (n = 130/131/131/147/147 including the constant row), entries below `2^63`; the Cholesky rows `C` are dense lower triangular
(8.5K - 10.9K entries below `2^32`); `T2 = 1`.  Checking `E = N - C C^T` costs `n^3/6` integer multiply-adds (about 0.37M for G24, 0.53M for G8) plus
`n^2` for the dominance sums.  Number of form multipliers: 22.0K / 9.0K / 9.9K / 5.2K / 4.1K (region 1..5), of which `tri`: 0 / 0 / 6817 / 0 / 1200.

## Soundness status

Verified by `verify_certs.py` (exact integer / rational arithmetic, ~20 s for all five): structure, `N` rebuilt by a second implementation,
the identity at 6 random rational points per region from the Lean-copied definitions (`sdpmodel.py`), `Lval >= Ltheta`, every form `>= 0` and
`Lval >= Ltheta >= 0` at random region points, dominance certificate of `N` and of the margin.  `verify_pd_bareiss.py` is a second, independent exact PD check (fraction-free elimination of
`N - ceil(D/2^k) I`, all leading principal minors `> 0`; no Cholesky data used, about 1 minute for all five).  What this does NOT replace: the Lean proof
(this is data + an independent exact check, evidence for the generator, not a proof of `RegionLB`).
