# Earlier runs: the paper package, 26 October 2026

These are the logs of the checks run on the paper's reproducibility package on 26 October 2026, before this repository
existed. They are kept for reference: the run of record for this repository is in `../../logs/`. The Lean sources they
were run on are the 342 files of `lean/Erdos/Proofs/` (same SHA-256, see `../../lean_modules.sha256`). Local folder names
of the machine are replaced by `<research-repository>` and `<paper-workspace>`; nothing else was changed.

The builds used plain `lean` 4.27.0 on the compiled Mathlib of the research repository, through
`../../build_closure.py` (a module-by-module build in dependency order), not `lake`.

| File | What it records |
|---|---|
| `standalone_build_log.jsonl`, `standalone_build_stdout.txt` | the build of the 189 modules of Theorems A and B from the package's sources (08:42 to 09:29 PDT): every return code 0 |
| `standalone_build_claim_log.jsonl`, `standalone_build_claim_stdout.txt` | the build of the closure of Theorems A, B and C (341 modules): the 189 above skipped as up to date, 152 compiled (12:36 to 14:04 PDT), every return code 0 |
| `lean_build_controls.log` | the build of `P1186ExCertCtl` (the negative controls of the Theorem C checker) and its closure: return code 0 |
| `Audit1186.lean`, `lean_axiom_audit.log`, `lean_axiom_audit_shipped_tree.log` | statements and `#print axioms` of Theorems A and B and their parts, run at 08:40 (before the standalone build) and at 15:15 on the rebuilt package tree: all `[propext, Classical.choice, Quot.sound]` |
| `AuditClaim1186.lean`, `lean_axiom_audit_claim_tree.log` | the same for Theorem C and its parts (15 theorems), on the rebuilt package tree |
| `closure_scan.log`, `closure_scan_shipped_tree.log`, `closure_scan_claim_tree.log` | the lines of the closures that contain a forbidden word (`sorry`, `native_decide`, `axiom` and others): all are comments saying "no `native_decide`" (2 and 11 lines). The first two report different byte counts for the same 189 modules (12,580,357 and 12,571,230, at 08:26 and 10:19); the cause was not recorded |
| `fidelity_check.log` | the text comparison of the definitions and statements with the upstream file: all OK |
| `lean4checker_claim_attempt1_failed.log`, `lean4checker_claim_attempt2_killed.log` | two attempts to replay the closure of Theorem C with lean4checker, in chunks of eight modules per process. Neither got past the first chunk: the first stopped with "failed to read file" on a Mathlib `.olean` that exists (not diagnosed), the second was killed by the machine's 9 GB memory cap. No replay was claimed from these runs |

`Audit1186.lean` and `AuditClaim1186.lean` are not part of this repository's checks; `../Headline.lean` and
`../AxiomAudit.lean` supersede them. (Their module names are the same as here, so `lake env lean` from `lean/` runs them.)
