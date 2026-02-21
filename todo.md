# levenshtein-vst — open items

1. **No theorem connects `lev_dp` (Z, VST) to `lev_dp_list` (nat, Crane)** — Factor `lev_dp` into a dependency-free file over nat, import from both sides, prove isomorphism via `dp_min_spec` on each side

2. **No theorem connects `outer_result` (indexed) to `outer_result_run` (tail-recursive)** — Eliminated by #1: if both sides share a single `lev_dp` definition, the two formulations never need to be related

3. **No `byte ↔ ascii` representation lemma** — Write a standalone lemma: `(Byte.unsigned b1 =? Byte.unsigned b2)%Z = true <-> byte_to_ascii b1 = byte_to_ascii b2`, place in the VST-side bridge file

4. **`calloc_spec` axiomatizes non-NULL return** — Add a NULL check + early return to `levenshtein.c`, regenerate Clight AST, update proof to handle the new branch

5. **`prog_correct` commented out** — Uncomment, run `prove_semax_prog` / `semax_func_cons body_levenshtein_n`, fix any remaining side conditions

6. **Crane Extraction commented out** — Gate behind a build flag or restore once PR #25 merges and the rocq-crane plugin is available in the compilation environment

7. **Stale bridge strategy in `verif_levenshtein.v` comments** — Replace the comment block with a reference to BridgeDP.v's actual approach (reversal + row specification)
