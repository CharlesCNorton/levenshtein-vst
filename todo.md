# levenshtein-vst status

## Completed

1. `lev_dp` (Z/byte) <-> list-level bridge scaffolding is now explicit in `levenshtein_dp.v`:
   - `lev_dp_ascii`
   - `lev_dp_list`
   - `lev_dp_ascii_of_bytes`
   - `lev_dp_list_of_bytes_spec`

2. Indexed/result link is now explicit:
   - `outer_result_run`
   - `outer_result_run_eq`

3. Byte/ascii representation lemma is present in `verif_levenshtein.v`:
   - `byte_to_ascii_eq_iff`

4. `prog_correct` is no longer commented out in `verif_levenshtein.v`.

5. Bridge strategy comment at the end of `verif_levenshtein.v` is updated to the current BridgeDP-style approach.

6. Extraction alignment was handled on the Crane branch (`tests/wip/levenshtein/Levenshtein.v`).

## Still open

1. `calloc_spec` currently models successful allocation. To remove this assumption fully:
   - add/retain the NULL-check path in `levenshtein.c`,
   - regenerate `levenshtein.v`,
   - update `verif_levenshtein.v` proof obligations for the nullable allocator branch.
