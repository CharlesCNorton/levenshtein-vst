# levenshtein-vst

VST verification artifacts for a C implementation of Levenshtein distance.

## Files

- `levenshtein.c`: C implementation under verification
- `levenshtein.v`: generated/hand-maintained Coq side declarations used by VST
- `verif_levenshtein.v`: main VST proof
- `_CoqProject`: local logical path setup
- `levenshtein-vst.opam`: OPAM metadata and dependency constraints

## Build

From this directory, in a Coq/VST switch:

```bash
opam install . --deps-only
```

Then compile:

```bash
opam exec -- coqc -Q . levenshtein_vst levenshtein.v
opam exec -- coqc -Q . levenshtein_vst verif_levenshtein.v
```

The second command depends on the first.

## Notes

- This repo targets the Rocq 9 / VST toolchain (`coq` >= 9.0, < 9.2).
- It is packaged separately from Rocq/Dune-based projects.
- The current checked-in `levenshtein.v` is generated against CompCert 3.16 (`Info.version = "3.16"`), and this repo is pinned to `coq-compcert = 3.16` and `coq-vst = 2.16`.
