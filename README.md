# levenshtein-vst

VST verification artifacts for a C implementation of Levenshtein distance.

## Files

- `levenshtein.c`: C implementation under verification
- `levenshtein.v`: generated/hand-maintained Coq side declarations used by VST
- `verif_levenshtein.v`: main VST proof
- `_CoqProject`: local logical path setup

## Build

From this directory:

```powershell
& 'C:\Coq-Platform~8.19~2024.10\bin\coqc.exe' -Q . levenshtein_vst levenshtein.v
& 'C:\Coq-Platform~8.19~2024.10\bin\coqc.exe' -Q . levenshtein_vst verif_levenshtein.v
```

The second command depends on the first.

## Notes

- This repo targets the VST/CompCert toolchain (Coq 8.19 environment).
- It is packaged separately from Rocq/Dune-based projects.
