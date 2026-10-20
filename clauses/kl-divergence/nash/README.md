# Theorem N: reproduction

Layout:
- `code/`: the shared rigorous core.
  - `nash_iv.py`: interval arithmetic, with rigorous log/sin/cos by series.
  - `nash_core.py`, `nash_core3.py`: the CKM chart, jets and kernels.
  - `nash_copies*.py`: the exact DKZ copies.
  - `nash_local_gs*.py`, `nash_tm*.py`: the local cubes.
  - `nash_bb.py`: local-cube loading and containment.
- `code/fast/`: the global branch-and-bound.
  - `track.py`: the tracking bound, numpy reference implementation.
  - `nbjets.py`, `nbtrack.py`: numba production implementation.
  - `bb_nb.py`: production driver; `bb_track.py`: domain and numpy driver.
  - `check_run.py`: completeness check; `crosscheck_numpy.py`: independent re-run.
  - `TRACK_METHOD.md`: derivation of the bound.
- `certificates/local/`: the two local cube certificates, as JSON summaries plus leaf arrays, with code hashes.
- `certificates/global/`: all 4,224 per-region results (`bbnb_results.tar.gz`), the completeness report and the code
  hashes.
- `audit/AUDIT_TRACK.md`: the independent audit, in three rounds.

Requirements:
- Python 3.12 with numpy, scipy, mpmath and numba 0.67 for the numba engine.
- Any recent Python with numpy, scipy and mpmath for the numpy reference and the local cubes.
- sympy for `nash_copies_exact.py`.

Steps (run from `code/`):
1. Exact copies:
   ```
   python nash_copies_exact.py
   ```
2. Local cubes, about 70 minutes each. These write `nash_local_gs_<key>.json` and `logs/`.
   ```
   python nash_local_gs2.py 6 0 6 0.1
   python nash_local_gs2.py 6 4 14 0.1
   ```
3. Global run. Run W workers with w = 0..W-1; each writes `fast/bbnb/box_<idx>.json`. The local-cube JSON files must
   be in `code/`.
   ```
   cd fast
   python bb_nb.py w W bbnb
   ```
4. Completeness check:
   ```
   python check_run.py bbnb
   ```
5. Optional cross-check of a random sample with the numpy implementation:
   ```
   python crosscheck_numpy.py w W n
   ```

The production run used 20 workers plus reverse-order helpers (`bb_nb_helper.py`) on a 24-core machine, about 4.5
hours.

Code hashes and line endings:
- `CODE_SHA256_v22.txt` and `certificates/local/CODE_SHA256.txt` record the SHA-256 of the code exactly as it ran,
  with the CRLF line endings of the original Windows working copies.
- This repository stores and checks out text files with LF line endings (`.gitattributes`).
- `CODE_SHA256_v22_LF.txt` and `CODE_SHA256_LF.txt` give the hashes of the same files after CRLF -> LF conversion,
  which is what a checkout of this repository contains. The content is otherwise identical.
