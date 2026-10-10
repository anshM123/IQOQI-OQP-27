# Noise against all Bell inequalities, complete von Neumann measurements: d = 4

Ansh Mishra, Aryan Senthilkumar. Computer-assisted, exact arithmetic. Not yet reviewed by outside experts.

**Statement.** Mix the maximally entangled state Φ_4 with white noise, ρ_v = v |Φ_4⟩⟨Φ_4| + (1 − v) 1/16. For every
choice of complete von Neumann measurements, the behaviour stays nonlocal (violates some Bell inequality) only for
v > 2/I_ME(4) = 0.6905497…, and the DKZ measurements are the only ones that reach this bound. So the DKZ
measurements have the highest resistance to noise against all Bell inequalities. The bound also holds for projective
measurements of any ranks on Φ_4, and for balanced projective measurements on maximally entangled states of any
dimension. With the earlier cases d = 2 and d = 3 (`../noise-literal/`), this part of the noise clause now holds for
d ≤ 4. It is open for d ≥ 5.

**How it is proved** ([`THEOREM.md`](THEOREM.md)).
- **Theorem V** (a visibility criterion) shows that a list of facet classes of the local polytope is complete if every
  class except positivity is closed under ridge adjacency and every non-local vertex of the no-signalling polytope
  violates a listed facet. The positivity class, with more than 7.5 million ridges per facet, never has to be expanded.
- **Theorem F4.** The local polytope of the (2,2,4) scenario has exactly 11 665 992 facets in 34 classes. This is the list
  of Jesus and Zambrini Cruzeiro (2023), proved complete here.
- **Theorem D4.** Every class other than CGLMP_4 has a certified maximal-entanglement ratio below κ_4 = I_ME(4)/2. The
  largest is √2, for a lifted CHSH class. The CGLMP_4 class gives exactly κ_4, with equality only for DKZ, by the main
  theorems of this repository.

**Checks.** A second implementation that imports none of the first one's code ([`INDEPENDENT_CHECK.md`](INDEPENDENT_CHECK.md),
the `IND_*.py` scripts) re-derives Theorem V and recomputes every computational input: the 34 facets and their orbits,
the closure of all 33 non-positivity classes (215 725 ridges), the 204 160 vertices of the no-signalling polytope, and
the per-class certificates with a different exact positivity test. Verdict: confirmed.

**Reproduce.**

    python CLOSE_verify.py 4 --skip-polar      # Theorem V hypotheses, d = 4 (about 1 min)
    python CLOSE_verify.py 4 --skip-adm        # the same with the polar enumeration of the no-signalling vertices
    python check_d4_summary.py                 # the saved per-class certificates
    python IND_summary.py                      # the independent check, from its logs
    python IND_expand.py expand 0 --threads 4 --mode nbhd --order index    # e.g. re-expand class 0 (about 1 h)

Section 5 of `THEOREM.md` and Section 7 of `INDEPENDENT_CHECK.md` list every command, with run times. Inputs:
`adj_d4_small_final.pkl` and `adj_d4_full.pkl` (class representatives, orbits, saved expansions), `d4_ratios.pkl`.
Requirements: Python 3 with numpy, scipy, numba, python-flint and cvxpy with SCS. One solver warning with local paths in
`logs/IND_sdp_all.log` was shortened; nothing else in the logs was changed.
