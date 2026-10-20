# Partial CGLMP families (PA2) and the noise clause on glued CGLMP facets

Ansh Mishra, Aryan Senthilkumar. 2026-10-20. Folder `clauses/noise-glued-pa2/`.

**Status:**
- Proved, computer-assisted, up to a small certified excess, for k = 3..10. k = 2 is exact (Tsirelson's vector
  argument).
- Independently re-checked; see [`INDEPENDENT_VERIFICATION.md`](INDEPENDENT_VERIFICATION.md).
- Not reviewed by outside experts.
- PA2 for all k remains OPEN, and so does C2 for general strategies.

## 1. Statements

**Lemma PA2(k).**
- Setting: let {alpha_{x,a}} and {phi_{y,b}} (x, y in {0,1}; a, b in Z_k) be four families, each orthonormal, in any
  Hilbert space. The families need not be complete or span the same subspace.
- Define S = sum_{x,y,a,b} c_k(x,y,a,b) |<alpha_{x,a}|phi_{y,b}>|^2, where c_k is the CGLMP_k coefficient table.
- Claim: S <= k I_ME(k).

**Theorem PA2-eps.** For k = 3, ..., 10, S <= k I_ME(k) + eps_k with the certified excesses:

| k | eps_k | solver |
|---|---|---|
| 3 | 6.47e-7 | Clarabel |
| 4 | 3.29e-6 | Clarabel |
| 5 | 5.06e-6 | Clarabel |
| 6 | 9.09e-6 | Clarabel |
| 7 | 4.9e-3 | SCS |
| 8 | 7.26e-3 | SCS |
| 9 | 7.35e-3 | SCS |
| 10 | 1.63e-2 | SCS |

The relaxation value agrees with k I_ME(k) to within solver accuracy at every k tested (|ratio - 1| <= 2.4e-5). The
certified excess reflects the solver's accuracy, not a gap in the relaxation.

**Corollary G (glued CGLMP facets).**
- Setting: let d = k_1 + ... + k_r with r >= 2 and every k_i in {2, ..., 10}. Take the glued CGLMP functional
  Phi = sum_i CGLMP_{k_i}, each block acting on the cells with both outcomes in block i, and zero on cross-block cells.
  The normalised "glued facet" of the same composition differs from Phi only by normalisation.
- Claim: for every complete von Neumann strategy (rank-one projective measurements) on Phi_d, the white-noise ratio of
  this inequality is at most
  sum_i (k_i/d) kappa_{k_i} + sum_i eps_{k_i}/(2d) < kappa_d.
- So C2 holds on all these facets, in every dimension d.

## 2. Proofs

**The glued functional.**
- Local bound 2. If all four outcomes lie in one block, the CGLMP bound applies. Otherwise the 4-cycle a0-b0-a1-b1 has
  at least two cross links, and the at most two within-block links contribute <= 1 each.
- Phi(u) = 0, since every row of a CGLMP table sums to 0. So the white-noise ratio is Phi(P)/2.
- With P(a,b|x,y) = (1/d)|<a_x|b_y>|^2, the block-i part of Phi(P) equals S_i/d. Here S_i is the PA2 sum of the four
  orthonormal k_i-families {a_x : a in block i}, {b_y : b in block i}.
- PA2-eps then gives the bound of Corollary G. The margin is per block: k(kappa_{k+2} - kappa_k) >= 0.0247 for every
  k <= 10, while eps_k/2 <= 8.2e-3, and d >= k_i + 2 because r >= 2.

**The relaxation behind PA2-eps.**
- Write A_{x,a} = |alpha_{x,a}><alpha_{x,a}| and B_{y,b} = |phi_{y,b}><phi_{y,b}|. These are rank-one projections with
  A_{x,a} A_{x,a'} = delta_{aa'} A_{x,a}, and the same for B.
- The moments are Tr(w) for words w in these projections, using NONEMPTY words only. So neither the identity nor the
  dimension enters.
- Averaging over the global outcome shift (a, b) -> (a + 1, b + 1), and over complex conjugation, keeps S and makes
  the moments real, invariant under the shift, and invariant under reversal.
- The words used are the letters together with the Alice-Bob products A_x B_y and B_y A_x.
- In Fourier sectors s = 0..k-1 of the shift, the moment matrices M_s(y) = C_s + sum_c y_c E_{s,c} are PSD for every
  configuration. Each is a Gram matrix: for the real moments, M_s = (1/2k)[Gram(F_s) + conj Gram(F_{-s})].
- For any Hermitian Z_s with Z_s + mu I >= 0:
      S = D(Z) + r.y - sum_s Re Tr(Z_s M_s(y)) <= D(Z) + sum_c |r_c| + mu k n.
  Here D(Z) = sum_s Re Tr(Z_s C_s) and r_c = b_c + sum_s Re Tr(Z_s E_{s,c}). The bound uses two facts:
  - |y_c| <= 1, since traces of products of rank-one projections are bounded by 1, also after averaging;
  - sum_s Tr M_s <= k n, with n = 4 + 8k words per sector.
- `code/certify_pa2.py` takes the numerical dual, clips negative eigenvalues and rounds to exact dyadic Hermitian
  matrices. It then evaluates D(Z) and every residual r_c in 200-bit interval arithmetic (cyclotomic phases, exact
  CGLMP coefficients), and certifies Z_s + mu I >= 0 by an interval Cholesky of the real embedding.
- The printed bound is rigorous for every Hilbert space dimension. For projections of equal rank r the same argument
  gives S <= r (k I_ME(k) + eps_k).

**Structure, CHECKED NUMERICALLY.** These facts are not used in the proofs.
- The level-1 relaxation (letters only) is not tight: ratio 1.392 at k = 3.
- With all words of length <= 2 the relaxation is tight at k = 3 and 4 (`code/trace_sdp.py`, `code/trace_sdp_sym.py`).
- The Alice-Bob products alone suffice at k = 3, 4 and 5 (`code/dual_sdp.py`).
- Relaxations that decouple the Fourier modes are no better than level 1.
- In every mode, DKZ's four vectors U_0^s, U_1^s, V_0^s, V_1^s span exactly a two-dimensional space.

## 3. Reproduction

Python 3 with numpy, scipy, cvxpy (Clarabel and SCS) and mpmath.

| k | command |
|---|---|
| 3..6 | `python certify_pa2.py k -34 clip` |
| 7..10 | `python certify_pa2.py k -30 clip,scs 60000` |

Clarabel needs about 8 GB of memory at k = 6, and more than 19 GB at k = 8, so k >= 7 uses SCS. The logs are in
`logs/cert_k*.log`, with full outputs in `logs/cert_k*_full.log` for k >= 7.

## 4. What is not claimed
- PA2 for k >= 11, and an all-k proof. A closed form of the certificate was not found.
- Glued facets with a block of size >= 11.
- C2 for general strategies.
