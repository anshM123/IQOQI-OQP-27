# Ledger A3a: noise resistance of the CGLMP violation (every d)

## Statement
Let d >= 2, D >= 1, and let S be any strategy with two d-outcome projective measurements per party on the maximally
entangled state Phi_D, with behaviour p_S(a,b|x,y) = Tr((A^x_a)^T B^y_b)/D. Let u(a,b|x,y) = 1/d^2 be the behaviour
of completely random, uniform outcomes, and for 0 <= v <= 1 let p_v = v p_S + (1 - v) u.

1. I_d(p_v) = v I_d(p_S) for every v.
2. Hence the CGLMP inequality I_d <= 2 is violated by p_v if and only if v I_d(p_S) > 2. The CGLMP noise threshold
   v_CGLMP(S) := inf{v in [0,1] : I_d(p_v) > 2} (infimum of the empty set := +infinity) satisfies
   v_CGLMP(S) = 2 / I_d(p_S) >= 2 / I_ME(d) whenever I_d(p_S) > 2, and v_CGLMP(S) = +infinity otherwise.
3. v_CGLMP(DKZ) = 2 / I_ME(d), and v_CGLMP(S) = 2/I_ME(d) holds if and only if d | D and S is unitarily equivalent to
   DKZ (x) 1_{D/d} by a local unitary u (x) conj(u).

The same holds for white noise on the state, rho_v = v Phi_D + (1-v) 1/D^2, for every strategy whose projections all have
rank D/d (then the noise behaviour tr(A^x_a) tr(B^y_b)/D^2 equals u); for rank-one measurements on Phi_d (D = d) the two
noise models coincide.

## Proof
(1) I_d is a linear functional of the behaviour, so I_d(p_v) = v I_d(p_S) + (1-v) I_d(u). Under u every probability
P(A_x - B_y = k mod d) and P(B_y - A_x = k mod d) equals sum over the d pairs (a, b) with a - b = k of 1/d^2, i.e. 1/d.
In I_d (formula of the mathematical paper / lean/OQP27/Statement.lean `Strategy.cglmp`) every k-th bracket is (four such probabilities) minus
(four such probabilities) = 4/d - 4/d = 0; hence I_d(u) = 0.
(2) Immediate from (1): I_d(p_v) > 2 iff v I_d(p_S) > 2; if I_d(p_S) > 2 the set of violating v is (2/I_d(p_S), 1],
and by the max-ent theorem (Theorem 1 / Lean `OQP27.maxEntClause_all`, `maxEntClause_le_twenty`)
I_d(p_S) <= I_ME(d), so 2 / I_d(p_S) >= 2 / I_ME(d).
(3) DKZ has I_d = I_ME(d) (Lean `OQP27.dkz_cglmp`), so its threshold is 2/I_ME(d). Conversely v_CGLMP(S) = 2/I_ME(d)
forces I_d(p_S) = I_ME(d), and the rigidity theorem (Theorem 2 / Lean `RigidityStatement`) gives d | D and
S ~ DKZ (x) 1 up to u (x) conj(u); the converse direction is the invariance of the behaviour under u (x) conj(u) and
under tensoring with an inert identity factor.
White noise: Tr((A^x_a)^T B^y_b ... ) of the maximally mixed state gives tr(A^x_a) tr(B^y_b)/D^2 = (D/d)^2/D^2 = 1/d^2
when every projection has rank D/d. QED.

## Remarks
- This is the reading "resistance to noise of the CGLMP violation". It does not say anything about other Bell
  inequalities; for those see ledger A3b (Gill's literal reading) and C2 (white noise, all Bell inequalities).
- For strategies with unequal ranks under WHITE state noise the noise behaviour is p_A (x) p_B, not u, and I_d of it
  can be positive; that case is ledger B1 (handled separately).
- Formal status: items 1-3 follow in a few lines from the Lean-verified max-ent theorem; a Lean formalisation of the
  behaviour-level statement is in `lean/OQP27/CglmpNoise.lean`.
