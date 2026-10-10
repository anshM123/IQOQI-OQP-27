"""
jm_relax.py -- numerics for the jointly-measurable (one-sided local-hidden-state) relaxation of the KL strength.

Lemma JM.  For Alice PVMs A_x (columns alpha^x_a), Bob steered states phi^y_b (columns of Bt_y) and ANY jointly
measurable POVM pair E = (E^0, E^1) on C^3 (parent POVM M_{a0 a1} >= 0, sum M = 1, E^0_a = sum_{a1} M_{a a1},
E^1_a = sum_{a0} M_{a0 a}), the behaviour p(a,b|x,y) = <phi^y_b|E^x_a|phi^y_b>/3 is LOCAL, hence
   S^UNI(q) <= (1/12) sum_{y,b} J(phi^y_b) <= (1/2) max_phi J(phi),   J(phi) = sum_x D(pi_phi(A_x) || pi_phi(E^x)),
   S^COR(q) <= max_x max_phi D(pi_phi(A_x) || pi_phi(E^x)),
where pi_phi(A_x)(a) = |<alpha^x_a|phi>|^2 and pi_phi(E^x)(a) = <phi|E^x_a|phi>.  (Numerics only in this file.)
"""
import sys
import numpy as np
import cvxpy as cp
from scipy.optimize import minimize
from c3core import *


def parent_vars():
    M = [cp.Variable((3, 3), hermitian=True) for _ in range(9)]
    cons = [m >> 0 for m in M] + [sum(M) == np.eye(3)]
    E = [[sum(M[a * 3 + a1] for a1 in range(3)) for a in range(3)],
         [sum(M[a0 * 3 + a] for a0 in range(3)) for a in range(3)]]
    return M, E, cons


def born(E_xa, phi):
    Pm = np.outer(phi, phi.conj())
    return cp.real(cp.trace(E_xa @ Pm))


def kl_terms(A, E, phi, x):
    """list of (t, s_expr) for D(pi_phi(A_x) || pi_phi(E^x))"""
    out = []
    for a in range(3):
        t = abs(np.vdot(A[x][:, a], phi)) ** 2
        out.append((t, born(E[x][a], phi)))
    return out


def D_expr(A, E, phi, x):
    expr = 0
    const = 0.0
    for t, s in kl_terms(A, E, phi, x):
        if t > 1e-300:
            expr = expr - t * cp.log(s)
            const += t * np.log(t)
    return expr + const


def solve_avg(A, states, solver="CLARABEL"):
    """min over JM pairs of (1/12) sum_{phi in states} J(phi)  (states = the 6 steered states)"""
    M, E, cons = parent_vars()
    obj = sum(D_expr(A, E, phi, x) for phi in states for x in range(2)) / 12.0
    prob = cp.Problem(cp.Minimize(obj), cons)
    prob.solve(solver=solver)
    Mv = [m.value for m in M]
    return prob.value, Mv


def E_from_M(Mv):
    E0 = [sum(Mv[a * 3 + a1] for a1 in range(3)) for a in range(3)]
    E1 = [sum(Mv[a0 * 3 + a] for a0 in range(3)) for a in range(3)]
    return [E0, E1]


def Dx_num(A, Ev, phi, x):
    v = 0.0
    for a in range(3):
        t = abs(np.vdot(A[x][:, a], phi)) ** 2
        s = np.real(np.vdot(phi, Ev[x][a] @ phi))
        if t > 1e-300:
            v += t * np.log(t / max(s, 1e-300))
    return v


def phi_of(th):
    t1, t2, c1, c2 = th
    return np.array([np.cos(t1), np.sin(t1) * np.cos(t2) * np.exp(1j * c1), np.sin(t1) * np.sin(t2) * np.exp(1j * c2)])


def global_max(fun, rng, nstart=400):
    """maximise fun(phi) over unit phi in C^3 (multistart Nelder-Mead / BFGS on 4 angles)."""
    best = (-np.inf, None)
    for s in range(nstart):
        th0 = np.array([np.arccos(np.sqrt(rng.random())), rng.random() * np.pi / 2, rng.random() * 2 * np.pi,
                        rng.random() * 2 * np.pi])
        res = minimize(lambda th: -fun(phi_of(th)), th0, method="BFGS", options={"gtol": 1e-10})
        if -res.fun > best[0]:
            best = (-res.fun, phi_of(res.x))
    return best


def minmax(A, init_states, mode="uni", rng=None, rounds=30, nstart=200, tol=1e-9, verbose=True, solver="CLARABEL"):
    """cutting plane for min over JM pairs of max_phi J (mode 'uni': (1/2)(D_0 + D_1); 'cor': max_x D_x)"""
    states = list(init_states)
    hist = []
    for r in range(rounds):
        M, E, cons = parent_vars()
        tau = cp.Variable()
        cc = list(cons)
        for phi in states:
            if mode == "uni":
                cc.append(0.5 * (D_expr(A, E, phi, 0) + D_expr(A, E, phi, 1)) <= tau)
            else:
                cc.append(D_expr(A, E, phi, 0) <= tau)
                cc.append(D_expr(A, E, phi, 1) <= tau)
        prob = cp.Problem(cp.Minimize(tau), cc)
        prob.solve(solver=solver)
        Mv = [m.value for m in M]
        Ev = E_from_M(Mv)
        if mode == "uni":
            f = lambda phi: 0.5 * (Dx_num(A, Ev, phi, 0) + Dx_num(A, Ev, phi, 1))
        else:
            f = lambda phi: max(Dx_num(A, Ev, phi, 0), Dx_num(A, Ev, phi, 1))
        val, phi_star = global_max(f, rng, nstart)
        hist.append((prob.value, val))
        if verbose:
            print(f"  round {r}: lower (cut LP) {prob.value/LOG2:.9f} bits, upper (max over phi) {val/LOG2:.9f} bits,"
                  f" #states {len(states)}", flush=True)
        if val - prob.value < tol:
            break
        states.append(phi_star)
    return prob.value, val, Mv, states


if __name__ == "__main__":
    rng = np.random.default_rng(7)
    U = dkz()
    A = [U[0], U[1]]
    steered = [U[2 + y][:, b] for y in range(2) for b in range(3)]
    v, Mv = solve_avg(A, steered)
    print("T1: min over JM of (1/12) sum_{y,b} J(phi*_yb) =", v, "nats =", v / LOG2, "bits;  S0 =", S0_BITS)
    Ev = E_from_M(Mv)
    for y in range(2):
        for b in range(3):
            phi = U[2 + y][:, b]
            print("   D_0, D_1 at steered state", y, b, Dx_num(A, Ev, phi, 0) / LOG2, Dx_num(A, Ev, phi, 1) / LOG2)
    f = lambda phi: 0.5 * (Dx_num(A, Ev, phi, 0) + Dx_num(A, Ev, phi, 1))
    val, ph = global_max(f, rng, 300)
    print("   with this E: max_phi (1/2)J =", val / LOG2, "bits")
    print("T2 (uni): cutting plane")
    lo, up, Mv2, st = minmax(A, steered, "uni", rng, rounds=25, nstart=150)
    print("T2 (cor): cutting plane")
    lo, up, Mv3, st = minmax(A, steered, "cor", rng, rounds=25, nstart=150)
