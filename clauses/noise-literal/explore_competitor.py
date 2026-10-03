"""explore_competitor.py -- float exploration (not a proof): competitor critical visibility via the 3-outcome
reduction {0,1,R} and the complete facet list of L(2,2,3) (facets223.txt).  Prints the minimising facet class."""
import sys
import numpy as np

sys.path.insert(0, ".")
from facets223 import IDX, NCG


def load_facets(fn="facets223.txt"):
    H, cls = [], []
    for line in open(fn):
        if line.startswith("#"):
            continue
        a, c = line.split(";")
        H.append([int(t) for t in a.split()])
        cls.append(c.strip())
    return np.array(H, float), cls


def cg(p):
    v = np.zeros(NCG)
    for x in range(2):
        for a in range(2):
            v[IDX[("A", x, a)]] = p[x, 0, a, :].sum()
    for y in range(2):
        for b in range(2):
            v[IDX[("B", y, b)]] = p[0, y, :, b].sum()
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    v[IDX[("AB", x, y, a, b)]] = p[x, y, a, b]
    return v


def chsh_q():
    s = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): -1}
    q = np.zeros((2, 2, 3, 3))
    for x in range(2):
        for y in range(2):
            for a in range(2):
                for b in range(2):
                    q[x, y, a, b] = (1 + (-1) ** (a + b) * s[(x, y)] / np.sqrt(2)) / 4
    return q


def det(c):
    q = np.zeros((2, 2, 3, 3))
    for x in range(2):
        for y in range(2):
            q[x, y, c[x], c[2 + y]] = 1
    return q


def noise(d):
    m = np.array([1 / d, 1 / d, (d - 2) / d])
    n = np.zeros((2, 2, 3, 3))
    for x in range(2):
        for y in range(2):
            n[x, y] = np.outer(m, m)
    return n


def vc(q, n, H, cls):
    X = np.hstack([np.ones(1), cg(q)])
    N = np.hstack([np.ones(1), cg(n)])
    fq = H @ X
    fn = H @ N
    best, arg = np.inf, None
    for i in range(len(H)):
        if fq[i] < -1e-12:
            t = fn[i] / (fn[i] - fq[i])
            if t < best - 1e-13:
                best, arg = t, i
    ties = [cls[i] for i in range(len(H)) if fq[i] < -1e-12 and abs(fn[i] / (fn[i] - fq[i]) - best) < 1e-11]
    return best, cls[arg], sorted(set(ties)), len(ties)


if __name__ == "__main__":
    H, cls = load_facets()
    r2 = np.sqrt(2)
    for d in range(3, 41):
        n = noise(d)
        if d % 2 == 0:
            q = chsh_q()
            formula = 4 * (d - 1) / ((r2 - 1) * d * d + 4 * (d - 1))
            res = [vc(q, n, H, cls)]
        else:
            formula = 4 / ((r2 - 1) * d + 4)
            res = [vc((d - 1) / d * chsh_q() + det((c, c, c, c)) / d, n, H, cls) for c in (0, 1)]
        # also the Phi_2 embedding (CHSH on {0,1}) for odd d
        q2 = vc(chsh_q(), n, H, cls)
        print(f"d={d:2d} formula {formula:.12f}  " + "  ".join(f"[vc {r[0]:.12f} {r[1]} ties {r[2]} x{r[3]}]" for r in res)
              + f"   | CHSH-on-Phi_2 {q2[0]:.12f} {q2[1]}")
