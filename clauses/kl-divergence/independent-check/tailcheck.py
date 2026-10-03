# float cross-check of the tail of T(mu*) between |m| = 3001 and N (referee)
import json, numpy as np
from fractions import Fraction as Fr
Z = json.load(open(r"..\P4_kl\zmodel_cert_A10.json"))
t = float(Fr(Z["t"]))
dl = {"00": 0.25, "01": 0.75, "10": -0.25, "11": 0.25}
for N in (10**5, 10**6, 2*10**6):
    tot = 0.0
    for L, d in dl.items():
        m = np.concatenate([np.arange(3001, N + 1), -np.arange(3001, N + 1)]).astype(float)
        mp_ = {"00": m, "01": m, "10": -m, "11": 1 - m}[L]
        P = t / (2 * (mp_ ** 2 - 0.25))
        Q = 1 / (2 * np.pi ** 2 * (m - d) ** 2)
        tot += 0.25 * np.sum(Q * np.log(Q / P))
    print(N, "tail sum (nats, averaged over links):", tot, " bits:", tot / np.log(2))
print("T_dropped(bits) + tail(2e6) =", 0.068780260568 + tot / np.log(2))
