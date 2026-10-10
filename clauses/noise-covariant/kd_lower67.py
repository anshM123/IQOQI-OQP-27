"""numerical lower bounds (DFT + diagonal-phase strategies) for the max-ent ratios of the K_d classes, d = 6, 7."""
import sys, json
import numpy as np
from kd_ratio import maximise, cprime
d = int(sys.argv[1]); starts = int(sys.argv[2])
rng = np.random.default_rng(3)
classes = json.load(open(f"kd_facets_d{d}.json"))
for ci, cl in enumerate(classes):
    if cl["size"] == 4 * d:
        continue
    c = np.array(cl["c"]); Fu = cprime(c, d).sum() / d
    lb = maximise(c, d, "dft", starts, rng)
    print(f"d={d} class {ci} (size {cl['size']}, tight {cl['tight']}): DFT+phase lower bound on the ratio {(lb - Fu)/(-Fu):.8f}", flush=True)
