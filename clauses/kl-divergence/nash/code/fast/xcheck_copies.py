"""Targeted numpy cross-check of initial boxes that contain a DKZ copy (exercises the local-cube handoff)."""
import os, sys, json
import crosscheck_numpy as X
import nash_bb as BB
idx = int(sys.argv[1])
here = os.getcwd(); os.chdir(os.path.join(X.HERE, "..")); locs = BB.load_locals(); os.chdir(here)
st = X.run(idx, locs)
json.dump(st, open(os.path.join(X.HERE, "xcheck", f"xc_{idx}.json"), "w"))
print(json.dumps(st), flush=True)
