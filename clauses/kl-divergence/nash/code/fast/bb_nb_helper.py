"""Helper worker for the bb_nb.py run: processes the work list from the END (reverse order), skipping regions that
already have a result file or a lock (exclusive create), and writes results exactly as bb_nb.py does.
usage: python bb_nb_helper.py helper_id nhelpers [outdir]"""
import os
os.environ.setdefault("NUMBA_NUM_THREADS", "1")
import sys, json, time
import bb_nb as B
import nash_bb as BB

if __name__ == "__main__":
    hid, nh = int(sys.argv[1]), int(sys.argv[2])
    outdir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(B.HERE, "bbnb")
    here = os.getcwd()
    os.chdir(B.NJ.ROOT)
    locs = BB.load_locals()
    os.chdir(here)
    assert len(locs) == 4
    todo = list(reversed(B.BT.work_list()))[hid::nh]
    log = open(os.path.join(outdir, f"helper_{hid}.log"), "a")
    log.write(f"helper {hid}/{nh}: {len(todo)} candidate regions (reverse order), engine {B.ENGINE}\n")
    log.flush()
    for idx in todo:
        fn = os.path.join(outdir, f"box_{idx}.json")
        lock = fn + ".helperlock"
        if os.path.exists(fn):
            continue
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.close(fd)
        except FileExistsError:
            continue
        st = B.run_initial(idx, locs)
        if not os.path.exists(fn):
            json.dump(st, open(fn + ".htmp", "w"))
            os.replace(fn + ".htmp", fn)
        log.write(f"{time.strftime('%H:%M:%S')} box {idx}: evals {st['evals']} unresolved {len(st['unresolved'])} "
                  f"worst/S0 {st['worst'] / B.S0LO:.4f} time {st['time']:.0f}s\n")
        log.flush()
    log.write("done\n")
