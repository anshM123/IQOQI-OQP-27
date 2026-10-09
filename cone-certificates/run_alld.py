"""run_alld.py: re-run the complete d >= 2001 pipeline (CONE_ALLD_PROOF.md, RIGOR_ALLD.md) from QD2/ and audit it.
Usage: python run_alld.py [NPAR]   (default 12 parallel jobs; each job < 0.5 GB).  Every job writes logs/alld/<name>.log;
the certificate scripts write their exact (rational-string) results to logs/alld/*.json; finally audit_alld.py ->
logs/alld/audit_alld.log (copied to logs/audit_alld_final.log)."""
import subprocess, sys, time, shutil, os
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

PY = sys.executable
L = 'logs/alld/'
NPAR = int(sys.argv[1]) if len(sys.argv) > 1 else 12

# (name, args); longest first.  Zone plans as in CONE_ALLD_PROOF.md s.5-7, s.9 (the four longest sweeps split in two).
STAGE1 = [
    ('zoneO_0b1', ['a06_zoneO.py', '0.015', '0.0225', '15', L + 'zoneO_0b1.json']),
    ('zoneO_0b2', ['a06_zoneO.py', '0.0225', '0.03', '15', L + 'zoneO_0b2.json']),
    ('zoneO_0a1', ['a06_zoneO.py', '0.011', '0.013', '8', L + 'zoneO_0a1.json']),
    ('zoneO_0a2', ['a06_zoneO.py', '0.013', '0.015', '8', L + 'zoneO_0a2.json']),
    ('slackW_O1a', ['a11_slack.py', 'outer', 'x', '0.03', '0.27', '24', L + 'slackW_O1a.json']),
    ('slackW_O1b', ['a11_slack.py', 'outer', 'x', '0.27', '0.501', '23', L + 'slackW_O1b.json']),
    ('slackW_O0a', ['a11_slack.py', 'outer', 'x', '0.011', '0.0205', '5', L + 'slackW_O0a.json']),
    ('slackW_O0b', ['a11_slack.py', 'outer', 'x', '0.0205', '0.03', '5', L + 'slackW_O0b.json']),
    ('zoneO_2', ['a06_zoneO.py', '0.10', '0.30', '40', L + 'zoneO_2.json']),
    ('zoneO_3c', ['a06_zoneO.py', '0.42', '0.501', '16', L + 'zoneO_3c.json']),
    ('zoneI_b3', ['a07_zoneI.py', 'b', '5', '20', '60', L + 'zoneI_b3.json']),
    ('a14_identities', ['a14_identities.py']),
    ('zoneO_3a', ['a06_zoneO.py', '0.30', '0.40', '20', L + 'zoneO_3a.json']),
    ('a10_pointwise', ['a10_pointwise.py']),
    ('a12_fp_alld', ['a12_fp_alld.py']),
    ('slackW_I2b', ['a11_slack.py', 'inner', 'b', '5', '20', '30', L + 'slackW_I2b.json']),
    ('slackW_I2a', ['a11_slack.py', 'inner', 'b', '2', '5', '30', L + 'slackW_I2a.json']),
    ('zoneI_b2', ['a07_zoneI.py', 'b', '2', '5', '30', L + 'zoneI_b2.json']),
    ('zoneO_1', ['a06_zoneO.py', '0.03', '0.10', '28', L + 'zoneO_1.json']),
    ('slackW_I1', ['a11_slack.py', 'inner', 'b', '1', '2', '20', L + 'slackW_I1.json']),
    ('zoneI_b1', ['a07_zoneI.py', 'b', '1', '2', '20', L + 'zoneI_b1.json']),
    ('zoneO_3b', ['a06_zoneO.py', '0.40', '0.42', '8', L + 'zoneO_3b.json']),
    ('zoneI_w1', ['a07_zoneI.py', 'w', '0.01', '0.05', '20', L + 'zoneI_w1.json']),
    ('zoneI_w2', ['a07_zoneI.py', 'w', '0.001', '0.01', '18', L + 'zoneI_w2.json']),
    ('slackW_I3', ['a11_slack.py', 'inner', 'w', '0', '0.05', '10', L + 'slackW_I3.json']),
    ('t35_polya', ['t35_polya.py', '3000']),
    ('a08_A2', ['a08_A2.py', '400']),
    ('a13_constants', ['a13_constants.py']),
    ('test_exact', ['test_exact.py']),
    ('slack_m1', ['a11_slack.py', 'm1']),
    ('zoneI_w3', ['a07_zoneI.py', 'w', '0', '0.001', '1', L + 'zoneI_w3.json']),
    ('a01_model_d1000', ['a01_model.py', '1000']),      # non-rigorous prototype cross-check (reads logs/phi_d1000.json)
    ('a01_model_d2000', ['a01_model.py', '2000']),
]
# The a01 jobs are an optional numerical cross-check, not part of the proof. Their input files logs/phi_d1000.json and
# logs/phi_d2000.json (certified solutions at d = 1000, 2000) are not shipped with this repository, so skip them if absent.
for _d in ('1000', '2000'):
    if not os.path.exists(f'logs/phi_d{_d}.json'):
        print(f'note: logs/phi_d{_d}.json not present; skipping the optional cross-check a01_model_d{_d}', flush=True)
        STAGE1 = [j for j in STAGE1 if j[0] != f'a01_model_d{_d}']
STAGE2 = [('a09_smallm', ['a09_smallm.py'])]          # needs logs/alld/polya.json (t35)


def run(job):
    name, args = job
    t0 = time.time()
    with open(L + name + '.log', 'w') as fo:
        rc = subprocess.call([PY] + args, stdout=fo, stderr=subprocess.STDOUT)
    dt = time.time() - t0
    with open(L + name + '.log') as fi:
        last = (fi.read().strip().splitlines() or [''])[-1]
    print(f"[{time.strftime('%H:%M:%S')}] {name}: rc={rc}  {dt:.0f}s  | {last[:150]}", flush=True)
    return name, rc, dt


if __name__ == '__main__':
    os.makedirs(L, exist_ok=True)
    T0 = time.time()
    print(f"run_alld: {len(STAGE1) + len(STAGE2)} jobs, {NPAR} parallel, python {sys.version.split()[0]}", flush=True)
    res = []
    with ThreadPoolExecutor(NPAR) as ex:
        pending = {ex.submit(run, j) for j in STAGE1}
        while pending:
            done, pending = wait(pending, return_when=FIRST_COMPLETED)
            for f in done:
                r = f.result(); res.append(r)
                if r[0] == 't35_polya':                       # stage 2 as soon as t35 is done
                    pending |= {ex.submit(run, j) for j in STAGE2}
    bad = [r for r in res if r[1] != 0]
    print(f"all jobs finished in {time.time() - T0:.0f}s; nonzero exit codes: {bad}", flush=True)
    with open(L + 'audit_alld.log', 'w') as fo:
        subprocess.call([PY, 'audit_alld.py'], stdout=fo, stderr=subprocess.STDOUT)
    shutil.copyfile(L + 'audit_alld.log', 'logs/audit_alld_final.log')
    print(open(L + 'audit_alld.log').read())
