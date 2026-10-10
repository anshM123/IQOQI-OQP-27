"""
IND_summary.py -- collects the independent d = 4 check (2026-10-09) from its own logs and prints the verdict data:
  * hypothesis (i): every non-positivity class expanded by IND_expand.py, every neighbour identified with a listed
    class by an explicit relabelling, NEW = 0, agreement with the saved expansion, repeated runs agree;
  * double counting orbit_i a_ij = orbit_j a_ji with the orbits recomputed by IND_expand.py classes;
  * hypothesis (ii): logs/IND_ns.json;
  * ratio certificates: logs/IND_sdp_results.jsonl (all classes except 17 = CGLMP_4 below kappa_4).
"""
import json
import pickle
from fractions import Fraction

if __name__ == "__main__":
    orbits = json.load(open("logs/IND_classes.json"))["orbits"]
    jpos = json.load(open("logs/IND_classes.json"))["positivity"]
    assert jpos == [25]
    runs = {}
    for line in open("logs/IND_expand_results.jsonl"):
        r = json.loads(line)
        runs.setdefault(r["cls"], []).append(r)
    adj = {}
    ok = True
    print("class | tight | ridges | NEW | equal to saved | runs agree | DD peak | DD s | order/mode")
    for j in range(34):
        if j == 25:
            continue
        if j not in runs:
            print(f"{j:5d} | NOT EXPANDED")
            ok = False
            continue
        rs = runs[j]
        agree = all(r["counts"] == rs[0]["counts"] and r["ridges"] == rs[0]["ridges"] for r in rs)
        r = rs[-1]
        adj[j] = {int(k): v for k, v in r["counts"].items()}
        inside = all(0 <= k < 34 for k in adj[j])
        ok &= agree and r["new"] == 0 and inside and r["equal_to_saved"]
        print(f"{j:5d} | {r['tight']:5d} | {r['ridges']:6d} | {r['new']:3d} | {r['equal_to_saved']} | {agree} ({len(rs)}) | "
              f"{r['dd']['peak']:7d} | {r['t_dd']:7.1f} | {r.get('order', 'zeros')}/{r.get('mode', 'lists')}")
    bad = 0
    for i in adj:
        for k, a in adj[i].items():
            if k in adj and orbits[i] * a != orbits[k] * adj[k].get(i, 0):
                bad += 1
    print(f"expanded non-positivity classes: {len(adj)} of 33; double-counting violations (own orbits): {bad}")
    ok &= (len(adj) == 33) and bad == 0
    if len(adj) == 33:
        num = sum(orbits[j] * adj[j].get(25, 0) for j in adj)
        print(f"Corollary P4 recount: sum_j orbit_j a_(j,25) / 64 = {num} / 64 = {Fraction(num, 64)} (integral: "
              f"{num % 64 == 0}); with the 63 positivity neighbours: {Fraction(num, 64) + 63}")
    ns = json.load(open("logs/IND_ns.json"))
    okns = ns["B"]["ok"] and ns["Bp_ok"] and all(Fraction(v["min_slack"]) < 0 for v in ns["C"].values())
    print(f"hypothesis (ii): vertices {ns['B']['vertices']} {ns['B']['by_orbit']}; edge closure {ns['Bp_ok']}; "
          f"PR_k violations {ns['C']}: {okns}")
    sd = {}
    for line in open("logs/IND_sdp_results.jsonl"):
        r = json.loads(line)
        sd[r["cls"]] = r
    oksdp = all(sd[j]["psd_certified"] and (sd[j]["below_kappa4"] or j == 17) for j in sd) and len(sd) == 34
    mx = max((sd[j]["ratio_ub"], j) for j in sd if j != 17)
    print(f"ratio certificates: {len(sd)} classes, all PSD-certified and below kappa_4 except class 17: {oksdp}; "
          f"largest non-CGLMP bound {mx[0]:.7f} (class {mx[1]})")
    print("ALL INDEPENDENT CHECKS PASSED" if (ok and okns and oksdp) else "SOME CHECK MISSING OR FAILED")
    # markdown tables for INDEPENDENT_CHECK_D4.md
    S = pickle.load(open("adj_d4_small_final.pkl", "rb"))
    with open("logs/IND_summary.md", "w") as fh:
        fh.write("| class | tight | ridges (own DD) | neighbours outside the list | equal to saved expansion | runs | DD peak rays | "
                 "DD time [s] | insertion order / adjacency variant |\n|---|---|---|---|---|---|---|---|---|\n")
        for j in range(34):
            if j == 25 or j not in runs:
                continue
            rs = runs[j]
            r = rs[-1]
            fh.write(f"| {j} | {r['tight']} | {r['ridges']} | {r['new']} | {r['equal_to_saved']} | {len(rs)} | "
                     f"{r['dd']['peak']} | {r['t_dd']:.0f} | {r.get('order', 'zeros')} / {r.get('mode', 'lists')} |\n")
        fh.write("\n| class | orbit (own) | slack(u) | certified max-ent ratio UB | below kappa_4 | residual sum |\n"
                 "|---|---|---|---|---|---|\n")
        for j in sorted(sd):
            r = sd[j]
            fh.write(f"| {j} | {orbits[j]} | {r['slack_u']} | {r['ratio_ub']:.7f} | "
                     f"{'yes' if r['below_kappa4'] else ('= kappa_4 class (CGLMP_4)' if j == 17 else 'NO')} | "
                     f"{r['resid']:.1e} |\n")
    print("markdown tables written to logs/IND_summary.md")
