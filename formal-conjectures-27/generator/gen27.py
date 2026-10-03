"""Assemble FormalConjectures/OpenQuantumProblems/27.lean from the OQP27 + CGLMPRigidity Lean projects.

usage: python gen27.py [--fast] [--src DIR] [--out PATH]
  --src  : folder containing OQP27/ and CGLMPRigidity/ (default: the repository's lean/ folder)
  --out  : output file (default: 27.out.lean next to this script; compare it with ../27.lean)
  --fast : replace every `decide +kernel` certificate evaluation by `sorry` (test build only, never shipped)
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "lean"))
if "--src" in sys.argv:
    ROOT = sys.argv[sys.argv.index("--src") + 1]
OQP = os.path.join(ROOT, "OQP27")
CGL = os.path.join(ROOT, "CGLMPRigidity")
FAST = "--fast" in sys.argv
OUT = os.path.join(HERE, "27.out.lean")
if "--out" in sys.argv:
    OUT = sys.argv[sys.argv.index("--out") + 1]

ATTR = "category API, AMS 15 81"

# ----------------------------------------------------------------------------------------- file list
order = [l.strip() for l in io.open(os.path.join(OQP, "BUILD_ORDER.txt"), encoding="utf-8") if l.strip()]


def path_of(mod):
    a, b = mod.split(".")
    return os.path.join(OQP if a == "OQP27" else CGL, b + ".lean")


# Source patches needed in the FormalConjectures environment (all of Mathlib is imported there):
# (module, regex, replacement, expected number of replacements)
PATCHES = [
    # `CStarMatrix` has a `default_instance` for `HMul` that is chosen when the implicit index type
    # of `Ecol` is still a metavariable; give it explicitly so that `Matrix` multiplication is used.
    ("OQP27.ReductionTwirl", r"Ecol (t\b|\(t \+ r\))", r"Ecol (ι := ι) \1", 5),
    # `open Polynomial` makes `smul_pow` ambiguous with `Polynomial.smul_pow`.
    ("OQP27.StripSpectral", r"(?<![\w.])smul_pow\b", "_root_.smul_pow", 1),
]


def read(mod, patched=True):
    s = io.open(path_of(mod), encoding="utf-8").read().replace("\r\n", "\n")
    if patched:
        for m, a, b, k in PATCHES:
            if m == mod:
                s, n = re.subn(a, b, s)
                assert n == k, (mod, a, n)
    return s


def deps(mod):
    out = []
    for line in read(mod).split("\n"):
        m = re.match(r"^(?:public\s+)?import\s+(\S+)", line)
        if m and m.group(1).split(".")[0] in ("OQP27", "CGLMPRigidity"):
            out.append(m.group(1))
    return out


need, stack = set(), ["OQP27.Main", "OQP27.CglmpNoise"]
while stack:
    m = stack.pop()
    if m in need:
        continue
    need.add(m)
    stack.extend(deps(m))
mods = [m for m in ("CGLMPRigidity.Rigidity", "CGLMPRigidity.Links", "CGLMPRigidity.Model") if m in need]
mods += ["OQP27." + f for f in order if "OQP27." + f in need]
assert set(mods) == need, sorted(need - set(mods))
seen = set()
for m in mods:  # topological check
    for d in deps(m):
        assert d in seen, (m, d)
    seen.add(m)
dropped = sorted("OQP27." + f for f in order if "OQP27." + f not in need)


# ----------------------------------------------------------------------------------------- lexer
def segments(s):
    """Split Lean source into ('code'|'comment'|'string', text) segments."""
    out, i, n, buf = [], 0, len(s), []

    def flush():
        if buf:
            out.append(("code", "".join(buf)))
            buf.clear()
    while i < n:
        if s.startswith("--", i):
            flush()
            j = s.find("\n", i)
            j = n if j < 0 else j
            out.append(("comment", s[i:j]))
            i = j
        elif s.startswith("/-", i):
            flush()
            depth, j = 1, i + 2
            while depth and j < n:
                if s.startswith("/-", j):
                    depth += 1
                    j += 2
                elif s.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append(("comment", s[i:j]))
            i = j
        elif s[i] == '"':
            flush()
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(("string", s[i:j + 1]))
            i = j + 1
        else:
            buf.append(s[i])
            i += 1
    flush()
    return out


# ----------------------------------------------------------------------------------------- comment clean-up
PATH_RULES = [
    (r"All paths (?:are )?relative to\s*`iqoqi/programs/oqp27B_all/`(?:; see `OQP27/STATUS_L4\.md`)?\.?\s*", ""),
    (r"\(paths relative to `iqoqi/programs/oqp27B_all/`\)", ""),
    (r"iqoqi/programs/oqp27B_all/", ""),
    (r"publish/CGLMP/", "CGLMP/"),
    (r"(?<![/\w-])paper-classical-all-d/main\.tex", "CGLMP/paper-classical-all-d/main.tex"),
    (r"(?<![/\w-])main\.tex", "CGLMP/paper-classical-all-d/main.tex"),
    (r"(?<![/\w-])RIGIDITY\.md", "CGLMP/rigidity/RIGIDITY.md"),
    (r"C_rigidity/RIGIDITY\.md", "CGLMP/rigidity/RIGIDITY.md"),
    (r"(?:Q_rig/)?RIGIDITY_ALLD\.md", "proofs/rigidity/RIGIDITY.md"),
    (r"Q_RI/PROOF\.md", "proofs/radon-identity/PROOF.md"),
    (r"Q_2bmv/PROOF\.md", "proofs/strip-inequality/PROOF.md"),
    (r"QD2/LOG\.md", "cone-certificates/RESEARCH_LOG.md"),
    (r"QD2/verify_fixedpoint\.py", "cone-certificates/"),
    (r"QD2/", "cone-certificates/"),
    (r"Q_quantum/LOG\.md", "papers/math"),
    (r"(?:`)?SHARED_LEMMAS\.md(?:`)?", "`papers/math`"),
    (r"(?<![/\w-])verify_cone\.py", "cone-certificates/verify_cone.py"),
    (r"OQP27/(certdata|logs)/", r"lean/OQP27/\1/"),
    (r"OQP27/(STATUS_L\d+[ab]?|LEAN_BRIEF)\.md", r"lean/OQP27/\1.md"),
    (r"`OQP27/([A-Za-z0-9*]+)\.lean`", r"part `\1` of this file"),
    (r"OQP27/([A-Za-z0-9*]+)\.lean", r"part `\1` of this file"),
    (r"\s*Authors: Ansh Mishra, Aryan Senthilkumar\.\s*License: MIT\.\s*\n", "\n"),
    (r"\s*Authors: Ansh Mishra, Aryan Senthilkumar\.\s*\n", "\n"),
]


def clean_comment(t):
    for a, b in PATH_RULES:
        t = re.sub(a, b, t)
    if t.startswith("/-!"):
        t = "/-" + t[3:]
    return t


def rename(t):
    t = re.sub(r"(?<![\w.])CGLMPRigidity\b", "OpenQuantumProblem27.CGLMPRigidity", t)
    t = re.sub(r"(?<![\w.])OQP27\b", "OpenQuantumProblem27", t)
    return t


# ----------------------------------------------------------------------------------------- per-file transform
DECL = re.compile(r"^(@\[(?P<attrs>[^\]]*)\]\s*)?(?P<mods>(?:(?:private|protected|noncomputable|nonrec)\s+)*)"
                  r"(?P<kw>theorem|lemma|example)\b")
SCOPE_NS = re.compile(r"^namespace\s+(\S+)\s*$")
SCOPE_SEC = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
SCOPE_END = re.compile(r"^end(?:\s+(\S+))?\s*$")
HASHCMD = re.compile(r"^#(print|check|eval|exit|reduce|lint|guard_msgs|synth)\b")
counts = {"decl": 0, "merged": 0, "sorried": 0}


def transform(mod):
    src = read(mod)
    segs = segments(src)
    # blank-out view of code (comments/strings replaced by spaces, newlines kept) for line analysis
    pieces = []
    for kind, text in segs:
        if kind == "code":
            pieces.append(text)
        else:
            pieces.append("".join("\n" if c == "\n" else " " for c in text))
    codeview = "".join(pieces)
    assert len(codeview) == len(src)
    # rewrite comments and code
    out = []
    for kind, text in segs:
        if kind == "comment":
            out.append(rename(clean_comment(text)))
        elif kind == "string":
            out.append(text)
        else:
            out.append(rename(text))
    new = "".join(out)
    # line-level pass: we need the code view of the *new* text; recompute
    segs2 = segments(new)
    cv = "".join(t if k == "code" else "".join("\n" if c == "\n" else " " for c in t) for k, t in segs2)
    lines, clines = new.split("\n"), cv.split("\n")
    assert len(lines) == len(clines)
    res, stackscope = [], []
    for line, cl in zip(lines, clines):
        if re.match(r"^(public\s+)?import\s", cl):
            continue
        if HASHCMD.match(cl):
            continue
        m = SCOPE_NS.match(cl)
        if m:
            stackscope.append(m.group(1))
        m2 = SCOPE_SEC.match(cl)
        if m2:
            stackscope.append(m2.group(1) or "")
        m3 = SCOPE_END.match(cl)
        if m3:
            name = m3.group(1) or ""
            assert stackscope and stackscope[-1] == name, (mod, line, stackscope)
            stackscope.pop()
        d = DECL.match(cl)
        if d:
            counts["decl"] += 1
            kw = d.group("kw")
            cat = "category test, AMS 15 81" if kw == "example" else ATTR
            if d.group(1):
                attrs = d.group("attrs").strip()
                assert "category" not in attrs and "AMS" not in attrs, line
                i0, i1 = line.index("@["), line.index("]")
                line = line[:i0] + "@[" + attrs + ", " + cat + "]" + line[i1 + 1:]
                counts["merged"] += 1
            else:
                line = "@[" + cat + "]\n" + line
        res.append(line)
    body = "\n".join(res)
    for name in reversed(stackscope):
        body = body.rstrip("\n") + "\n\nend" + (" " + name if name else "") + "\n"
    if FAST:
        n0 = body.count("decide +kernel")
        body = body.replace("by decide +kernel", "by sorry")
        counts["sorried"] += n0
    return body.strip("\n")


# ----------------------------------------------------------------------------------------- assemble
parts = []
for k, m in enumerate(mods, 1):
    short = m.split(".")[1]
    sec = ("CGLMP" + short) if m.startswith("CGLMPRigidity") else short
    body = transform(m)
    # move the part's leading doc comment (if any) before the section header
    doc = ""
    mm = re.match(r"^(/-(?!-).*?-/)\s*", body, re.S)
    if mm:
        doc, body = mm.group(1), body[mm.end():]
        doc = "/- ## Part " + str(k) + ": `" + sec + "`\n\n" + doc[2:].lstrip("\n")
    else:
        doc = "/- ## Part " + str(k) + ": `" + sec + "` -/"
    parts.append(doc + "\n\nsection " + sec + "\n\n" + body + "\n\nend " + sec + "\n")

head = io.open(os.path.join(HERE, "fc27_head.lean"), encoding="utf-8").read().replace("\r\n", "\n")
tail = io.open(os.path.join(HERE, "fc27_tail.lean"), encoding="utf-8").read().replace("\r\n", "\n")
problem = io.open(os.path.join(HERE, "fc27_problem.lean"), encoding="utf-8").read().replace("\r\n", "\n")
checks = io.open(os.path.join(HERE, "fc27_checks.lean"), encoding="utf-8").read().replace("\r\n", "\n")
adgl = io.open(os.path.join(HERE, "fc27_adgl.lean"), encoding="utf-8").read().replace("\r\n", "\n")
head = (head.rstrip("\n") + "\n\n" + problem.strip("\n") + "\n\n" + checks.strip("\n") + "\n\n" +
        adgl.strip("\n") + "\n")
text = head.rstrip("\n") + "\n\n" + "\n\n".join(parts) + "\n" + tail.lstrip("\n")
if FAST:
    text = text.replace("by decide +kernel", "by sorry")
else:
    # Elaborate each kernel certificate check synchronously: with parallel elaboration several of them
    # would otherwise run at the same time, and each needs several GB.
    segs = segments(text)
    cv = "".join(t if k == "code" else "".join("\n" if c == "\n" else " " for c in t) for k, t in segs)
    L, CL = text.split("\n"), cv.split("\n")
    starts = set()
    for i, c in enumerate(CL):
        if "decide +kernel" in c:
            j = i
            while not re.match(r"^(@\[|theorem\b|lemma\b)", L[j]):
                j -= 1
            while j > 0 and re.match(r"^@\[", L[j - 1]):
                j -= 1
            if L[j - 1].rstrip().endswith("-/"):
                j -= 1
                while not L[j].startswith("/--"):
                    j -= 1
            starts.add(j)
    for j in sorted(starts, reverse=True):
        L.insert(j, "set_option Elab.async false in")
        L.insert(j, "set_option maxHeartbeats 0 in")
        L.insert(j, "-- A long kernel evaluation, checked synchronously (one at a time) without a heartbeat limit.")
    text = "\n".join(L)
    print("synchronous kernel checks:", len(starts))
io.open(OUT, "w", encoding="utf-8", newline="\n").write(text)
print("parts:", len(mods), "| dropped:", " ".join(d.split(".")[1] for d in dropped))
print("decls tagged:", counts["decl"], "merged:", counts["merged"], "sorried(fast):", counts["sorried"])
print("lines:", text.count("\n") + 1, "bytes:", len(text.encode("utf-8")), "->", OUT)
